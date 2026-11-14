using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    private sealed record SlotContents(Term Address, Term Representative, ImmutableHashSet<MetadataEntity> Entities,
        ImmutableArray<SlotContents> Inputs, BlockIdentity? Block = null, Merge? Merge = null);

    // 查询只验证地址的值图；全部输入成功后才由快照改写创建定义。
    private sealed class SlotContentsQuery(StateQueries state, ValueNamingQuery names,
        IReadOnlyDictionary<Term, (BlockIdentity Block, Merge Merge)> merges) : Query<Term, SlotContents>
    {
        public override Outcome<SlotContents> Compute(QueryContext c, Term address)
        {
            var active = new HashSet<Term>();
            var known = new Dictionary<Term, Outcome<SlotContents>>();
            Outcome<SlotContents> No(string code, string message, Reason? cause = null) =>
                Outcome<SlotContents>.Failure(new("structure.merged-slot." + code, message, cause));
            Outcome<SlotContents> Read(Term key)
            {
                if (c.Step() is { } budget) return No("budget", "槽内容证明预算耗尽。", budget);
                if (known.TryGetValue(key, out var previous)) return previous;
                var resolved = c.Get(state.Resolve, key);
                if (!resolved.IsSuccess) return No("address", "槽位地址无法解析。", resolved.Why);
                if (!active.Add(resolved.Value)) return No("cycle", "槽位地址的值图含循环，不能逐输入证明。");
                var value = Node(resolved.Value, key);
                active.Remove(resolved.Value); known[key] = value;
                return value;
            }
            Outcome<SlotContents> Node(Term key, Term original)
            {
                if (key.Width != c.Snapshot.AddressWidth || key.ContainsUndefined)
                    return No("address", "输入不是有定义的完整指针宽地址。");
                bool select = key.Operator is CoreOperator { Operation: CoreOperation.Select };
                // 解析用于证明槽位；选择仍引用原快照中的条件定义，不把内存状态原子写回快照。
                var source = select && original.Operator is CoreOperator { Operation: CoreOperation.Select } ? original : key;
                if (select && SnapshotRewrite.Dependencies([source.Operands[0]]).Any(t => t.Kind == TermKind.Atom
                    && t.Identity is not (EntryAtom or ResultAtom or RootAtom or CallerValue or ExceptionAtom or SelectorAtom)))
                    return No("condition", "选择条件没有可保留的原生定义身份。");
                var merged = merges.GetValueOrDefault(key);
                if (select || merged.Merge is not null)
                {
                    var inputs = select ? source.Operands.Skip(1).ToArray() : merged.Merge!.Inputs.Select(i => i.Value).ToArray();
                    if (inputs.Length == 0) return No("input", "地址合流没有输入。");
                    var values = ImmutableArray.CreateBuilder<SlotContents>();
                    for (int i = 0; i < inputs.Length; i++)
                    {
                        var input = Read(inputs[i]);
                        if (!input.IsSuccess) return No("input", select ? (i == 0 ? "选择的真支" : "选择的假支") + "不是已证明的元数据槽位地址。"
                            : $"合流第 {i} 个输入不是已证明的元数据槽位地址。", input.Why);
                        values.Add(input.Value);
                    }
                    return Outcome<SlotContents>.Success(new(select ? source : key, values[0].Representative,
                        values.SelectMany(v => v.Entities).ToImmutableHashSet(), values.ToImmutable(), merged.Block, merged.Merge));
                }
                var location = c.Get(state.Locations, new(key, key.Width));
                if (!location.IsSuccess || location.Value is not { Region: Region.Image, Offset: { } offset }
                    || offset < 0 || offset > ulong.MaxValue)
                    return No("slot", "输入不能定位为映像中的常量槽位。", location.Why);
                var named = c.Get(names, c.Snapshot.Terms.Atom(new MemoryAtom(location.Value, null), key.Width));
                if (!named.IsSuccess || named.Value.Name is not EntityName { Slot: not null } entity)
                    return No("slot", "常量地址没有已解码的元数据实体。", named.IsSuccess ? named.Value.Why : named.Why);
                return Outcome<SlotContents>.Success(new(key, key, [entity.Entity], []));
            }
            return Read(address);
        }
    }

    private sealed class SlotContentsRewrite(QueryContext context, SlotContentsQuery query)
    {
        private readonly Dictionary<Term, Term> values = [];
        private readonly Dictionary<Term, Term> slots = [];
        private readonly List<MemoryRead> reads = [];
        private readonly Dictionary<BlockIdentity, List<Merge>> merges = [];
        internal HashSet<Term> PathEntities { get; } = [];

        internal Outcome<SlotContents> Prove(Term address) => context.Get(query, address);
        internal Term Materialize(SlotContents node)
        {
            if (values.TryGetValue(node.Address, out var known)) return known;
            var terms = context.Snapshot.Terms;
            Term value;
            if (node.Entities.Count == 1)
            {
                // 已解码槽的读取只提供实体凭据；托管写法由命名给出，不产生原生指针常量。
                if (!slots.TryGetValue(node.Representative, out value!))
                {
                    var id = new ReadIdentity(); value = terms.Atom(new ResultAtom(id), context.Snapshot.AddressWidth);
                    reads.Add(new(id, node.Representative, value.Width, value)); slots[node.Representative] = value;
                }
            }
            else if (node.Merge is { } source)
            {
                var id = new MergeIdentity(source.Identity); value = terms.Atom(new ResultAtom(id), source.Result.Width);
                if (!merges.TryGetValue(node.Block!, out var additions)) merges[node.Block!] = additions = [];
                additions.Add(new(id, value, source.Inputs.Select((input, i) => input with { Value = Materialize(node.Inputs[i]) }).ToImmutableArray()));
            }
            else value = terms.Apply(node.Address.Operator!, node.Address.Width, node.Address.Operands[0], Materialize(node.Inputs[0]), Materialize(node.Inputs[1]));
            values[node.Address] = value;
            if (node.Entities.Count > 1 && !node.Entities.All(e => e is StringEntity)) PathEntities.Add(value);
            return value;
        }
        internal void Publish(SnapshotRewrite edit)
        {
            if (reads.Count != 0)
            {
                var entry = edit.Blocks[context.Snapshot.Entry];
                edit.Blocks[entry.Identity] = entry with { Statements = [.. reads, .. entry.Statements] };
            }
            foreach (var (id, additions) in merges)
                edit.Blocks[id] = edit.Blocks[id] with { Merges = edit.Blocks[id].Merges.AddRange(additions) };
        }
    }

    private static StableIdentity SlotUseIdentity(Statement? statement, BlockIdentity block) => statement switch
    {
        Call call => call.Identity, MemoryRead read => read.Identity, MemoryWrite write => write.Identity, _ => block,
    };

    private void RecordPathEntities(NativeFunction function, IReadOnlySet<Term> entities, List<StructureRecord> records)
    {
        if (entities.Count == 0) return;
        var c = names.CreateContext(function);
        var uses = new SemanticUses(c, calls, state, names.Binder, names.Entry);
        bool Depends(Term value)
        {
            bool found = false;
            uses.Visit(value, (term, _, _) => found |= entities.Contains(term));
            return found;
        }
        foreach (var use in uses.Roots.Where(u => Depends(u.Value)))
        {
            var block = function.Blocks.Single(b => b.Identity == use.Point.Block);
            var statement = use.Point.Before < block.Statements.Length ? block.Statements[use.Point.Before] : null;
            void Reject(string code)
            {
                var why = new Reason("structure.merged-slot.use." + code, "元数据实体随路径而定；该使用需要单一托管实体，尚未做路径拆分。");
                var record = new StructureRecord("merged-slot-use", statement?.Trace?.NativeAddress ?? block.Trace?.NativeAddress, why.Message, false) { Why = why, Use = SlotUseIdentity(statement, block.Identity) };
                if (!records.Contains(record)) records.Add(record);
            }
            if (statement is Call call && c.Get(calls, call.Identity) is { IsSuccess: true } classified)
            {
                var inputs = classified.Value.Inputs?.Where(p => p.Value.Source is TermSource source && Depends(source.Term)).Select(p => p.Key).ToArray() ?? [];
                if (inputs.Length != 0) foreach (var input in inputs) Reject(classified.Value.Operation!.Name + "." + input);
                else Reject(classified.Value.Operation?.Name ?? "managed-call");
            }
            else Reject(statement is MemoryWrite ? "store" : statement is MemoryRead ? "read" : statement is null ? "terminator" : "statement");
        }
    }
}
