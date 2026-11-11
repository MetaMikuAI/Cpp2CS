using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Naming;

public abstract record MetadataEntity;
public sealed record ClassEntity(TypeRef Type) : MetadataEntity;
public sealed record TypeEntity(TypeRef Type) : MetadataEntity;
public sealed record MethodEntity(MethodRef Method) : MetadataEntity;
public sealed record FieldEntity(FieldRef Field) : MetadataEntity;
public sealed record StringEntity(string Value) : MetadataEntity;
public interface IMetadataSlotDecoder { Outcome<MetadataEntity> Decode(ulong imageOffset); }
public sealed record FlagEvidence(bool IsFlag, ImmutableArray<Reason> Reasons, int Reads, int Writes);
public sealed record NamingFacts(ImmutableDictionary<ulong, Outcome<MetadataEntity>> Slots,
    ImmutableDictionary<ulong, FlagEvidence> Flags, bool Complete)
{
    public static NamingFacts Empty { get; } = new(ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty,
        ImmutableDictionary<ulong, FlagEvidence>.Empty, false);
}
public sealed class InitializationFlagQuery(NamingFacts facts) : Query<ulong, FlagEvidence>
{
    public override Outcome<FlagEvidence> Compute(QueryContext c, ulong key) => Outcome<FlagEvidence>.Success(
        facts.Flags.GetValueOrDefault(key) ?? new(false, [new("naming.no-access-evidence", "没有全映像访问凭据。")], 0, 0));
}

/// <summary>一次运行的流式普查器；Finish 后只发布不可变事实。缺失函数必须调用 Incomplete，不以部分普查证明全称命题。</summary>
/// <remarks>给出映像时，映像里不变数据的读取（例如经 GOT 取槽位地址）按文件内容解析。</remarks>
public sealed class NamingSurvey(CallNamingQuery calls, IMetadataSlotDecoder decoder, Cpp2CS.Native.Images.IImage? image = null)
{
    private readonly HashSet<ulong> slots = [];
    private readonly Dictionary<ulong, List<Reason>> reasons = [];
    private readonly Dictionary<ulong, (int Reads, int Writes)> counts = [];
    private readonly HashSet<ulong> escaped = [];
    private readonly HashSet<ulong> byteCandidates = [];
    private readonly StateQueries state = new(image: image);
    private readonly FlowQueries flow = new();
    private bool complete = true;
    private readonly HashSet<(ulong Address, int Width)> accesses = [];
    public void Incomplete() => complete = false;
    public void Observe(NativeFunction function)
    {
        var c = state.CreateContext(function);
        var initializers = new List<Point>();
        foreach (var block in function.Blocks)
        for (int i = 0; i < block.Statements.Length; i++)
            if (block.Statements[i] is Call call)
            {
                var classified = c.Get(calls, call.Identity);
                if (classified.IsSuccess && classified.Value.Operation?.Name == "InitializeMetadata")
                {
                    initializers.Add(new(block.Identity, i));
                    if (classified.Value.Inputs?.GetValueOrDefault("slot")?.Source is TermSource source && Address(c, source.Term, 8) is { } address) slots.Add(address);
                }
            }
        // 读取结果的直接使用沿纯项与合流传播；任何非分支根使用均否定凭据。
        var badReads = new HashSet<ReadIdentity>();
        var testedReads = new HashSet<ReadIdentity>();
        void Use(Term value, bool addressUse = false, bool condition = false)
        {
            var pending = new Stack<Term>(); var seen = new HashSet<Term>(); pending.Push(value);
            while (pending.TryPop(out var t))
            {
                if (!seen.Add(t)) continue;
                if (t.Identity is ResultAtom { Definition: ReadIdentity id }) (condition ? testedReads : badReads).Add(id);
                foreach (var child in t.Operands) pending.Push(child);
                if (t.Identity is ResultAtom { Definition: MergeIdentity merge })
                    foreach (var input in function.Blocks.SelectMany(b => b.Merges).Single(m => m.Identity == merge).Inputs) pending.Push(input.Value);
                if (!addressUse && t.Width == function.AddressWidth && Address(c, t, 8) is { } address) escaped.Add(address);
            }
        }
        foreach (var b in function.Blocks)
        {
            foreach (var s in b.Statements)
                switch (s)
                {
                    case MemoryRead r: Use(r.Address, true); break;
                    case MemoryWrite w: Use(w.Address, true); Use(w.Value); break;
                    case Call call:
                        foreach (var arg in call.Arguments) Use(arg.Value);
                        if (call.Target is ComputedTarget target) Use(target.Value);
                        if (call.OutgoingArgumentArea is { } area) Use(area);
                        break;
                    case TrapWhen t: Use(t.Condition); break;
                    case DynamicAllocation d: Use(d.Size); break;
                }
            switch (b.End)
            {
                case Branch branch: Use(branch.Condition, condition: true); break;
                case JumpTable table: Use(table.Selector, condition: true); break;
                case Return r: foreach (var v in r.Results) Use(v.Value); break;
                case ResumeUnwind u: Use(u.Exception); break;
            }
        }
        foreach (var b in function.Blocks)
        for (int i = 0; i < b.Statements.Length; i++)
        {
            var s = b.Statements[i];
            var address = s switch { MemoryRead r => Address(c, r.Address, r.Width), MemoryWrite w => Address(c, w.Address, w.Width), _ => null };
            if (address is not { } a) continue;
            var width = s is MemoryRead ar ? ar.Width : ((MemoryWrite)s).Width;
            accesses.Add((a, width));
            if (width == 8) byteCandidates.Add(a);
            if (!reasons.ContainsKey(a)) reasons[a] = [];
            var count = counts.GetValueOrDefault(a);
            if (s is MemoryRead read)
            {
                counts[a] = (count.Reads + 1, count.Writes);
                if (read.Width != 8 || badReads.Contains(read.Identity) || !testedReads.Contains(read.Identity)) reasons[a].Add(new("naming.flag-read", "读取不是字节或其值有非分支使用。"));
            }
            else if (s is MemoryWrite write)
            {
                counts[a] = (count.Reads, count.Writes + 1);
                var value = c.Get(state.Resolve, write.Value);
                if (write.Width != 8 || !value.IsSuccess || value.Value.ConstantValue != 1)
                    reasons[a].Add(new("naming.flag-write", "写入不是字节常量 1。"));
                if (!initializers.Any(p => c.Get(flow.PointDominates, new(p, new(b.Identity, i))) is { IsSuccess: true, Value: true }))
                    reasons[a].Add(new("naming.flag-order", "写入没有被元数据初始化调用支配。"));
            }
        }

    }
    private ulong? Address(QueryContext c, Term term, int width)
    {
        var value = c.Get(state.Resolve, term); if (!value.IsSuccess) { complete = false; return null; }
        var location = c.Get(state.Locations, new(value.Value, width));
        if (!location.IsSuccess || location.Value is { Region: Region.Image, Offset: null }) complete = false;
        return location.IsSuccess && location.Value is { Region: Region.Image, Offset: { } offset } && offset >= 0 && offset <= ulong.MaxValue ? (ulong)offset : null;
    }
    public NamingFacts Finish()
    {
        var decoded = slots.ToImmutableDictionary(a => a, decoder.Decode);
        var evaluated = reasons.ToDictionary(p => p.Key, p => p.Value.ToList());
        var flags = ImmutableDictionary.CreateBuilder<ulong, FlagEvidence>();
        // 以区间索引找可能重叠者，实际重叠仍由内核的唯一别名查询判定。
        var candidates = new SortedSet<ulong>(byteCandidates);
        var table = new TermTable(); var root = table.Atom(new RootAtom(AddressRoot.Image), 64);
        var block = new BlockIdentity(); var builder = new FunctionBuilder(table, block, 64, new(table.Atom(new RootAtom(AddressRoot.Frame), 64)));
        builder.Blocks.Add(new(block, [], [], new Return([])));
        var context = state.CreateContext(builder.Freeze());
        foreach (var access in accesses.Where(x => x.Width > 8))
        {
            var bytes = (ulong)((access.Width + 7) / 8);
            var end = access.Address > ulong.MaxValue - bytes + 1 ? ulong.MaxValue : access.Address + bytes - 1;
            foreach (var candidate in candidates.GetViewBetween(access.Address, end))
            {
                var alias = context.Get(state.Alias, new(new(Region.Image, root, candidate, 8), new(Region.Image, root, access.Address, access.Width)));
                if (!alias.IsSuccess || alias.Value.Kind != AliasKind.Disjoint)
                    evaluated[candidate].Add(new("naming.flag-overlap", "存在覆盖该字节的宽访问。"));
            }
        }
        foreach (var (address, list) in evaluated.Where(p => byteCandidates.Contains(p.Key) && !slots.Contains(p.Key)))
        {
            var why = list.ToList(); var count = counts[address];
            if (!complete) why.Add(new("naming.incomplete-survey", "映像普查不完整，不能证明全部访问。"));
            if (escaped.Contains(address)) why.Add(new("naming.flag-escape", "地址另有非内存访问用途。"));
            if (count.Reads == 0 || count.Writes == 0) why.Add(new("naming.flag-access", "缺少读取或写入凭据。"));
            flags[address] = new(why.Count == 0, why.Distinct().ToImmutableArray(), count.Reads, count.Writes);
        }
        return new(decoded, flags.ToImmutable(), complete);
    }
}
