using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Idioms;

/// <summary>按同根的 invoke_impl/method_code/method 和具体 Invoke ABI 收窄保守间接调用。</summary>
internal sealed class DelegateCallNormalizer
{
    private readonly ProgramFacts facts;
    private readonly ManagedAbi abi;
    private readonly Dictionary<Variable, Expr> definitions;
    private readonly Dictionary<Variable, Phi> phis;
    private readonly Dictionary<Variable, Call> results;
    private readonly Dictionary<Variable, Block> owners;
    private readonly Dictionary<Storage, TypeRef> inputs = [];
    private readonly Dictionary<Variable, TypeRef> known = [];
    private readonly Dictionary<long, TypeRef> frameTypes = [];

    private DelegateCallNormalizer(ProgramFacts facts, MachineFunction function)
    {
        this.facts = facts;
        abi = new(facts.Layouts);
        var all = function.Blocks.SelectMany(b => b.Statements).ToArray();
        definitions = all.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        foreach (var (_, dead) in function.Dead) definitions.TryAdd(dead.Target, dead.Value);
        phis = all.OfType<Phi>().ToDictionary(p => p.Target);
        owners = function.Blocks.SelectMany(b => b.Statements.OfType<Define>().Select(d => (d.Target, Block: b)))
            .ToDictionary(p => p.Target, p => p.Block);
        results = all.OfType<Call>().SelectMany(c => c.Defines.Where(v => v is not null).Select(v => (v, c))).ToDictionary(x => x.v, x => x.c);
        // 共享入口不能选第一个托管实例猜输入类型；只有所有注册签名一致的寄存器才提供类型证据。
        var signatures = facts.EntriesAt(function.Entry).Select(e => e.Method).OfType<MethodRef>().Distinct()
            .Select(m => abi.Classify(m, out _)).ToArray();
        if (signatures.Length > 0 && signatures.All(s => s is not null))
            foreach (var value in signatures[0]!.Arguments.Where(v => v.Passing == Passing.Registers && v.Pieces.Length == 1))
            {
                var register = value.Pieces[0].Register;
                if (signatures.All(s => s!.Arguments.Any(v => v.Passing == Passing.Registers && v.Pieces.Length == 1
                    && v.Pieces[0].Register == register && Equals(v.Type, value.Type)))) inputs[register] = value.Type;
            }
        var addressed = new List<(long Offset, TypeRef Type)>();
        foreach (var call in all.OfType<Call>())
        {
            if (call.Op is not null || call.Target is not Const target) continue;
            var methods = facts.EntriesAt(target.Value).Select(e => e.Method).OfType<MethodRef>().Distinct().ToArray();
            var exact = call.Arguments.Select(ExpandOne).OfType<Symbol>().Where(s => s.Kind == SymbolKind.Method).Select(s => (MethodRef)s.Value)
                .Where(m => methods.Any(c => c.Method == m.Method)).Distinct().ToArray();
            var callee = exact.Length == 1 ? exact[0] : methods.Length == 1 ? methods[0] : null;
            if (callee is null || abi.Classify(callee, out _) is not { } signature) continue;
            foreach (var parameter in signature.Arguments)
            {
                if (parameter is not { Type: ByRefRef byRef, Passing: Passing.Registers, Pieces: [var piece] }) continue;
                var index = Array.IndexOf(call.Sources, piece.Register);
                if (index >= 0 && Top(call.Arguments[index]) is FrameAddress frame) addressed.Add((frame.Offset, byRef.Element));
            }
        }
        foreach (var group in addressed.GroupBy(p => p.Offset))
            if (group.Select(p => p.Type).Distinct().ToArray() is [var type]) frameTypes[group.Key] = type;
    }

    public static bool Run(ProgramFacts facts, MachineFunction function, IdiomResult report)
    {
        static bool NeedsProof(Call call) => call.Op?.Kind == OpKind.CallDelegate
            ? call is not { Target: Symbol { Kind: SymbolKind.Method }, DelegateReceiver: not null }
            : call.Op is null && call.Target is Use;
        if (!function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(NeedsProof)) return false;
        var context = new DelegateCallNormalizer(facts, function);
        var invalidResults = new HashSet<Variable>();
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call call || !NeedsProof(call)) continue;
                var normalized = context.Normalize(call, block);
                if (normalized is null)
                {
                    if (call.Op?.Kind == OpKind.CallDelegate)
                    {
                        block.Statements[i] = call with { Op = null };
                        report.Hits[Template.DelegateCall]--;
                    }
                    continue;
                }
                invalidResults.UnionWith(call.Defines.Except(normalized.Defines).Where(v => v is not null));
                if (call.Op is null) report.Hit(Template.DelegateCall);
                block.Statements[i] = normalized;
            }
        // 保守 clobber 里不属于 Invoke 结果的值没有托管含义。真实使用保留 Unknown 留洞，不能猜成原寄存器值。
        if (invalidResults.Count > 0)
        {
            bool changed;
            do
            {
                changed = false;
                foreach (var phi in function.Blocks.SelectMany(b => b.Statements).OfType<Phi>())
                    if (phi.Sources.Any(invalidResults.Contains)) changed |= invalidResults.Add(phi.Target);
            } while (changed);
            foreach (var block in function.Blocks)
            {
                block.Statements.RemoveAll(s => s is Phi p && invalidResults.Contains(p.Target));
                for (var i = 0; i < block.Statements.Count; i++)
                    block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e,
                        v => v is Use u && invalidResults.Contains(u.Variable) ? new Unknown("非Invoke返回寄存器", u.Width) : null));
            }
        }
        return true;
    }

    private Expr Top(Expr e, int depth = 16) => depth > 0 && e is Use u && definitions.TryGetValue(u.Variable, out var value) ? Top(value, depth - 1) : e;
    private Expr Expand(Expr e, int depth = 12) => depth <= 0 ? e : ExprMap.Map(e,
        v => v is Use u && definitions.TryGetValue(u.Variable, out var value) ? Expand(value, depth - 1) : null);

    private (Expr? Root, long Offset) Split(Expr address)
    {
        var rest = new List<Expr>();
        long offset = 0;
        void Add(Expr e)
        {
            switch (Top(e))
            {
                case Binary { Op: BinOp.Add } b: Add(b.Left); Add(b.Right); break;
                case Const c: offset += unchecked((long)c.Value); break;
                default: rest.Add(e); break;
            }
        }
        Add(address);
        return (rest.Count == 1 ? rest[0] : null, offset);
    }

    // 两个分支分别读取同一委托字段，汇合后调用；中间不能有写入或其他调用。
    private Expr JoinedField(Expr expression, Block destination, Call call)
    {
        var value = Top(expression);
        if (value is not Use use || !phis.TryGetValue(use.Variable, out var phi)) return value;
        var loads = new List<Load>();
        foreach (var source in phi.Sources)
        {
            if (Top(new Use(source, source.Width)) is not Load { Width: 64 } load || !owners.TryGetValue(source, out var origin)) return value;
            var index = origin.Statements.FindIndex(s => s is Define d && d.Target == source);
            var current = origin;
            var visited = new HashSet<Block>();
            var reached = false;
            while (visited.Add(current))
            {
                foreach (var statement in current.Statements.Skip(index + 1))
                {
                    if (ReferenceEquals(statement, call)) { reached = true; break; }
                    if (statement is not (Define or Phi or Nop or Jump)) return value;
                }
                if (reached) break;
                if (current.NormalSuccessors.ToArray() is not [var next] || next.IsLandingPad) return value;
                current = next;
                index = -1;
            }
            if (!reached || current != destination) return value;
            loads.Add(load);
        }
        if (loads.Count == 0) return value;
        if (loads.All(l => Equals(l, loads[0]))) return loads[0];
        var fields = loads.Select(l => Split(l.Address)).ToArray();
        if (fields.Any(f => f.Root is not Use || f.Offset != fields[0].Offset)) return value;
        var roots = fields.Select(f => ((Use)f.Root!).Variable).ToArray();
        var receiver = destination.Statements.OfType<Phi>().FirstOrDefault(p => p.Sources.SequenceEqual(roots));
        return receiver is null ? value : new Load(new Binary(BinOp.Add,
            new Use(receiver.Target, 64), Expr.C(unchecked((ulong)fields[0].Offset), 64), 64), 64);
    }

    private Call? Normalize(Call call, Block block)
    {
        if (JoinedField(call.Target, block, call) is not Load { Width: 64 } target || Split(target.Address) is not { Root: { } root, Offset: 0x18 }) return null;
        var registers = call.Sources.Select((r, i) => (r, e: call.Arguments[i])).ToDictionary(x => x.r, x => x.e);
        bool Field(Expr? value, long offset) => value is not null && JoinedField(value, block, call) is Load { Width: 64 } load
            // Load 定义不可展开后比较：同一字段在两次读取之间可能已被写过，只有同一个 SSA 根才是见证。
            && Split(load.Address) is { Root: { } other } split && split.Offset == offset && Equals(root, other);
        if (!Field(registers.GetValueOrDefault(Storage.Gpr(0)), 0x40) || TypeOf(root, []) is not DefinitionRef type
            || DelegateFacts.Invoke(type) is not { } invoke || abi.Classify(invoke, out _) is not { MethodInfo: { } info } signature
            || !Field(registers.GetValueOrDefault(info.Register), 0x28)) return null;
        if (signature.Parameters.Any(a => a.Passing == Passing.Stack)) return null;
        var sources = signature.Parameters.SelectMany(a => a.Pieces).Select(p => p.Register)
            .Concat(signature.Return is { Passing: Passing.Indirect } indirect ? indirect.Pieces.Select(p => p.Register) : []).Distinct().ToArray();
        if (sources.Any(r => !registers.ContainsKey(r))) return null;
        var returns = call.Results.Select((r, i) => (r, i)).Where(x => signature.Results.Contains(x.r)).ToArray();
        return call with
        {
            Op = new RuntimeOp(OpKind.CallDelegate, invoke), DelegateReceiver = root, Target = new Symbol(SymbolKind.Method, invoke),
            Sources = sources, Arguments = sources.Select(r => registers[r]).ToArray(),
            Results = returns.Select(x => x.r).ToArray(), Defines = returns.Select(x => call.Defines[x.i]).ToArray(),
        };
    }

    private TypeRef? TypeOf(Expr expression, HashSet<Variable> active)
    {
        if (expression is Use u)
        {
            if (known.TryGetValue(u.Variable, out var cached)) return cached;
            if (u.Variable.Version == 0) return inputs.GetValueOrDefault(u.Variable.Storage);
            if (!active.Add(u.Variable)) return null;
            TypeRef? type = null;
            if (definitions.TryGetValue(u.Variable, out var value)) type = TypeOf(value, active);
            else if (phis.TryGetValue(u.Variable, out var phi))
            {
                type = JoinedReferenceType(phi.Sources.Select(v => (Expr)new Use(v, v.Width)), definitions, phis, e => TypeOf(e, new(active)));
                if (type is null)
                {
                    var sources = phi.Sources.Select(v => (Expr)new Use(v, v.Width)).Where(v => Top(v) is not Const { Value: 0 }).ToArray();
                    var types = sources.Select(v => TypeOf(v, active)).ToArray();
                    if (types.Length > 0 && types[0] is not null && types.All(t => Equals(t, types[0]))) type = types[0];
                }
            }
            else if (results.TryGetValue(u.Variable, out var call))
            {
                if (call.Op is { Kind: OpKind.NewObject or OpKind.IsInst, Operand: TypeRef t }) type = t;
                else if (call.Op is null && call.Target is Const target)
                {
                    var methods = facts.EntriesAt(target.Value).Select(e => e.Method).OfType<MethodRef>().Distinct().ToArray();
                    var exact = call.Arguments.Select(ExpandOne).OfType<Symbol>().Where(s => s.Kind == SymbolKind.Method).Select(s => (MethodRef)s.Value)
                        .Where(m => methods.Any(c => c.Method == m.Method)).Distinct().ToArray();
                    var callee = exact.Length == 1 ? exact[0] : methods.Length == 1 ? methods[0] : null;
                    if (callee is not null && abi.Classify(callee, out _)?.Return is { Pieces.Length: 1 } ret && ret.Pieces[0].Register == u.Variable.Storage) type = ret.Type;
                }
            }
            active.Remove(u.Variable);
            if (type is not null) known[u.Variable] = type;
            return type;
        }
        if (expression is Ir.Convert c) return TypeOf(c.Operand, active);
        if (expression is Select select)
            return JoinedReferenceType([select.True, select.False], definitions, phis, e => TypeOf(e, new(active)));
        if (expression is Load { Address: FrameAddress frame } read && frameTypes.TryGetValue(frame.Offset, out var stored)
            && abi.Size(stored) * 8 == read.Width) return stored;
        if (expression is Load { Address: FrameAddress member } memberRead)
        {
            var candidates = frameTypes.Where(p => member.Offset >= p.Key && member.Offset + memberRead.Width / 8 <= p.Key + abi.Size(p.Value))
                .SelectMany(p => p.Value is DefinitionRef type && facts.Layouts.Of(type) is { } layout
                    ? FieldTypes(layout.Fields, member.Offset - p.Key + RuntimeLayout.ObjectHeaderSize, memberRead.Width) : [])
                .Distinct().ToArray();
            if (candidates is [var fieldType]) return fieldType;
        }
        if (expression is not Load load || Split(load.Address) is not { Root: { } root } split) return null;
        var statics = Top(root) as Symbol;
        var owner = statics is { Kind: SymbolKind.StaticFields, Value: DefinitionRef d } ? d : TypeOf(root, active);
        var fieldOffset = split.Offset;
        if (owner is ByRefRef { Element: DefinitionRef { Definition.IsValueType: true } valueType })
        {
            owner = valueType;
            fieldOffset += RuntimeLayout.ObjectHeaderSize;
        }
        for (var current = owner; current is DefinitionRef type; current = type.Definition.BaseType?.Substitute(type.Arguments, []))
        {
            if (facts.Layouts.Of(type) is not { } layout) return null;
            var fields = statics is { Kind: SymbolKind.StaticFields } ? layout.Statics : layout.Fields;
            var matches = FieldTypes(fields, fieldOffset, load.Width).ToArray();
            if (matches.Length > 0) return matches is [var fieldType] ? fieldType : null;
            if (statics is { Kind: SymbolKind.StaticFields }) break;
        }
        return null;
    }

    // phi/条件选择的循环只合并引用来源；null 不提供类型，其他未知来源不能被忽略。
    internal static TypeRef? JoinedReferenceType(IEnumerable<Expr> roots, IReadOnlyDictionary<Variable, Expr> definitions,
        IReadOnlyDictionary<Variable, Phi> phis, Func<Expr, TypeRef?> resolve)
    {
        var pending = new Queue<Expr>(roots);
        var seen = new HashSet<Variable>();
        TypeRef? found = null;
        while (pending.TryDequeue(out var expression))
        {
            if (expression is Const { Value: 0, Width: 64 }) continue;
            if (expression is Use use)
            {
                if (definitions.TryGetValue(use.Variable, out var value) && value is Use or Select or Const { Value: 0, Width: 64 })
                {
                    if (seen.Add(use.Variable)) pending.Enqueue(value);
                    continue;
                }
                if (phis.TryGetValue(use.Variable, out var phi))
                {
                    if (seen.Add(use.Variable)) foreach (var source in phi.Sources) pending.Enqueue(new Use(source, use.Width));
                    continue;
                }
            }
            if (expression is Select select)
            {
                pending.Enqueue(select.True); pending.Enqueue(select.False);
                continue;
            }
            var type = resolve(expression);
            if (type is null || !ManagedTypes.IsReferenceType(type) || found is not null && !found.Equals(type)) return null;
            found = type;
        }
        return found;
    }

    // 内嵌结构体的委托字段与对象字段一样是引用；只接受唯一且宽度完全重合的叶子。
    private IEnumerable<TypeRef> FieldTypes(IEnumerable<FieldSlot> fields, long offset, int width)
    {
        foreach (var field in fields)
        {
            var size = abi.Size(field.Type);
            if (field.Offset > offset || offset + width / 8 > field.Offset + size) continue;
            if (abi.Kind(field.Type) == ValueKind.Struct && field.Type is DefinitionRef value
                && facts.Layouts.Of(value) is { } layout)
            {
                foreach (var leaf in FieldTypes(layout.Fields, offset - field.Offset + RuntimeLayout.ObjectHeaderSize, width))
                    yield return leaf;
            }
            else if (field.Offset == offset && size * 8 == width) yield return field.Type;
        }
    }

    private Expr ExpandOne(Expr expression) => Expand(expression);
}
