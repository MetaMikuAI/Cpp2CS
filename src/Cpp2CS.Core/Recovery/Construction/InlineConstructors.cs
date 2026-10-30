using Cpp2CS.Idioms;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>以真实构造函数的直线调用、字段写入为模板，认回分配之后展开的构造。</summary>
internal static class InlineConstructors
{
    internal sealed record Pattern(MethodRef Method, AbiSignature Signature, IReadOnlyList<Stmt> Effects)
    {
        public bool ReorderStores { get; init; }
    }
    internal sealed record Match(MethodRef Method, IReadOnlyList<Expr> Arguments, IReadOnlyList<Stmt> Statements);

    internal static Pattern? Create(MethodRef method, AbiSignature signature, MachineFunction function)
    {
        if (function.Range.ExceptionRegions.Any() || signature.This is not { Passing: Passing.Registers, Pieces.Length: 1 }
            || signature.Parameters.Any(p => p.Passing != Passing.Registers || p.Pieces.Length != 1
                || !(p.Pieces[0].Register.Bank == Bank.Gpr
                    || p.Pieces[0] is { Register.Bank: Bank.Vec, Width: 32 or 64 }))) return null;
        var effects = new List<Stmt>();
        var definitions = new Dictionary<Variable, Expr>();
        foreach (var (_, statement) in AllocationPairing.Following(function.EntryBlock, -1))
        {
            switch (statement)
            {
                case Nop: continue;
                case Define d when Pure(Expand(d.Value, definitions)): definitions[d.Target] = Expand(d.Value, definitions); continue;
                // 提升器保留的序言存寄存器不属于构造行为。
                case Store { Target: FrameAddress, Value: Use { Width: 64, Variable: { Version: 0 } v } }
                    when v.Storage.Bank == Bank.Gpr && v.Storage.Index is >= 19 and <= 30
                        || v.Storage.Bank == Bank.Vec && v.Storage.Index is >= 8 and <= 15:
                    continue;
                case Return { Value: null }:
                case Call { Kind: CallKind.Tail, Op.Kind: OpKind.WriteBarrier }:
                    // 尾部写屏障只通知 GC；调用点保留自身屏障及其返回语义。
                    return effects.Count > 1 && effects.Any(s => s is Store)
                        && effects.Any(s => s is Call { Op: null, Kind: CallKind.Direct }) ? new(method, signature, effects) : null;
                case Call { Kind: CallKind.Direct } call when call.Op is null or { Kind: OpKind.WriteBarrier }:
                    effects.Add(ExprMap.MapOperands(call, e => Expand(e, definitions)));
                    break;
                case Call { Kind: CallKind.Tail, Op: null } tail:
                    // 内联后尾调用成为普通调用；它的实参和副作用仍须完整匹配，不能作为屏障删去。
                    effects.Add(ExprMap.MapOperands(tail with { Kind = CallKind.Direct }, e => Expand(e, definitions)));
                    return effects.Any(s => s is Store) ? new(method, signature, effects) : null;
                case Store store:
                    var expanded = (Store)ExprMap.MapOperands(store, e => Expand(e, definitions));
                    if (expanded.Target is not Binary { Op: BinOp.Add, Left: Use { Variable.Version: 0 } self, Right: Const }
                        || self.Variable.Storage != signature.This.Pieces[0].Register) return null;
                    effects.Add(expanded);
                    break;
                default: return null;
            }
            if (effects.Count > 64) return null;
        }
        return null;
    }

    internal static Match? Find(Pattern pattern, MachineFunction function, Block block, int index, Variable created)
    {
        var allocation = block.Statements[index];
        var bindings = new Dictionary<Variable, Expr>
        {
            [new(pattern.Signature.This!.Pieces[0].Register, 0)] = new Use(created, 64)
        };
        var parameters = pattern.Signature.Parameters.Select(p => p.Pieces[0]).ToArray();
        var widths = parameters.ToDictionary(p => new Variable(p.Register, 0), p => p.Width);
        var definitions = new Dictionary<Variable, Expr>();
        var matched = new List<Stmt>();
        var stores = new List<Store>();
        var effect = 0;
        foreach (var (current, statement) in AllocationPairing.Following(block, index))
        {
            // newobj 留在原分配点；会抛出的调用须有相同异常去向。
            // 模板只写新对象的直接字段，写入本身不引入托管异常。
            if (statement is Call && !SameRegion(function, block, allocation, current, statement)) return null;
            matched.Add(statement);
            if (statement is Nop) continue;
            if (statement is Define d && Pure(Expand(d.Value, definitions))) { definitions[d.Target] = Expand(d.Value, definitions); continue; }
            var actual = ExprMap.MapOperands(statement, e => Expand(e, definitions));
            var expected = pattern.Effects[effect];
            var consumed = 1;
            if ((pattern.ReorderStores || !pattern.Effects.Take(effect).Any(s => s is Call)) && actual is Store write && expected is Store)
            {
                if (stores.Count == 0)
                {
                    stores.AddRange(pattern.Effects.Skip(effect).TakeWhile(s => s is Store).Cast<Store>());
                    if (!DisjointStores(stores)) return null;
                }
                consumed = MatchStores(write, stores, bindings, widths);
                if (consumed == 0) return null;
            }
            else if (stores.Count != 0 || !Statement(expected, actual, bindings, widths)) return null;
            effect += consumed;
            if (effect == pattern.Effects.Count) break;
        }
        if (effect != pattern.Effects.Count) return null;
        var args = new List<Expr>();
        foreach (var parameter in parameters)
        {
            if (!bindings.TryGetValue(new(parameter.Register, 0), out var value) || !Pure(value)) return null;
            args.Add(Low(value, parameter.Width));
        }
        var removed = matched.ToHashSet(ReferenceEqualityComparer.Instance);
        var locals = matched.SelectMany(Defines).ToHashSet();
        // 参数不能来自构造内部；内部调用结果也不能被构造之后的代码继续读取。
        if (args.SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == created || locals.Contains(u.Variable))) return null;
        foreach (var statement in function.Blocks.SelectMany(b => b.Statements).Where(s => !removed.Contains(s)))
            if (statement is Phi phi && phi.Sources.Any(locals.Contains)
                || ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => locals.Contains(u.Variable))) return null;
        return new(pattern.Method, args, matched);
    }

    // 宽写入必须恰好覆盖连续字段；不允许跨过间隙、调用或尚未匹配的其他副作用。
    private static int MatchStores(Store actual, List<Store> pending, Dictionary<Variable, Expr> bindings,
        Dictionary<Variable, int> parameters)
    {
        if (actual.Target is not Binary { Op: BinOp.Add, Left: var root, Right: Const offset }
            || actual.Value.Width % 8 != 0) return 0;
        var end = offset.Signed + actual.Value.Width / 8;
        var selected = pending.Where(s => ((Const)((Binary)s.Target).Right).Signed >= offset.Signed
            && ((Const)((Binary)s.Target).Right).Signed < end)
            .OrderBy(s => ((Const)((Binary)s.Target).Right).Signed).ToArray();
        var cursor = offset.Signed;
        foreach (var store in selected)
        {
            var target = (Binary)store.Target;
            if (((Const)target.Right).Signed != cursor || store.Value.Width % 8 != 0
                || cursor + store.Value.Width / 8 > end
                || !Expression(target.Left, root, bindings, parameters)
                || !Expression(store.Value, Fold.Extract(actual.Value, (int)(cursor - offset.Signed) * 8,
                    store.Value.Width), bindings, parameters)) return 0;
            cursor += store.Value.Width / 8;
        }
        if (cursor != end) return 0;
        foreach (var store in selected) pending.Remove(store);
        return selected.Length;
    }

    // 新对象尚未发布时，连续且互不重叠的纯字段写入允许交换；调用和屏障仍保持顺序。
    private static bool DisjointStores(IReadOnlyList<Store> stores)
    {
        if (stores.Any(s => !Pure(s.Value) || s.Target is not Binary
            { Op: BinOp.Add, Left: Use, Right: Const })) return false;
        var spans = stores.Select(s => (Root: ((Binary)s.Target).Left, Offset: ((Const)((Binary)s.Target).Right).Signed,
            Size: s.Value.Width / 8)).OrderBy(s => s.Offset).ToArray();
        return spans.All(s => s.Root == spans[0].Root && s.Offset >= 16 && s.Size > 0)
            && spans.Zip(spans.Skip(1)).All(p => p.First.Offset + p.First.Size <= p.Second.Offset);
    }

    private static IEnumerable<Variable> Defines(Stmt statement) => statement switch
    {
        Define d => [d.Target],
        Call c => c.Defines.OfType<Variable>(),
        _ => []
    };

    private static bool SameRegion(MachineFunction function, Block source, Stmt start, Block destination, Stmt end)
    {
        var first = function.Range.ExceptionRegions.FirstOrDefault(r => r.Start <= start.Address && start.Address < r.End);
        var last = function.Range.ExceptionRegions.FirstOrDefault(r => r.Start <= end.Address && end.Address < r.End);
        return source.Handler == destination.Handler && (first?.LandingPad ?? 0) == (last?.LandingPad ?? 0)
            && (first?.ActionOffset ?? 0) == (last?.ActionOffset ?? 0);
    }

    private static bool Statement(Stmt pattern, Stmt actual, Dictionary<Variable, Expr> bindings, Dictionary<Variable, int> parameters)
    {
        if (pattern is Store p && actual is Store a)
            return Expression(p.Target, a.Target, bindings, parameters) && Expression(p.Value, a.Value, bindings, parameters);
        if (pattern is not Call pc || actual is not Call ac || pc.Kind != ac.Kind || pc.Op != ac.Op
            || !pc.Sources.SequenceEqual(ac.Sources) || pc.Arguments.Length != ac.Arguments.Length
            || !pc.Results.SequenceEqual(ac.Results) || !Expression(pc.Target, ac.Target, bindings, parameters)) return false;
        for (var i = 0; i < pc.Arguments.Length; i++)
            if (!Expression(pc.Arguments[i], ac.Arguments[i], bindings, parameters)) return false;
        for (var i = 0; i < pc.Defines.Length; i++)
            if (pc.Defines[i] is { } result)
            {
                if (i >= ac.Defines.Length || ac.Defines[i] is not { } target) return false;
                bindings[result] = new Use(target, target.Width);
            }
        return true;
    }

    private static bool Expression(Expr pattern, Expr actual, Dictionary<Variable, Expr> bindings, Dictionary<Variable, int> parameters)
    {
        // 布尔参数在原生构造中常先取低一位；调用点传常量时该运算已经折叠。
        var boolean = pattern;
        while (boolean is Ir.Convert { Kind: ConvKind.Truncate or ConvKind.ZeroExtend } conversion) boolean = conversion.Operand;
        if (boolean is Binary { Op: BinOp.And, Left: Use flag, Right: Const { Value: 1 } }
            && actual is Const { Value: <= 1 } constant && parameters.TryGetValue(flag.Variable, out var parameterWidth))
        {
            var bound = bindings.GetValueOrDefault(flag.Variable) ?? Expr.C(constant.Value, parameterWidth);
            var substituted = Fold.Simplify(ExprMap.Map(pattern, e => e is Use u && u.Variable == flag.Variable ? Low(bound, u.Width) : null));
            if (substituted != actual) return false;
            bindings[flag.Variable] = bound;
            return true;
        }
        if (pattern is Use use)
        {
            if (bindings.TryGetValue(use.Variable, out var bound)) return Low(bound, use.Width) == actual;
            if (!parameters.TryGetValue(use.Variable, out var width) || use.Width != width || actual.Width != width) return false;
            bindings[use.Variable] = actual;
            return true;
        }
        if (pattern.Width != actual.Width) return false;
        if (pattern == actual) return true;
        return (pattern, actual) switch
        {
            (Binary p, Binary a) => p.Op == a.Op && Expression(p.Left, a.Left, bindings, parameters) && Expression(p.Right, a.Right, bindings, parameters),
            (Unary p, Unary a) => p.Op == a.Op && Expression(p.Operand, a.Operand, bindings, parameters),
            (Ir.Convert p, Ir.Convert a) => p.Kind == a.Kind && Expression(p.Operand, a.Operand, bindings, parameters),
            (Extract p, Extract a) => p.Low == a.Low && Expression(p.Operand, a.Operand, bindings, parameters),
            (Insert p, Insert a) => p.Low == a.Low && Expression(p.Base, a.Base, bindings, parameters) && Expression(p.Value, a.Value, bindings, parameters),
            (Load p, Load a) => Expression(p.Address, a.Address, bindings, parameters),
            (Const or Symbol, _) => pattern == actual,
            _ => false
        };
    }

    private static bool Pure(Expr expression) => ExprMap.Walk(expression).All(e => e is Const or Use or Binary or Unary or Ir.Convert or Symbol or Extract or Insert);
    private static Expr Low(Expr value, int width) => value is Use u ? u with { Width = width }
        : Fold.Convert(value.Width < width ? ConvKind.ZeroExtend : ConvKind.Truncate, value, width);
    private static Expr Expand(Expr expression, IReadOnlyDictionary<Variable, Expr> definitions)
    {
        var expanded = ExprMap.Map(expression, e => e is Use u && definitions.TryGetValue(u.Variable, out var value) ? Low(value, u.Width) : null);
        return Fold.Simplify(ExprMap.Map(expanded, e => e is Intrinsic duplicate
            ? ScalarVectorNarrowing.RepeatedConstant(duplicate) ?? ScalarVectorNarrowing.RepeatedVariable(duplicate) : null));
    }
}

public sealed partial class MethodRecovery
{
    internal readonly Dictionary<MethodRef, InlineConstructors.Pattern?> constructorPatterns = new();
    internal InlineConstructors.Pattern? ConstructorPattern(MethodRef method)
    {
        if (constructorPatterns.TryGetValue(method, out var cached)) return cached;
        InlineConstructors.Pattern? pattern = null;
        var entry = NativeMethods.ConstructorEntry(method);
        if (entry != 0 && facts.Code.RegionOf(entry) == CodeRegion.Managed
            && abi.Classify(method, out _) is { } signature && lifter.Lift(entry) is { Succeeded: true } lifted)
        {
            var normalized = rewriter.Run(lifted.Function);
            if (normalized.Errors.Count == 0 && normalized.Residuals.Count == 0)
            {
                pattern = InlineConstructors.Create(method, signature, lifted.Function);
                if (pattern is { Effects: [Call { Target: Const target }, ..] }
                    && pattern.Effects.Skip(1).All(s => s is Store or Call { Op.Kind: OpKind.WriteBarrier })
                    && facts.EntriesAt(target.Value).Any(e => e.Method is
                    {
                        Method:
                        { Name: ".ctor", IsStatic: false, Parameters.Count: 0, Owner.FullName: "System.Object" }
                    }))
                    pattern = pattern with { ReorderStores = true };
            }
        }
        return constructorPatterns[method] = pattern;
    }
}
