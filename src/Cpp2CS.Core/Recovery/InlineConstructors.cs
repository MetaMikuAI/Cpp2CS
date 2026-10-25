using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>以真实构造函数的直线调用、字段写入为模板，认回分配之后展开的构造。</summary>
internal static class InlineConstructors
{
    internal sealed record Pattern(MethodRef Method, AbiSignature Signature, IReadOnlyList<Stmt> Effects);
    internal sealed record Match(MethodRef Method, IReadOnlyList<Expr> Arguments, IReadOnlyList<Stmt> Statements);

    internal static Pattern? Create(MethodRef method, AbiSignature signature, MachineFunction function)
    {
        if (function.Range.ExceptionRegions.Any() || signature.This is not { Passing: Passing.Registers, Pieces.Length: 1 }
            || signature.Parameters.Any(p => p.Passing != Passing.Registers || p.Pieces.Length != 1 || p.Pieces[0].Register.Bank != Bank.Gpr)) return null;
        var effects = new List<Stmt>();
        var definitions = new Dictionary<Variable, Expr>();
        foreach (var (_, statement) in AllocationPairing.Following(function.EntryBlock, -1))
        {
            switch (statement)
            {
                case Nop: continue;
                case Define d when Pure(d.Value): definitions[d.Target] = Expand(d.Value, definitions); continue;
                // 提升器保留的序言存寄存器不属于构造行为。
                case Store { Target: FrameAddress, Value: Use { Variable: { Version: 0 } v } }
                    when v.Storage == Storage.Gpr(30) || v.Storage.Bank == Bank.Gpr && v.Storage.Index is >= 19 and <= 29: continue;
                case Return { Value: null }:
                    return effects.Count > 1 && effects.Any(s => s is Store)
                        && effects[0] is Call { Op: null, Kind: CallKind.Direct } ? new(method, signature, effects) : null;
                case Call { Kind: CallKind.Direct } call when call.Op is null or { Kind: OpKind.WriteBarrier }:
                    effects.Add(ExprMap.MapOperands(call, e => Expand(e, definitions)));
                    break;
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
        var effect = 0;
        foreach (var (current, statement) in AllocationPairing.Following(block, index))
        {
            // newobj 留在原分配点；整个展开区间须有相同异常去向。
            if (!SameRegion(function, block, allocation, current, statement)) return null;
            matched.Add(statement);
            if (statement is Nop) continue;
            if (statement is Define d && Pure(d.Value)) { definitions[d.Target] = Expand(d.Value, definitions); continue; }
            var actual = ExprMap.MapOperands(statement, e => Expand(e, definitions));
            if (!Statement(pattern.Effects[effect], actual, bindings, widths)) return null;
            if (++effect == pattern.Effects.Count) break;
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

    private static IEnumerable<Variable> Defines(Stmt statement) => statement switch
    {
        Define d => [d.Target], Call c => c.Defines.OfType<Variable>(), _ => []
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
        if (pattern is Use use)
        {
            if (bindings.TryGetValue(use.Variable, out var bound)) return Low(bound, use.Width) == actual;
            if (!parameters.TryGetValue(use.Variable, out var width) || use.Width != width || actual.Width != width) return false;
            bindings[use.Variable] = actual;
            return true;
        }
        if (pattern.Width != actual.Width) return false;
        return (pattern, actual) switch
        {
            (Binary p, Binary a) => p.Op == a.Op && Expression(p.Left, a.Left, bindings, parameters) && Expression(p.Right, a.Right, bindings, parameters),
            (Unary p, Unary a) => p.Op == a.Op && Expression(p.Operand, a.Operand, bindings, parameters),
            (Ir.Convert p, Ir.Convert a) => p.Kind == a.Kind && Expression(p.Operand, a.Operand, bindings, parameters),
            (Load p, Load a) => Expression(p.Address, a.Address, bindings, parameters),
            (Const or Symbol, _) => pattern == actual,
            _ => false
        };
    }

    private static bool Pure(Expr expression) => ExprMap.Walk(expression).All(e => e is Const or Use or Binary or Unary or Ir.Convert or Symbol);
    private static Expr Low(Expr value, int width) => value is Use u ? u with { Width = width }
        : Fold.Convert(value.Width < width ? ConvKind.ZeroExtend : ConvKind.Truncate, value, width);
    private static Expr Expand(Expr expression, IReadOnlyDictionary<Variable, Expr> definitions) => Fold.Simplify(ExprMap.Map(expression,
        e => e is Use u && definitions.TryGetValue(u.Variable, out var value) ? Low(value, u.Width) : null));
}

public sealed partial class MethodRecovery
{
    private readonly Dictionary<MethodRef, InlineConstructors.Pattern?> constructorPatterns = new();

    private InlineConstructors.Pattern? ConstructorPattern(MethodRef method)
    {
        if (constructorPatterns.TryGetValue(method, out var cached)) return cached;
        InlineConstructors.Pattern? pattern = null;
        if (method.Method.Address != 0 && facts.Code.RegionOf(method.Method.Address) == CodeRegion.Managed
            && abi.Classify(method, out _) is { } signature && lifter.Lift(method.Method.Address) is { Succeeded: true } lifted)
        {
            var normalized = rewriter.Run(lifted.Function);
            if (normalized.Errors.Count == 0 && normalized.Residuals.Count == 0)
                pattern = InlineConstructors.Create(method, signature, lifted.Function);
        }
        return constructorPatterns[method] = pattern;
    }

    private sealed partial class Context
    {
        private readonly Dictionary<Call, InlineConstructors.Match> inlineConstructors = new(ReferenceEqualityComparer.Instance);

        private bool InlineConstructor(Block block, int index, Call allocation, DefinitionRef type, Variable created)
        {
            InlineConstructors.Match? match = null;
            foreach (var constructor in type.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic))
            {
                if (owner.ConstructorPattern(new(constructor, type.Arguments, [])) is not { } pattern
                    || InlineConstructors.Find(pattern, function, block, index, created) is not { } candidate) continue;
                if (match is not null) return false;
                match = candidate;
            }
            if (match is null) return false;
            inlineConstructors[allocation] = match;
            dropped.UnionWith(match.Statements);
            return true;
        }
    }
}
