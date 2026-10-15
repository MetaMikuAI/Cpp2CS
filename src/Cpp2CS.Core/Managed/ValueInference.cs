using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

public sealed partial class ValueRecovery
{
    private readonly Dictionary<Variable, Define> definitions = new();
    private readonly Dictionary<Variable, Phi> phis = new();

    private void Infer()
    {
        foreach (var statement in method.Function.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is Define define)
            {
                definitions.Add(define.Target, define);
                // 运算结果的类型约束先于操作数求解；下方必须核验操作数，不能把约束当作恢复成功。
                if (NumericResult(define.Value) is { } type) locals.Add(define.Target, (type, define.Value.Width));
            }
            else if (statement is Phi phi) phis.Add(phi.Target, phi);
        }

        bool changed;
        do
        {
            changed = false;
            foreach (var define in definitions.Values)
                if (!locals.ContainsKey(define.Target) && Recover(define.Value, out _) is { } value)
                {
                    locals.Add(define.Target, (value.Type, value.Width));
                    changed = true;
                }
            foreach (var phi in phis.Values)
                if (!locals.ContainsKey(phi.Target) && PhiType(phi) is { } shape)
                {
                    locals.Add(phi.Target, shape);
                    changed = true;
                }
        } while (changed);

        // 撤销不满足约束的结果，并传播撤销。循环内的候选不能掩盖任何未知入口、无效操作或不兼容的边。
        do
        {
            changed = false;
            foreach (var define in definitions.Values)
                if (locals.TryGetValue(define.Target, out var shape)
                    && (Recover(define.Value, out _) is not { } value || (value.Type, value.Width) != shape))
                    changed |= locals.Remove(define.Target);
            foreach (var phi in phis.Values)
                if (locals.TryGetValue(phi.Target, out var shape)
                    && phi.Sources.Any(source => Shape(source) is null || RecoverAs(new Use(source, shape.Width), shape.Type, out _) is null))
                    changed |= locals.Remove(phi.Target);
        } while (changed);
    }

    private (TypeRef Type, int Width)? Shape(Variable variable) => variable.Version == 0
        ? arguments.TryGetValue(variable.Storage, out var argument) ? (argument.Type, argument.Width) : null
        : locals.TryGetValue(variable, out var local) ? local : null;

    private (TypeRef Type, int Width)? PhiType(Phi phi)
    {
        // 展开 φ 之间的环，只由环外的真实来源决定类型。没有来源的环仍为未知。
        var pending = new Stack<Variable>(phi.Sources);
        var seen = new HashSet<Variable>();
        var sources = new List<Variable>();
        while (pending.TryPop(out var variable))
        {
            if (!seen.Add(variable)) continue;
            if (phis.TryGetValue(variable, out var incoming))
                foreach (var source in incoming.Sources) pending.Push(source);
            else
            {
                if (Shape(variable) is null) return null;
                sources.Add(variable);
            }
        }
        if (sources.Count == 0) return null;
        var shapes = sources.Select(v => Shape(v)!.Value).ToArray();
        if (shapes.All(s => s == shapes[0])) return shapes[0];
        if (shapes.All(s => Numeric(s.Type)))
        {
            var width = shapes.Max(s => s.Width);
            return Integer(width) is { } type ? (type, width) : null;
        }
        var references = sources.Where(v => !IsZero(v)).Select(v => Shape(v)!.Value).ToArray();
        if (references.Length == 0 || references.Any(s => !ManagedTypes.IsReferenceType(s.Type))) return null;
        var common = references[0].Type;
        foreach (var source in references.Skip(1))
        {
            while (!types.IsAssignable(source.Type, common))
                common = common is DefinitionRef { Definition.BaseType: { } parent } definition
                    ? parent.Substitute(definition.Arguments, []) : types.Object;
        }
        return (common, 64);
    }

    private TypeRef? NumericResult(Expr value) => value switch
    {
        Const constant => Integer(constant.Width),
        Compare or Logical or Not => types.Boolean,
        Ir.Convert c => c.Kind is ConvKind.SIntToFloat or ConvKind.UIntToFloat or ConvKind.FloatToFloat
            ? Float(c.Width) : Integer(c.Width, c.Kind is ConvKind.SignExtend or ConvKind.FloatToSInt),
        Binary b => b.Op is BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv or BinOp.FMin or BinOp.FMax
            ? Float(b.Width) : Integer(b.Width, b.Op is BinOp.SDiv or BinOp.SRem or BinOp.AShr or BinOp.MulHighS),
        Unary u => u.Op is UnOp.FNeg or UnOp.FAbs or UnOp.FSqrt or UnOp.FFloor or UnOp.FCeil or UnOp.FTrunc
            or UnOp.FRoundEven or UnOp.FRoundAway or UnOp.FRoundCurrent ? Float(u.Width) : Integer(u.Width),
        _ => null,
    };

    private bool IsZero(Variable variable) => AllLeaves(variable, define => Fold.Simplify(define.Value) is Const { Value: 0 });

    // Define 的窄写在 IR 中明确清零高位；入口参数和调用返回没有这一保证。
    private bool ZeroHigh(Variable variable, int width) => AllLeaves(variable, define => define.Value.Width <= width);

    private bool AllLeaves(Variable root, Func<Define, bool> matches)
    {
        var pending = new Stack<Variable>();
        pending.Push(root);
        var seen = new HashSet<Variable>();
        var found = false;
        while (pending.TryPop(out var variable))
        {
            if (!seen.Add(variable)) continue;
            if (phis.TryGetValue(variable, out var phi))
                foreach (var source in phi.Sources) pending.Push(source);
            else
            {
                if (!definitions.TryGetValue(variable, out var define) || !matches(define)) return false;
                found = true;
            }
        }
        return found;
    }
}
