using Cpp2CS.Ir;
using Cpp2CS.Facts;

namespace Cpp2CS.Machine.Lifting;

using Storage = Cpp2CS.Ir.Storage;

/// <summary>未化简 SSA 的入口读取；未知指令或不完整控制流不能证明参数未用。</summary>
internal static class NativeInputs
{
    public static HashSet<Storage>? Reads(LiftedFunction lifted, Func<Call, Storage, bool>? unused = null, Func<Call, bool>? knownTail = null)
    {
        var statements = lifted.Function.Blocks.SelectMany(b => b.Statements).ToArray();
        var tails = statements.OfType<Call>().Where(c => c.Kind == CallKind.TailIndirect).ToArray();
        if (!lifted.Succeeded || lifted.Function.Problems.Count != 0
            || lifted.Function.UnresolvedIndirectJumps != 0 && (lifted.Function.UnresolvedIndirectJumps != tails.Length
                || !tails.All(c => VirtualTail(c, statements) || DelegateTail(c, statements) || knownTail?.Invoke(c) == true))
            || statements.Any(s => s is Opaque or IndirectJump { Targets.Length: 0 })) return null;
        if (unused is null)
            return statements.SelectMany(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable)
                    .Concat(s is Phi phi ? phi.Sources : []))
                .Where(v => v.Version == 0).Select(v => v.Storage).ToHashSet();
        var definitions = new Dictionary<Variable, Variable[]>();
        var roots = new HashSet<Variable>();
        Variable[] Uses(IEnumerable<Expr> expressions) => expressions.SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable).ToArray();
        foreach (var statement in statements)
        {
            if (statement is Phi phi) definitions[phi.Target] = phi.Sources;
            else if (statement is Define define) definitions[define.Target] = Uses([define.Value]);
        }
        bool CarriesEntry(Expr value)
        {
            var pending = new Stack<Variable>(Uses([value]));
            var seen = new HashSet<Variable>();
            while (pending.TryPop(out var variable))
            {
                if (variable.Version == 0) return true;
                if (seen.Add(variable) && definitions.TryGetValue(variable, out var inputs))
                    foreach (var input in inputs) pending.Push(input);
            }
            return false;
        }
        foreach (var statement in statements)
        {
            if (statement is Phi) continue;
            else if (statement is Define define)
            {
                var inputs = Uses([define.Value]);
                // 访存及未知运算仍是读取证据，不能因调用不消费结果而抹掉潜在异常。
                if (ExprMap.Walk(define.Value).Any(e => e is Load or Intrinsic)) roots.UnionWith(inputs);
            }
            else if (statement is Call call)
                roots.UnionWith(Uses([call.Target, .. call.Arguments.Where((value, i) => i >= call.Sources.Length
                    || !CarriesEntry(value) || !unused(call, call.Sources[i]))]));
            else roots.UnionWith(Uses(ExprMap.Operands(statement)));
        }
        var pending = new Stack<Variable>(roots);
        while (pending.TryPop(out var variable))
            if (definitions.TryGetValue(variable, out var inputs))
                foreach (var input in inputs) if (roots.Add(input)) pending.Push(input);
        return roots.Where(v => v.Version == 0).Select(v => v.Storage).ToHashSet();
    }

    private static bool DelegateTail(Call call, Stmt[] statements)
    {
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Top(Expr value, int depth = 32) => depth > 0 && value is Use use && definitions.TryGetValue(use.Variable, out var source) ? Top(source, depth - 1) : value;
        (Expr? Root, long Offset) Field(Expr value)
        {
            if (Top(value) is not Load { Width: 64 } load) return (null, 0);
            var form = AddressForm.Decompose(load.Address, new() { Expansion = AddressExpansion.BeforeSplit, Expand = e => Top(e), PreserveLeaf = true });
            return (form.Root, form.Offset);
        }
        // invoke_impl、method_code 和 method 来自同一委托；这里只证明尾调用，不裁剪未知 Invoke 的实参。
        return Field(call.Target) is { Root: { } root, Offset: 0x18 }
            && call.Arguments.Length > 1 && Field(call.Arguments[0]) == (root, 0x40)
            && call.Arguments.Skip(1).Any(a => Field(a) == (root, 0x28));
    }

    // 已知 vtable 取址及同一对象作为 this，足以证明该跳转是尾调用；所有实参仍参与入口读取分析。
    private static bool VirtualTail(Call call, Stmt[] statements)
    {
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Expand(Expr value, int depth = 32) => depth == 0 ? value : Fold.Simplify(ExprMap.Map(value,
            e => e is Use use && definitions.TryGetValue(use.Variable, out var source) ? Expand(source, depth - 1) : null));
        if (Expand(call.Target) is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Load { Width: 64 } klass, Right: Const offset } }
            || offset.Value < RuntimeLayout.ClassVtable || (offset.Value - RuntimeLayout.ClassVtable) % RuntimeLayout.VirtualInvokeDataSize != 0)
            return false;
        return call.Arguments.Length > 0 && Expand(call.Arguments[0]) == klass.Address;
    }
}
