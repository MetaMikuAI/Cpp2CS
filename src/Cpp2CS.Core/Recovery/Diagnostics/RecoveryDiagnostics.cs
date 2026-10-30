using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class RecoveryDiagnostics
{
    internal static RecoveryHole Hole(this RecoveryScope ctx, ulong address, string reason, string rule, bool derived = false) => ctx.ledger.Add(address, reason, derived, "recovery." + rule);
    internal static RecoveryFailure Fail(ulong address, string reason, string rule) => new(address, reason, Code: "recovery." + rule);
    internal static RecoveryFailure Derived(RecoveryHole cause, string reason) => new(0, HoleLedger.DerivedReason(cause, reason), true, cause);
    internal static RecoveryFailure? CheckPoison(this RecoveryScope ctx, Variable variable) => ctx.ledger.TryGetPoison(variable, out var cause) ? RecoveryDiagnostics.Derived(cause, $"变量 {variable} 依赖未恢复的值") : null;
    internal static void Poison(this RecoveryScope ctx, Variable variable, RecoveryHole cause) => ctx.ledger.Poison(variable, cause);
    internal static void Poison(this RecoveryScope ctx, Stmt statement, RecoveryHole cause) => ctx.ledger.Poison(statement, cause);
    internal static IEnumerable<Variable> DefinedBy(this RecoveryScope ctx, Stmt statement)
    {
        if (statement is Define define)
            yield return define.Target;
        if (statement is Call call)
        {
            foreach (var result in call.Defines)
                if (result is not null)
                    yield return result;
            if (ctx.State.Construction.constructed.TryGetValue(call, out var created))
                yield return created;
        }
    }

    internal static RecoveryHole Record(this RecoveryScope ctx, RecoveryFailure exception, ulong address, Stmt? statement = null)
    {
        var hole = ctx.ledger.Add(exception.Address == 0 ? address : exception.Address, exception.Message, exception.Derived, exception.Code);
        if (exception.Cause is { } source)
            ctx.ledger.Link(hole, source);
        if (exception.Unresolved is { } variable)
            ctx.ledger.Unresolved(variable, statement);
        // 未定型的定义可能来自尚未遍历到的调用/回边；等全部语句诊断完再决定根因。
        if (statement is not null && (exception.Unresolved is null || statement is Call))
            ctx.Poison(statement, exception.Cause ?? hole);
        return exception.Cause ?? hole;
    }

    /// <summary>值中有 L3 内部的值（结构体片等，ManagedValues 不认识的类型）。</summary>
    internal static bool FragmentInside(ManagedValue value)
    {
        if (value is Fragment or AggregatePiece)
            return true;
        return ManagedValues.Children(value).Any(RecoveryDiagnostics.FragmentInside);
    }
}
