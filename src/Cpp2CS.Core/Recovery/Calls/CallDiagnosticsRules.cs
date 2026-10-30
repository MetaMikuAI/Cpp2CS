using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class CallDiagnosticsRules
{
    internal static string CallResolutionFailure(this RecoveryScope ctx, Call call)
    {
        if (ctx.State.Calls.callBindings.Resolution(call) is { Status: "conflict" } conflict)
            return $"调用 多个兼容候选未消歧：{string.Join('；', conflict.Candidates.Where(c => c.Rejection is null).Select(c => c.Method))}";
        if (call.Op is not null)
            return $"调用 {call.Op} 的方法未确定";
        if (call.Target is not Const target)
            return "调用 目标地址未确定";
        var entries = ctx.facts.EntriesAt(target.Value);
        if (entries.Length == 0)
        {
            if (ctx.facts.Unregistered.At(target.Value) is { } identity)
            {
                UnregisteredMethods.Resolve(identity, call, ctx.Expand, ctx.owner.abi, out var problem);
                return $"调用 目标没有注册身份；已有推断定义，但调用实例未确定：{problem}";
            }

            return "调用 目标没有注册身份";
        }

        var candidates = entries.Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod && e.Method is not null).Select(e => e.Method!).Distinct().ToArray();
        if (candidates.Length == 0)
            return "调用 目标已注册，但没有可用的 Method/GenericMethod 定义";
        var receiver = ConstructionRules.Receiver(call) is { } value ? ctx.TypeOfValue(value) : null;
        var definitions = candidates.Select(c => c.Method).Distinct().ToArray();
        var reasons = new List<string>();
        if (definitions.Any(m => !m.IsStatic))
            reasons.Add(receiver is null ? "接收者类型未定" : $"接收者类型为 {receiver}，未能据此选出兼容实例");
        if (definitions.Any(m => m.GenericParameters.Count > 0))
            reasons.Add("方法泛型实参未确定");
        if (definitions.Any(m => m.Owner.GenericParameters.Count > 0))
            reasons.Add("声明类型泛型实参未确定");
        var registers = CallResolution.ArgumentsOf(call);
        var hidden = candidates.Select(candidate =>
        {
            var signature = ctx.owner.abi.Classify(candidate, out _);
            if (signature is null)
                return "MethodInfo 的 ABI 位置未确定";
            if (signature.MethodInfo is not { } info)
                return "MethodInfo 在栈上";
            if (!registers.TryGetValue(info.Register, out var argument))
                return "MethodInfo 寄存器实参缺失";
            return ctx.Expand(argument) switch
            {
                Const { Value: 0 } => "MethodInfo 为零",
                Symbol { Kind: SymbolKind.Method } => "MethodInfo 符号未匹配注册定义",
                _ => "MethodInfo 不是已确定的 Method 符号",
            };
        }).Distinct().Order(StringComparer.Ordinal);
        reasons.AddRange(hidden);
        return $"调用 目标已注册，但无法选出具体实例（{string.Join('；', reasons)}）";
    }
}
