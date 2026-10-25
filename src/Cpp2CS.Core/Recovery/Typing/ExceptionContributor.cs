using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

/// <summary>F5：由已证明的 catch 区域给出 wrapper 种子，重新推导别名、+0 异常对象和保留边上的 φ。</summary>
internal sealed class ExceptionContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "异常";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        if (!input.HasExceptions) return;
        var (wrappers, exceptions) = (input.Wrappers, input.Exceptions);
        foreach (var (variable, exception) in exceptions)
            constraints.Defines(variable, exception.Type, new(Name, context.Function.Entry, $"catch 对象 {exception.Variable}，wrapper+0/别名/同源 φ"));
        foreach (var variable in wrappers.Keys)
            constraints.IsRuntime(variable, RuntimeContributor.Legacy, new(Name, context.Function.Entry, "BeginCatch wrapper/同源别名"));
        foreach (var define in context.Statements.OfType<Define>())
            if (define.Value is Intrinsic { Name: "eh_exception" or "eh_selector" } intrinsic)
                constraints.IsRuntime(define.Target, RuntimeContributor.Legacy, new(Name, define.Address, intrinsic.Name));
    }
}
