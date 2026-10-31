using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

internal sealed class TypeCheckContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "类型检查";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        foreach (var (call, klass) in input.Expressions(context).TypeChecks())
        {
            if (klass is Use use)
                constraints.IsRuntime(use.Variable, RuntimeContributor.Legacy, new(Name, call.Address, $"klass = {klass} 的已证托管对象类指针读取"));
            foreach (var variable in call.Defines.OfType<Variable>())
                constraints.Defines(variable, context.Types.UInt64, new(Name, call.Address, "继承检查返回 0/1 的 UInt64"));
        }
    }

}
