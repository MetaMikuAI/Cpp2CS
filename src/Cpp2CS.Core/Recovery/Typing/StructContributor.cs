using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

/// <summary>ByRef this、大参数副本、x8 根与 HFA/GPR 片。内嵌叶子由表达式服务查询布局。</summary>
internal sealed class StructContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "结构体";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        var expressions = input.Expressions(context);
        foreach (var (register, argument) in input.Arguments)
            if (argument.Type is Model.ByRefRef || input.StructArguments.ContainsKey(register))
            {
                var variable = new Variable(register, 0);
                var type = input.StructArguments.ContainsKey(register) ? expressions.TypeOf(new Use(variable, argument.Width)) : argument.Type;
                if (type is not null) constraints.Defines(variable, type, new(Name, context.Function.Entry, $"入口 ABI {register}:{argument.Width}，聚合 {argument.Type}"));
            }
        var abi = new ManagedAbi(context.Types.Layouts);
        foreach (var call in context.Statements.OfType<Call>())
            if (context.Resolve(call) is { } method && abi.Classify(method, out _)?.Return is { Passing: Passing.Registers } returned && context.Types.Kind(returned.Type) == TypeKind.Struct)
                foreach (var piece in returned.Pieces)
                {
                    var index = Array.IndexOf(call.Results, piece.Register);
                    if (index < 0 || index >= call.Defines.Length || call.Defines[index] is not { } variable) continue;
                    if (expressions.TypeOf(new Use(variable, piece.Width)) is { } type)
                        constraints.Defines(variable, type, new(Name, call.Address, $"{method} 返回片 {piece.Register} +{piece.Offset}:{piece.Width}，聚合 {returned.Type}"));
                }
    }
}
