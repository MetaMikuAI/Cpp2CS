using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceStringCreationCheck
{
    [Command("source-string-creation", "字符串工厂的真实转调与求值边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new MethodRecovery(facts, types);
        var a = new Assertions();
        var factories = types.String.Definition.Methods.Where(m => m.Name == "CreateString"
            && m.Parameters[0].Type is ArrayRef { IsVector: true, Element: var element } && ManagedTypes.PrimitiveName(element) == "Char"
            || m.Owner == types.String.Definition && m.Name == "CreateString" && m.Parameters.Count == 2 && ManagedTypes.PrimitiveName(m.Parameters[0].Type) == "Char").ToArray();
        a.Equal(3, factories.Length, "匹配字符重复、字符数组及字符区间三个库入口");
        foreach (var factory in factories)
        {
            var reference = new MethodRef(factory, [], []);
            var body = SourceRewriter.Rewrite(recovery.Recover(reference, factory.Address).Body!, types);
            var constructor = SourceStringCreation.Constructor(body, types);
            a.True(constructor is not null, "真实实例工厂忽略 this 并原样转调静态 Ctor");
            if (constructor is null) continue;
            var forwarding = (ManagedCall)body.Blocks.Single().Statements.Single();
            var result = new LocalValue(new(Storage.Gpr(0), 1), types.String, 64);
            var call = new ManagedCall(0, new(reference, new ConstantValue(0, types.String, 64), forwarding.Invocation.Arguments, false), result, false);
            a.True(SourceStringCreation.Rewrite(call, constructor) is ManagedAssignment { Value: NewObjectValue }, "null 接收者的实例工厂生成构造表达式");
            a.True(SourceStringCreation.Rewrite(call with { Tail = true, Result = null }, constructor) is ManagedReturn { Value: NewObjectValue }, "尾调用保留返回值");
            a.Equal(call with { Result = null }, SourceStringCreation.Rewrite(call with { Result = null }, constructor), "未使用的分配保留原调用，不丢弃异常");
            var effect = new NewObjectValue(constructor, call.Invocation.Arguments);
            var evaluated = call with { Invocation = call.Invocation with { Receiver = effect } };
            a.Equal(evaluated, SourceStringCreation.Rewrite(evaluated, constructor), "接收者求值含副作用时拒绝");
            var virtualCall = call with { Invocation = call.Invocation with { Virtual = true } };
            a.Equal(virtualCall, SourceStringCreation.Rewrite(virtualCall, constructor), "虚调用不当作工厂直接转调");
            var swapped = forwarding with { Invocation = forwarding.Invocation with
                { Arguments = [new ArgumentValue(-1, types.String, 64), .. forwarding.Invocation.Arguments.Skip(1)] } };
            a.True(SourceStringCreation.Constructor(body with { Blocks = [new(0, [swapped])] }, types) is null, "读取接收者或改变参数时拒绝");
            a.True(SourceStringCreation.Constructor(body with { Blocks = [new(0, [new ManagedReturn(0, null), forwarding])] }, types) is null,
                "有额外语句时不当作纯转调");
        }
        return a.Finish("source-string-creation");
    }
}
