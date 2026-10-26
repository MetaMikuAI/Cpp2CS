using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class AsyncGenericContextCheck
{
    [Command("async-generic-context", "异步提升中的闭包、委托与入口泛型参数身份", Gate = Gate.Unit)]
    public static int Run()
    {
        var index = 0;
        TypeDef Type(string name, bool value = false) => new() { Index = index++, Assembly = "Async.Tests.dll", Namespace = "Tests", Name = name,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = false };
        var nothing = new PrimitiveRef("Void");
        MethodDef Method(TypeDef type, string name) => new() { Index = index++, Owner = type, Name = name, Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = nothing };
        var owner = Type("Owner"); var machine = Type("Machine`1", true); var closure = Type("Closure`1");
        var action = Type("Action`1"); var builder = Type("Builder", true);
        var typeParameter = new GenericParameterRef("T", false, 0);
        var methodParameter = new GenericParameterRef("T", true, 0);
        var machineType = new DefinitionRef(machine, [typeParameter]);
        var actualMachine = new DefinitionRef(machine, [methodParameter]);
        var closureType = new DefinitionRef(closure, [typeParameter]);
        var actionType = new DefinitionRef(action, [typeParameter]);
        var builderType = new DefinitionRef(builder, []);
        var builderField = new FieldDef { Index = index++, Owner = machine, Name = "<>t__builder", Type = builderType, Offset = 8, Attributes = FieldAttributes.Public };
        var local = new LocalValue(new(Storage.Temp(1), 1), actualMachine, 0);
        var kickoff = new ManagedBody(new(Method(owner, "Begin"), [], [methodParameter]), [new(0, [
            new ManagedCall(0, new(new(Method(builder, "Start"), [], [actualMachine]), null, [new AddressValue(local)], false), null, false),
            new ManagedReturn(1, null)])]);
        var receiver = new ArgumentValue(-1, machineType, 64);
        var builderValue = new AddressValue(new FieldValue(receiver, new(builderField, machineType), builderType, 0));
        var created = new LocalValue(new(Storage.Temp(2), 1), closureType, 64);
        var callback = new LocalValue(new(Storage.Temp(3), 1), actionType, 64);
        var body = new ManagedBody(new(Method(machine, "MoveNext"), [typeParameter], []), [new(0, [
            new ManagedAssignment(0, created, new NewObjectValue(new(Method(closure, ".ctor"), [typeParameter], []), []) { Transparent = true }),
            new ManagedAssignment(1, callback, new DelegateValue(actionType, created, new(Method(closure, "Accept"), [typeParameter], []), DelegateBinding.ClosedInstance)),
            new ManagedCall(2, new(new(Method(builder, "SetResult"), [], []), builderValue, [callback], false), null, false),
            new ManagedReturn(3, null)]), new(10, [
            new ManagedCall(10, new(new(Method(builder, "SetException"), [], []), builderValue, [], false), null, false),
            new ManagedReturn(11, null)])]) { Regions = [new([0], 10, [10], null, ManagedRegionKind.Catch)] };
        var a = new Assertions();
        var lifted = AsyncLifting.Lift(kickoff, body, out var reason);
        a.True(lifted is not null, $"泛型闭包与委托可提升：{reason}");
        var values = lifted?.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).ToArray() ?? [];
        var allocation = values.OfType<NewObjectValue>().SingleOrDefault();
        var binding = values.OfType<DelegateValue>().SingleOrDefault();
        a.True(allocation is { Transparent: true } && allocation.Constructor.TypeArguments.SequenceEqual([methodParameter])
            && allocation.Type.Equals(new DefinitionRef(closure, [methodParameter])), "构造引用及值类型一同映射，保留透明执行标志");
        a.True(binding is not null && binding.Method.TypeArguments.SequenceEqual([methodParameter])
            && binding.Type.Equals(new DefinitionRef(action, [methodParameter]))
            && binding.Target.Type.Equals(new DefinitionRef(closure, [methodParameter])), "委托类型、目标及被调方法使用入口方法参数");
        a.True(body.Blocks[0].Statements.OfType<ManagedAssignment>().First().Value.Type.Equals(closureType), "原始 MoveNext 保持不变");
        return a.Finish("async-generic-context");
    }
}
