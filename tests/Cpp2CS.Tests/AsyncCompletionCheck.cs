using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class AsyncCompletionCheck
{
    [Command("async-completion", "同步完成的异步方法按入口证据消除接收者判空", Gate = Gate.Unit)]
    public static int Run()
    {
        TypeDef Type(string name, bool value) => new() { Index = -1, Assembly = "Completion.Tests.dll", Namespace = "Tests", Name = name,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = false };
        var owner = Type("Subject", false); var machine = Type("StateMachine", true); var builder = Type("Builder", true);
        var ownerType = new DefinitionRef(owner, []); var machineType = new DefinitionRef(machine, []); var builderType = new DefinitionRef(builder, []);
        var boolean = new PrimitiveRef("Boolean"); var nothing = new PrimitiveRef("Void");
        MethodDef Method(TypeDef type, string name) => new() { Index = -1, Owner = type, Name = name, Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = nothing };
        var capture = new FieldDef { Index = -1, Owner = machine, Name = "<>4__this", Type = ownerType, Offset = 16, Attributes = FieldAttributes.Public };
        var builderField = new FieldDef { Index = -2, Owner = machine, Name = "<>t__builder", Type = builderType, Offset = 8, Attributes = FieldAttributes.Public };
        var local = new LocalValue(new(Storage.Temp(1), 1), machineType, 0);
        FieldValue Capture(ManagedValue instance) => new(instance, new(capture, machineType), ownerType, 64);
        var receiver = new ArgumentValue(-1, machineType, 64);
        var finish = new ManagedCall(4, new(new(Method(builder, "SetResult"), [], []),
            new AddressValue(new FieldValue(receiver, new(builderField, machineType), builderType, 0)), [], false), null, false);
        var check = new ManagedCheck(3, new ComparisonValue(Cond.Eq, Capture(receiver), new ConstantValue(0, ownerType, 64), boolean),
            new(Method(Type("NullReferenceException", false), ".ctor"), [], []));
        ManagedBody Kickoff(int argument) => new(new(Method(owner, "Begin"), [], []), [new(0, [
            new ManagedStore(0, Capture(new AddressValue(local)), new ArgumentValue(argument, ownerType, 64)),
            new ManagedCall(1, new(new(Method(builder, "Start"), [], [machineType]), null, [new AddressValue(local)], false), null, false),
            new ManagedReturn(2, null)])]);
        var move = new ManagedBody(new(Method(machine, "MoveNext"), [], []), [new(0, [check, finish, new ManagedReturn(5, null)])]);
        var a = new Assertions();
        var lifted = AsyncLifting.Lift(Kickoff(-1), move, out var reason);
        a.True(lifted is not null, $"实例接收者原样捕获后同步完成：{reason}");
        a.True(lifted?.Blocks.SelectMany(b => b.Statements).ToArray() is [ManagedReturn { Value: AsyncResultValue }], "只剩完成标记，不残留判空或状态机字段");
        var copied = new LocalValue(new(Storage.Temp(2), 1), ownerType, 64);
        var copiedCheck = check with { Condition = new ComparisonValue(Cond.Eq, copied, new ConstantValue(0, ownerType, 64), boolean) };
        var copiedBody = move with { Blocks = [new(0, [new ManagedAssignment(0, copied, Capture(receiver)), copiedCheck, finish, new ManagedReturn(5, null)])] };
        a.True(AsyncLifting.Lift(Kickoff(-1), copiedBody, out _) is not null, "原样复制到单次赋值局部变量后仍能识别接收者");
        a.True(AsyncLifting.Lift(Kickoff(0), move, out _) is null, "普通参数仍可能为空，不能把它当作实例接收者");
        var overwritten = move with { Blocks = [new(0, [new ManagedStore(0, Capture(receiver), new ConstantValue(0, ownerType, 64)), check, finish, new ManagedReturn(5, null)])] };
        a.True(AsyncLifting.Lift(Kickoff(-1), overwritten, out _) is null, "捕获被重写时保留判空");
        return a.Finish("async-completion");
    }
}
