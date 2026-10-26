using System.Reflection;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class ConstrainedCallCheck
{
    [Command("constrained-call", "受约束直接调用的接口槽位与泛型身份", Gate = Gate.Unit)]
    public static int Run()
    {
        TypeDef Type(int index, string name, bool value, bool contract = false) => new() { Index = index, Assembly = "Calls.Tests.dll", Namespace = "Tests", Name = name,
            Token = 0, Attributes = TypeAttributes.Public | (contract ? TypeAttributes.Interface : 0), IsValueType = value, IsEnum = false };
        MethodDef Method(int index, TypeDef type, string name) => new() { Index = index, Owner = type, Name = name, Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Virtual, ImplAttributes = 0, Slot = 0 };
        var contract = Type(1, "IWorker", false, true); var type = Type(2, "Worker`1", true);
        var parameter = new GenericParameterDef { Name = "T", Position = 0, Attributes = 0 };
        type.GenericParameters = [parameter];
        var generic = new GenericParameterRef("T", true, 0) { Parameter = parameter };
        var receiver = new DefinitionRef(type, [generic]); var contractType = new DefinitionRef(contract, []);
        var requirement = Method(1, contract, "Run"); var implementation = Method(2, type, "Run"); var other = Method(3, type, "Other");
        type.InterfaceOffsets = [(contractType, 1)]; type.VTable = [new(other, [], []), new(implementation, [], [])];
        var reference = new MethodRef(requirement, [], []);
        var a = new Assertions();
        a.Equal(new MethodRef(implementation, [generic], []), MethodRecovery.ConstrainedImplementation(receiver, reference, [implementation]), "非零接口偏移保留调用者的开放实参");
        a.True(MethodRecovery.ConstrainedImplementation(receiver, reference, [other]) is null, "注册入口与槽位实现不同则拒绝");
        a.True(MethodRecovery.ConstrainedImplementation(generic, reference, [implementation]) is null, "只有 T 而无具体实现类型则拒绝");
        type.InterfaceOffsets = [(contractType, 5)];
        a.True(MethodRecovery.ConstrainedImplementation(receiver, reference, [implementation]) is null, "槽位越界不猜测实现");
        type.InterfaceOffsets = [];
        a.True(MethodRecovery.ConstrainedImplementation(receiver, reference, [implementation]) is null, "类型未实现接口则拒绝");
        return a.Finish("constrained-call");
    }
}
