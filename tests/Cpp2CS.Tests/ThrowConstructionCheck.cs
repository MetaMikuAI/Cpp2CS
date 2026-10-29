using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class ThrowConstructionCheck
{
    [Command("throw-construction", "抛异常包装的参数求值顺序、额外操作与局部来源边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = 0, Assembly = "Tests.dll", Namespace = "Tests", Name = "Errors", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var type = new DefinitionRef(owner, []);
        var definition = new MethodDef { Index = 0, Owner = owner, Name = "Fail", Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1,
            Parameters = [new("first", type, 0, null, false), new("second", type, 0, null, false)] };
        var constructor = new MethodDef { Index = 1, Owner = owner, Name = ".ctor", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, Parameters = definition.Parameters };
        var first = new ArgumentValue(0, type, 64);
        var second = new ArgumentValue(1, type, 64);
        var created = new NewObjectValue(MethodRef.Open(constructor), [first, second]);
        var local = new LocalValue(new(Storage.Gpr(0), 1), type, 64);
        ManagedBody Body(params ManagedStatement[] statements) => new(MethodRef.Open(definition), [new(0x100, statements)]);
        var direct = Body(new ManagedThrow(0x100, created));
        var assigned = Body(new ManagedAssignment(0x100, local, created), new ManagedThrow(0x104, local));
        var a = new Assertions();
        a.Equal(created, MethodRecovery.ThrowConstruction(direct), "直接构造并抛出");
        a.Equal(created, MethodRecovery.ThrowConstruction(assigned), "抛出唯一赋值的构造结果");
        a.True(MethodRecovery.ThrowConstruction(Body(new ManagedThrow(0x100, created with { Arguments = [second, first] }))) is null, "不能重排调用方的求值");
        a.True(MethodRecovery.ThrowConstruction(Body(new ManagedThrow(0x100, created with { Arguments = [first, first] }))) is null, "不能复制参数求值");
        a.True(MethodRecovery.ThrowConstruction(Body(new ManagedThrow(0x100, created with { Arguments = [first] }))) is null, "不能省略参数求值");
        a.True(MethodRecovery.ThrowConstruction(Body(new ManagedThrow(0x100, created with { Arguments = [local, second] }))) is null, "不引用包装方法的未知局部");
        a.True(MethodRecovery.ThrowConstruction(Body(new ManagedAssignment(0x100, local, created),
            new ManagedThrow(0x104, local with { Variable = new(Storage.Gpr(1), 1) }))) is null, "抛出对象必须来自这次构造");
        a.True(MethodRecovery.ThrowConstruction(Body(new ManagedCall(0x100, new(MethodRef.Open(definition), null, [first, second], false), null, false),
            new ManagedThrow(0x104, created))) is null, "额外调用不能删除");
        a.True(MethodRecovery.ThrowConstruction(Body(new ManagedReturn(0x100, null))) is null, "普通返回不形成抛出证明");
        a.True(MethodRecovery.ThrowConstruction(direct with { Regions = [new([0x100], 0x200, [0x200], local, ManagedRegionKind.Catch)] }) is null, "异常区域不折叠");
        a.True(MethodRecovery.ThrowConstruction(Body(new ManagedThrow(0x100, created with { Transparent = true }))) is null, "内联构造仍需原有透明执行证据");
        return a.Finish("throw-construction");
    }
}
