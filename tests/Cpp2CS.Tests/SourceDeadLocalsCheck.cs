using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceDeadLocalsCheck
{
    [Command("source-dead-locals", "异常退出、外层观察和同时复制的局部存活", Gate = Gate.Unit)]
    public static int Run()
    {
        var type = new TypeDef { Index = 1, Assembly = "Checks.dll", Namespace = "", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodRef(new MethodDef { Index = 1, Owner = type, Name = "Read", Token = 0, Attributes = MethodAttributes.Public,
            ImplAttributes = 0, Slot = -1, ReturnType = new PrimitiveRef("Int32") }, [], []);
        var integer = new PrimitiveRef("Int32"); var obj = new DefinitionRef(type, []);
        LocalValue Local(int index, TypeRef t) => new(new(Storage.Temp(index), 1), t, 64);
        var value = Local(1, integer); var other = Local(2, integer); var exception = Local(3, obj); var outerException = Local(4, obj);
        var zero = new ConstantValue(0, integer, 32); var one = new ConstantValue(1, integer, 32);
        var a = new Assertions();
        foreach (var outer in new[] { false, true })
        {
            var body = new ManagedBody(method, [new(0, [new ManagedAssignment(0, value, one), new ManagedJump(0, new(2, []))]),
                new(1, [new ManagedAssignment(1, value, zero), new ManagedCall(1, new(method, null, [], false), null, false), new ManagedThrow(1, exception)]),
                new(2, [new ManagedReturn(2, value)]), new(3, [new ManagedCall(3, new(method, null, [value], false), null, false), new ManagedThrow(3, outerException)])])
                { Regions = outer ? [new([0], 1, [1], exception, ManagedRegionKind.Catch), new([0, 1, 2], 3, [3], outerException, ManagedRegionKind.Catch)]
                    : [new([0], 1, [1], exception, ManagedRegionKind.Catch)] };
            var result = SourceDeadLocals.Rewrite(body);
            a.Equal(outer, result.Blocks[1].Statements.OfType<ManagedAssignment>().Any(), "外层可以观察时保留异常路径写入");
            a.Equal(1, result.Blocks[1].Statements.OfType<ManagedCall>().Count(), "清理调用保留");
            a.Equal(1, result.Blocks[0].Statements.OfType<ManagedAssignment>().Count(), "正常返回读取的值保留");
        }
        var swap = new ManagedBody(method, [new(0, [new ManagedAssignment(0, value, zero), new ManagedAssignment(0, other, one),
            new ManagedJump(0, new(1, [new(value, other), new(other, value)]))]), new(1, [new ManagedReturn(1, value)])]);
        var swapped = SourceDeadLocals.Rewrite(swap);
        a.True(swapped.Blocks[0].Statements.OfType<ManagedAssignment>().Single().Target == other, "同时复制读取赋值前的源值");
        a.True(swapped.Blocks[0].Statements.OfType<ManagedJump>().Single().Edge.Copies is [{ Target: var target }] && target == value, "只保留被后继读取的目标");
        var addressed = new ManagedBody(method, [new(0, [new ManagedCall(0, new(method, null, [new AddressValue(value)], false), null, false),
            new ManagedAssignment(0, value, zero), new ManagedReturn(0, null)])]);
        a.Equal(1, SourceDeadLocals.Rewrite(addressed).Blocks[0].Statements.OfType<ManagedAssignment>().Count(), "取址的局部不删除写入");
        var faulting = new ManagedBody(method, [new(0, [new ManagedAssignment(0, value, new ArrayLengthValue(Local(5, new ArrayRef(integer, 1)), integer, 32)), new ManagedReturn(0, null)])]);
        a.Equal(1, SourceDeadLocals.Rewrite(faulting).Blocks[0].Statements.OfType<ManagedAssignment>().Count(), "未用到的数组长度读取仍保留异常");
        return a.Finish("source-dead-locals");
    }
}
