using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceCatchCheck
{
    [Command("source-catches", "异常类型恢复不将 object 或接口写成 catch 类型", Gate = Gate.Unit)]
    public static int Run()
    {
        var index = 0;
        TypeDef Type(string name, TypeRef? parent = null) => new() { Index = index++, Assembly = "mscorlib.dll", Namespace = "System", Name = name,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, BaseType = parent };
        var obj = new DefinitionRef(Type("Object"), []);
        var exception = new DefinitionRef(Type("Exception", obj), []);
        var derived = new DefinitionRef(Type("InvalidOperationException", exception), []);
        var unrelated = new DefinitionRef(Type("IComparable"), []);
        var boolean = new PrimitiveRef("Boolean");
        var caught = new LocalValue(new(Storage.Temp(1), 1), exception, 64);
        var method = new MethodRef(new MethodDef { Index = index++, Owner = Type("Subject"), Name = "Read", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = new PrimitiveRef("Void") }, [], []);
        ManagedBody Body(TypeRef type) => new(method, [
            new(0, [new ManagedReturn(0, null)]),
            new(1, [new ManagedBranch(1, new ComparisonValue(Cond.Ne, new IsInstValue(caught, type), new ConstantValue(0, type, 64), boolean), new(2, []), new(3, []))]),
            new(2, [new ManagedReturn(2, null)]), new(3, [new ManagedRethrow(3)])])
            { Regions = [new([0], 1, [1, 2, 3], caught, ManagedRegionKind.Catch)] };
        var a = new Assertions();
        foreach (var type in new TypeRef[] { obj, unrelated })
        {
            var body = Body(type);
            a.True(ReferenceEquals(body, SourceRewriter.TypedCatches(body)), $"{type} 保留内部判断，不扩张捕获类型");
        }
        foreach (var type in new TypeRef[] { exception, derived })
        {
            var body = Body(type);
            var result = SourceRewriter.TypedCatches(body);
            a.Equal(type, result.Regions[0].CatchType, $"{type} 恢复合法 catch 类型");
            a.True(result.Blocks[1].Statements is [ManagedJump { Edge.Target: 2 }], "保留匹配分支");
            a.True(body.Regions[0].CatchType is null, "输入异常区域不变");
        }
        return a.Finish("source-catches");
    }
}
