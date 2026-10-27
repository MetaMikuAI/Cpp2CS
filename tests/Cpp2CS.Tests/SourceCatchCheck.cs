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
        var copy = new LocalValue(new(Storage.Temp(2), 1), exception, 64);
        var merged = new LocalValue(new(Storage.Temp(3), 1), exception, 64);
        var zero = new ConstantValue(0, exception, 64);
        ManagedBody NullBranch(ManagedValue value, Cond condition, params ManagedStatement[] prefix) => new(method,
            [new(0, [new ManagedReturn(0, null)]), new(1, [.. prefix,
                new ManagedBranch(1, new ComparisonValue(condition, value, zero, boolean), new(2, []), new(3, []))]),
                new(2, [new ManagedReturn(2, null)]), new(3, [new ManagedRethrow(3)])])
            { Regions = [new([0], 1, [1, 2, 3], caught, ManagedRegionKind.Catch)] };
        foreach (var condition in new[] { Cond.Eq, Cond.Ne })
        {
            var direct = SourceCaughtExceptions.Rewrite(NullBranch(caught, condition));
            a.True(direct.Blocks[1].Statements.Last() is ManagedJump jump && jump.Edge.Target == (condition == Cond.Ne ? 2UL : 3UL), "捕获对象非空，选择正确分支");
            var alias = SourceCaughtExceptions.Rewrite(NullBranch(copy, condition, new ManagedAssignment(0, copy, caught)));
            a.True(alias.Blocks[1].Statements.Last() is ManagedJump, "异常引用的唯一副本保持非空");
        }
        var nullable = NullBranch(merged, Cond.Eq, new ManagedAssignment(0, merged, caught), new ManagedAssignment(0, merged, zero));
        a.True(SourceCaughtExceptions.Rewrite(nullable).Blocks[1].Statements.Last() is ManagedBranch, "混入空值的局部保留判断");
        var replaced = NullBranch(caught, Cond.Eq, new ManagedAssignment(0, caught, zero));
        a.True(SourceCaughtExceptions.Rewrite(replaced).Blocks[1].Statements.Last() is ManagedBranch, "捕获对象重新赋值后不再假定非空");
        var addressed = NullBranch(caught, Cond.Eq, new ManagedCall(0, new(method, null, [new AddressValue(caught)], false), null, false));
        a.True(SourceCaughtExceptions.Rewrite(addressed).Blocks[1].Statements.Last() is ManagedBranch, "按引用传出的异常保留判断");
        return a.Finish("source-catches");
    }
}
