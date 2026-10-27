using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceCheckedCastCheck
{
    [Command("source-checked-casts", "显式引用转换的 null 旁路、检查极性与异常位置", Gate = Gate.Unit)]
    public static int Run()
    {
        DefinitionRef Type(string name) => new(new TypeDef { Index = name.GetHashCode(), Assembly = "mscorlib.dll", Namespace = "System", Name = name,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false }, []);
        var obj = Type("Object");
        var target = Type("String");
        var boolean = new PrimitiveRef("Boolean");
        var integer = new PrimitiveRef("U8");
        var source = new ArgumentValue(0, obj, 64);
        var flag = new LocalValue(new(Storage.Temp(1), 1), integer, 64);
        var result = new LocalValue(new(Storage.Temp(2), 1), target, 64);
        var exception = new MethodRef(new MethodDef { Index = 1, Owner = Type("InvalidCastException").Definition, Name = ".ctor", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        var cast = new IsInstValue(source, target);
        var matches = new ConversionValue(ConvKind.ZeroExtend,
            new ComparisonValue(Cond.Ne, cast, new ConstantValue(0, target, 64), boolean), integer, 64);
        var failed = new ComparisonValue(Cond.Eq, flag, new ConstantValue(0, integer, 64), boolean);
        ManagedBody Body(Cond nullTest = Cond.Eq) => new(null!, [
            new(0, [new ManagedBranch(0, new ComparisonValue(nullTest, source, new ConstantValue(0, obj, 64), boolean),
                new(nullTest == Cond.Eq ? 8UL : 4UL, []), new(nullTest == Cond.Eq ? 4UL : 8UL, []))]),
            new(4, [new ManagedAssignment(4, flag, matches), new ManagedCheck(5, failed, exception), new ManagedCheck(6, failed, exception), new ManagedJump(7, new(8, []))]),
            new(8, [new ManagedAssignment(8, result, cast), new ManagedReturn(9, result)])]);
        var a = new Assertions();
        foreach (var condition in new[] { Cond.Eq, Cond.Ne })
        {
            var restored = SourceCheckedCasts.Rewrite(Body(condition));
            a.True(restored.Blocks[0].Statements is [ManagedJump { Edge.Target: 8 }], "正反 null 分支均折回汇合点");
            a.True(restored.Blocks[1].Statements is [ManagedJump], "重复检查与仅供检查使用的临时值一并消除");
            a.True(restored.Blocks[2].Statements[0] is ManagedAssignment { Value: CheckedCastValue { Operand: var operand, Target: var type } }
                && operand == source && type.Equals(target), "保留原引用与精确目标类型");
        }
        var baseline = Body();
        ManagedBody Path(params ManagedStatement[] prefix) => baseline with
        { Blocks = [baseline.Blocks[0], baseline.Blocks[1] with { Statements = [.. prefix, .. baseline.Blocks[1].Statements] }, baseline.Blocks[2]] };
        var effects = Path(new ManagedCall(3, new(exception, source, [], false), null, false));
        a.True(ReferenceEquals(effects, SourceCheckedCasts.Rewrite(effects)), "不越过有副作用的调用");
        var wrong = baseline with { Blocks = [baseline.Blocks[0], baseline.Blocks[1] with { Statements =
            [new ManagedAssignment(4, flag, matches), new ManagedCheck(5, failed with { Condition = Cond.Ne }, exception), new ManagedJump(7, new(8, []))] }, baseline.Blocks[2]] };
        a.True(ReferenceEquals(wrong, SourceCheckedCasts.Rewrite(wrong)), "匹配时抛出不能还原为 castclass");
        var escaped = baseline with { Blocks = [.. baseline.Blocks.Take(2), new(8, [new ManagedAssignment(8, result, cast), new ManagedReturn(9, flag)])] };
        a.True(ReferenceEquals(escaped, SourceCheckedCasts.Rewrite(escaped)), "外部使用的临时结果不能删除");
        var region = baseline with { Regions = [new([0, 4], 16, [16], null, ManagedRegionKind.Catch)] };
        a.True(ReferenceEquals(region, SourceCheckedCasts.Rewrite(region)), "不把类型异常移出原 try 区域");
        var sameRegion = baseline with { Regions = [new([0, 4, 8], 16, [16], null, ManagedRegionKind.Catch)] };
        a.True(SourceCheckedCasts.Rewrite(sameRegion).Blocks[2].Statements[0] is ManagedAssignment { Value: CheckedCastValue }, "同一 try 内保留异常归属");
        var extraEntry = baseline with { Blocks = [.. baseline.Blocks, new(12, [new ManagedJump(12, new(8, []))])] };
        a.True(ReferenceEquals(extraEntry, SourceCheckedCasts.Rewrite(extraEntry)), "未检查的第三个入口不能补上新的转换");
        var uncheckedPath = baseline with { Blocks = [baseline.Blocks[0], new(4, [new ManagedJump(7, new(8, []))]), baseline.Blocks[2]] };
        a.True(ReferenceEquals(uncheckedPath, SourceCheckedCasts.Rewrite(uncheckedPath)), "as 转换不能增加异常");
        return a.Finish("source-checked-casts");
    }
}
