using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceEntryDefaultsCheck
{
    [Command("source-entry-defaults", "入口清零不跨越读取、调用、回边或异常入口", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = 0, Assembly = "Sample", Namespace = "Tests", Name = "Owner", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var integer = new PrimitiveRef("I4");
        var structure = new DefinitionRef(new TypeDef { Index = 1, Assembly = "Sample", Namespace = "Tests", Name = "Value", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        var method = MethodRef.Open(new MethodDef { Index = 0, Owner = owner, Name = "Read", Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = integer });
        var scalar = new LocalValue(new(Storage.Temp(0), 1), integer, 32);
        var aggregate = new LocalValue(new(Storage.Temp(1), 1), structure, 0);
        var zero = new ManagedAssignment(1, scalar, new ConstantValue(0, integer, 32));
        var clear = new ManagedStore(2, new IndirectValue(new AddressValue(aggregate), structure), new ComposedValue(structure, []));
        var read = new ManagedReturn(3, scalar);
        ManagedBody Body(params ManagedBlock[] blocks) => new(method, blocks);
        var a = new Assertions();
        var baseline = Body(new(0, [new ManagedJump(0, new(1, []))]), new(1, [zero, clear, read]));
        a.Equal(2, SourceEntryDefaults.Find(baseline).Count, "直线入口的标量与整区零初始化由 InitLocals 承担");
        a.Equal(0, SourceEntryDefaults.Find(Body(new ManagedBlock(0, [zero, new ManagedJump(0, new(0, []))]))).Count,
            "方法入口有回边时清零不能消除");
        a.Equal(0, SourceEntryDefaults.Find(Body(new(0, [new ManagedJump(0, new(1, []))]), new(1, [zero, read]),
            new(2, [new ManagedJump(2, new(1, []))]))).Count, "多入边不沿用入口默认值");
        var call = new ManagedCall(0, new(method, null, [], false), null, false);
        a.Equal(0, SourceEntryDefaults.Find(Body(new ManagedBlock(0, [call, zero, read]))).Count, "不跨过可能观察局部地址的调用");
        var nonzero = zero with { Value = new ConstantValue(7, integer, 32) };
        a.Equal(0, SourceEntryDefaults.Find(Body(new ManagedBlock(0, [nonzero, zero, read]))).Count, "非零赋值后的重置必须保留");
        a.Equal(1, SourceEntryDefaults.Find(Body(new ManagedBlock(0, [zero, call, clear, read]))).Count, "仅消除调用前的前缀");
        var addressedParameter = clear with { Target = new IndirectValue(new ArgumentValue(0, new ByRefRef(structure), 64), structure) };
        a.Equal(0, SourceEntryDefaults.Find(Body(new ManagedBlock(0, [addressedParameter, read]))).Count, "外部地址清零具有副作用");
        var guarded = baseline with { Regions = [new ManagedRegion([0], 1, [1], null, ManagedRegionKind.Fault)] };
        a.Equal(0, SourceEntryDefaults.Find(guarded).Count, "异常入口不能当作唯一的正常入边");
        return a.Finish("source-entry-defaults");
    }
}
