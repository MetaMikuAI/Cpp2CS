using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceTryBlocksCheck
{
    [Command("source-try-blocks", "保护区局部运算合并及抛出、入口和嵌套边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = 0, Assembly = "Sample", Namespace = "", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodRef(new MethodDef { Index = 0, Owner = owner, Name = "Visit", Token = 0, Attributes = MethodAttributes.Public,
            ImplAttributes = 0, Slot = -1, ReturnType = new PrimitiveRef("Void") }, [], []);
        var integer = new PrimitiveRef("Int32");
        var local = new LocalValue(new(Storage.Temp(1), 1), integer, 32);
        var caught = new LocalValue(new(Storage.Temp(2), 1), new PrimitiveRef("Object"), 64);
        ManagedJump Jump(ulong from, ulong target) => new(from, new(target, []));
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "call", "divide", "external-entry", "entry-prefix", "handler", "nested-try", "nested-handler", "copies" })
        {
            ManagedStatement value = mode == "call" ? new ManagedCall(3, new(method, null, [], false), local, false)
                : new ManagedAssignment(3, local, new BinaryValue(mode == "divide" ? BinOp.SDiv : BinOp.Or,
                    local, new ConstantValue(2, integer, 32), integer, 32));
            var body = new ManagedBody(method, [new(0, [mode == "external-entry"
                ? new ManagedBranch(0, local, new(1, []), new(3, [])) : Jump(0, mode == "entry-prefix" ? 3UL : 1UL)]),
                new(1, [new ManagedCall(1, new(method, null, [], false), local, false), Jump(1, 3)]),
                new(2, [new ManagedRethrow(2)]), new(3, [value, mode == "copies"
                    ? new ManagedJump(3, new(1, [new(local, new ConstantValue(1, integer, 32))])) : Jump(3, 1)]),
                new(4, [new ManagedReturn(4, null)])])
                { Regions = [new([1], 2, mode == "handler" ? [2, 3] : [2], caught, ManagedRegionKind.Catch)] };
            if (mode == "nested-try") body = body with { Regions = [.. body.Regions, new([3], 4, [4], caught, ManagedRegionKind.Catch)] };
            if (mode == "nested-handler") body = body with { Regions = [.. body.Regions, new([4], 3, [3], caught, ManagedRegionKind.Catch)] };
            var result = SourceTryBlocks.Rewrite(body);
            var expected = mode is "valid" or "copies" or "entry-prefix";
            a.Equal(expected, result.Regions[0].Try.Contains(3UL), $"{mode} 的区域边界");
            a.Equal(body.Blocks.Single(b => b.Address == 3), result.Blocks.Single(b => b.Address == 3), "语句和边复制原样保留");
            a.Equal(1, body.Regions[0].Try.Count, "输入区域不变");
            if (expected) a.True(result.Blocks.Select(b => b.Address).SequenceEqual(mode == "entry-prefix"
                ? new ulong[] { 0, 3, 1, 2, 4 } : new ulong[] { 0, 1, 3, 2, 4 }), "合并后保护区连续且保留唯一入口");
        }
        return a.Finish("source-try-blocks");
    }
}
