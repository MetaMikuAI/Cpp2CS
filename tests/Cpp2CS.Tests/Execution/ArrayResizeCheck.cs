using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

internal static class ArrayResizeCheck
{
    [Command("array-resize", "对照 CLR 验证数组扩缩、身份和前缀保留", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var world = new World(new WorldIndex(facts, types), 0, new Hints([], []), null);
        var definition = types.Corlib("System.Array").Definition.Methods.Single(m => m.Name == "Resize" && m.GenericParameters.Count == 1);
        var a = new Assertions();
        foreach (var reference in new[] { false, true })
        foreach (var oldLength in new[] { -1, 0, 2 })
        foreach (var length in new[] { 0, 1, 2, 4 })
        {
            var side = new CilSide(world);
            world.Active = side;
            var element = reference ? types.Object : types.UInt64;
            var arrayType = new ArrayRef(element, 1);
            var original = oldLength < 0 ? 0 : side.NewArray(arrayType, oldLength);
            var item = reference ? world.String("item") : 0x123456789abcdef0UL;
            for (var i = 0; i < oldLength; i++) side.WriteValue(original + (ulong)(RuntimeLayout.ArrayData + i * 8), item, 8);
            var slot = World.StackBase + 0x200;
            side.WriteValue(slot, original, 8);
            var method = new MethodRef(definition, [], [element]);
            world.Index.StructAbi.WriteBack(side, method, 0, [StructAbi.Bytes(slot, 8), StructAbi.Bytes((ulong)length, 4)]);
            var result = side.Read64(slot);
            a.Equal((ulong)length, side.Read64(result + RuntimeLayout.ArrayMaxLength), "写回扩缩后的长度");
            bool same;
            ulong[] expected;
            if (reference)
            {
                object marker = new();
                object[]? values = oldLength < 0 ? null : Enumerable.Repeat(marker, oldLength).ToArray();
                var before = values;
                Array.Resize(ref values, length);
                same = ReferenceEquals(before, values);
                expected = values.Select(v => ReferenceEquals(v, marker) ? item : 0UL).ToArray();
            }
            else
            {
                ulong[]? values = oldLength < 0 ? null : Enumerable.Repeat(item, oldLength).ToArray();
                var before = values;
                Array.Resize(ref values, length);
                same = ReferenceEquals(before, values);
                expected = values;
            }
            a.Equal(same, original == result, "数组身份与 CLR 一致");
            a.True(expected.Select((value, i) => side.Read64(result + (ulong)(RuntimeLayout.ArrayData + i * 8)) == value).All(equal => equal), "保留旧前缀并清零新增元素");
        }
        return a.Finish("array-resize");
    }
}
