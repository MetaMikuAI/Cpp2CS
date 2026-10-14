using Cpp2CS.IR;
using Cpp2CS.Model;

public static class BitsGraphChecks
{
    public static void Run(Action<bool, string> check)
    {
        Bits Deep(string identity)
        {
            Bits value = new InputBits(identity, 64);
            for (var i = 0; i < 4096; i++)
            {
                var joined = new ConcatBits(Sequence<Bits>.Of(new SliceBits(value, 0, 32), new SliceBits(value, 32, 32)), 64);
                value = new PhiBits("join:" + i, Sequence<Bits>.Of(joined, joined), 64);
            }
            return value;
        }
        var first = Deep("input"); var second = Deep("input"); var different = Deep("other");
        check(first.GetHashCode() == second.GetHashCode() && first == second, "4096 层共享位值图保持结构相等，遍历不展开成树");
        check(first != different, "深层叶值差异不能因共享形状而丢失");
        var lookup = new Dictionary<Bits, int> { [first] = 1 };
        check(lookup.TryGetValue(second, out var entry) && entry == 1 && !lookup.ContainsKey(different), "位值字典支持独立构造的等价图");
        var phi = (PhiBits)first;
        var copy = phi with { };
        check(copy == first && copy.GetHashCode() == first.GetHashCode(), "record 复制不改变结构身份");
        check((phi with { Block = "other" }) != first && (phi with { Width = 32 }) != first && (phi with { BitWidth = 32 }) != first,
            "已计算哈希后的 with 修改使用新节点身份");
        check((phi with { Incoming = Sequence<Bits>.Of(new InputBits("input", 64)) }) != first, "前驱数量和内容参与位值身份");
        var hashes = new int[64];
        Parallel.For(0, hashes.Length, i => hashes[i] = second.GetHashCode());
        check(hashes.All(h => h == first.GetHashCode()), "并行读取位值哈希不改变结果");
        var collisionA = new PhiBits("block", Sequence<Bits>.Of(new CollisionBits(1)), 64);
        var collisionB = new PhiBits("block", Sequence<Bits>.Of(new CollisionBits(2)), 64);
        check(collisionA.GetHashCode() == collisionB.GetHashCode() && collisionA != collisionB, "哈希碰撞仍检查完整结构，不能认定为同一个值");

        Bits[] leaves = [new InputBits("input", 64), new InputBits("input", 32), new InputBits("other", 64),
            new ConstantBits(1, 64), new ConstantBits(2, 64), new UnknownBits("input", "missing", 64), new UnknownBits("input", "other", 64)];
        var values = new List<Bits>(leaves);
        foreach (var left in leaves)
        foreach (var right in leaves)
        {
            values.Add(new ConcatBits(Sequence<Bits>.Of(left, right), left.Width + right.Width));
            values.Add(new PhiBits("block", Sequence<Bits>.Of(left, right), left.Width));
            values.Add(new PhiBits("other", Sequence<Bits>.Of(left, right), left.Width));
            values.Add(new SliceBits(new ConcatBits(Sequence<Bits>.Of(left, right), left.Width + right.Width), 8, 16));
        }
        var expected = values.Select(Text).ToArray();
        var equalPairs = 0;
        for (var i = 0; i < values.Count; i++)
        for (var j = 0; j < values.Count; j++)
        {
            var equal = values[i] == values[j];
            if (equal != (expected[i] == expected[j])) throw new InvalidOperationException($"位值结构对照失败：{i}/{j}");
            if (equal && values[i].GetHashCode() != values[j].GetHashCode()) throw new InvalidOperationException("相等位值的哈希不同");
            if (equal) equalPairs++;
        }
        check(equalPairs >= values.Count, $"{values.Count * values.Count} 对浅层位值与独立结构文本一致，保留类别、位宽、来源和输入顺序");
    }
    private sealed record CollisionBits(int Identity) : Bits(64)
    {
        public override int GetHashCode() => 0;
    }
    private static string Text(Bits value) => value.Width + ":" + (value switch
    {
        InputBits i => $"input:{i.Identity}:{i.BitWidth}",
        ConstantBits c => $"constant:{c.Value}:{c.BitWidth}",
        UnknownBits u => $"unknown:{u.Identity}:{u.Reason}:{u.BitWidth}",
        SliceBits s => $"slice:{s.Offset}:{s.BitWidth}({Text(s.Source)})",
        ConcatBits c => $"concat:{c.BitWidth}({string.Join(',', c.Parts.Select(Text))})",
        PhiBits p => $"phi:{p.Block}:{p.BitWidth}({string.Join(',', p.Incoming.Select(Text))})",
        _ => throw new InvalidOperationException("未支持的测试位值")
    });
}
