using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class FrameInitializationCheck
{
    internal static void Run(Assertions a)
    {
        var type = new PrimitiveRef("I4");
        var leaf = new LocalValue(new Variable(Storage.Temp(-1), 1), type, 32);
        var other = leaf with { Variable = new Variable(Storage.Temp(-2), 1) };
        var one = new ConstantValue(1, type, 32);
        HashSet<ManagedValue> Under(ManagedValue v) => v == leaf || v == other ? [v] : [];
        ulong[] Check(ManagedBlock[] blocks, params ManagedRegion[] regions) =>
            FrameInitialization.Uninitialized(new ManagedBody(null!, blocks) { Regions = regions },
                new HashSet<ManagedValue> { leaf, other }, Under).ToArray();
        ManagedJump Jump(ulong to) => new(0, new(to, []));
        ManagedAssignment Write(LocalValue to) => new(0, to, one);
        ManagedReturn Read(ulong at, ManagedValue v) => new(at, v);
        ManagedCall Call(LocalValue result, params ManagedValue[] arguments) => new(5, new(null!, null, arguments, false), result, false);
        a.True(Check([new(0, [Call(leaf), Read(10, leaf)])]).Length == 0,
            "调用返回值在正常续接上定义帧叶子");
        a.True(Check([new(0, [Call(leaf, leaf), Read(10, leaf)])]).SequenceEqual(new ulong[] { 5 }),
            "调用结果不能证明本次调用的输入已经初始化");
        a.True(Check([new(0, [Call(leaf), Read(10, other)])]).SequenceEqual(new ulong[] { 10 }),
            "调用结果不初始化其他帧叶子");
        foreach (var kind in new[] { ManagedRegionKind.Catch, ManagedRegionKind.Fault })
        {
            var region = new ManagedRegion([0], 1, [1, 2], null, kind);
            a.True(Check([new(0, [Call(leaf), Read(10, leaf)]), new(1, [Read(11, leaf)])], region).SequenceEqual(new ulong[] { 11 }),
                $"{kind} 调用抛出时不存在返回值定义");
            a.True(Check([new(0, [Write(leaf), Read(10, one)]), new(1, [new ManagedAssignment(11, other, leaf), Jump(2)]), new(2, [Write(leaf), Jump(1)])], region).Contains(11UL),
                $"{kind} 首次异常进入不能用 handler 回边证明叶子初值");
            a.True(Check([new(0, [Read(10, one)]), new(1, [Write(leaf), Read(11, leaf)]), new(2, [Jump(1)])], region).Length == 0,
                $"{kind} 体内先定义再读取局部值");
            a.True(Check([new(0, [Write(leaf), Read(10, one)]), new(1, [Read(11, leaf)])], region).Contains(11UL),
                $"{kind} 不把 try 的正常出口状态用作异常边状态");
            a.True(Check([new(0, [Read(10, one)]), new(1, [Write(leaf), Read(11, other)])], region).Contains(11UL),
                $"{kind} 一个叶子初始化不能覆盖另一个叶子");
            a.True(Check([new(0, [Write(leaf), Jump(3)]), new(1, [Jump(3)]), new(3, [Read(13, leaf)])], region).Contains(13UL),
                $"{kind} 正常与异常续接合流要求所有路径定义");
            a.True(Check([new(0, [Write(leaf), Jump(3)]), new(1, [Write(leaf), Jump(3)]), new(3, [Read(13, leaf)])], region).Length == 0,
                $"{kind} 两条续接路径都定义时允许读取");
        }
    }
}
