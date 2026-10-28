using Cpp2CS.Facts;
using Cpp2CS.Functions;

namespace Cpp2CS.Tests;

internal static class UnregisteredExceptionShapeCheck
{
    [Command("unregistered-exception-shape", "未注册入口异常表的地址归一与拒绝边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        CodeFunction Function(ulong start, ulong table, ulong slot) => new(start, start + 128, CodeRegion.Managed, BoundaryEvidence.EhFrame)
        {
            ExceptionRegions = [new(start, start + 40, start + 64)
            {
                ActionOffset = 3,
                Actions = [new(table, 1, -3, slot, "typed-catch"), new(table - 2, 0, 0, null, "cleanup")],
            }],
        };
        var first = Function(0x1000, 0x4000, 0x8000);
        var moved = Function(0x2000, 0x5000, 0x9000);
        string Shape(CodeFunction f) => UnregisteredMethods.ExceptionShape(f, slot => slot is 0x8000 or 0x9000 ? 0xa000UL : slot == 0x9008 ? 0xb000UL : null);
        var expected = Shape(first);
        a.Equal(expected, Shape(moved), "代码和动作表位置变化但区间与 RTTI 相同时同形");
        CodeFunction Region(Cpp2CS.Functions.ExceptionRegion region) => moved with { ExceptionRegions = [region] };
        var original = moved.ExceptionRegions.Single();
        foreach (var region in new[]
        {
            original with { End = original.End + 4 },
            original with { LandingPad = original.LandingPad + 4 },
            original with { Actions = [original.Actions[0] with { Filter = 2 }, original.Actions[1]] },
            original with { Actions = [original.Actions[0] with { TypeInfo = 0x9008 }, original.Actions[1]] },
            original with { Actions = [original.Actions[0] with { TypeInfo = 0x9010 }, original.Actions[1]] },
            original with { Actions = [original.Actions[0] with { Filter = -1 }, original.Actions[1]] },
            original with { Actions = [original.Actions[0] with { TypeInfo = 0, Kind = "catch-all" }, original.Actions[1]] },
            original with { Actions = [original.Actions[1] with { NextOffset = 2 }, original.Actions[0] with { NextOffset = 0 }] },
            original with { Actions = [original.Actions[0]] },
            original with { ActionOffset = 0 },
            original with { LandingPad = moved.End },
        }) a.True(Shape(Region(region)) != expected, "区间、处理器、筛选、顺序或类型变化以及未知/不完整信息不能误判同形");
        a.Equal(expected, Shape(Region(original with { ActionOffset = 10, Actions =
            [original.Actions[0] with { Address = 0x6010, NextOffset = 10 }, original.Actions[1] with { Address = 0x6020 }] })),
            "已解析动作链保留语义顺序，不依赖链在表中的物理布局");
        return a.Finish("unregistered-exception-shape");
    }
}
