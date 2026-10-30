using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class FrameMemoryCheck
{
    [Command("frame-memory", "定长栈复制保留双向重叠、尾部字节及返回地址", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var displacement in new[] { -3, 0, 5 })
        {
            var source = new FrameAddress(-64);
            var target = new FrameAddress(source.Offset + displacement);
            var result = new Variable(Storage.Gpr(0), 1);
            var block = new Block(0x100) { Statements = [new Call(0x100, CallKind.Direct, Expr.C(0x200, 64))
            {
                Op = new(OpKind.Import, "memmove"), Arguments = [target, source, Expr.C(19, 64)], Defines = [result],
            }] };
            var function = new MachineFunction { Entry = block.Start, Range = new(0x100, 0x104, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block] };
            var next = 1;
            a.True(FrameMemoryNormalizer.Run(function, () => new(Storage.Temp(next++), 1)), "固定大小的栈复制被展开");
            Expr Lower(Expr e) => ExprMap.Map(e, p => p switch
            {
                FrameAddress frame => Expr.C(unchecked((ulong)(4096 + frame.Offset)), 64),
                Use use => new Read(use.Variable.Storage, use.Width),
                _ => null,
            });
            var statements = block.Statements.Select(s => s switch
            {
                Define define => (Stmt)new Assign(define.Address, define.Target.Storage, Lower(define.Value)),
                Store write => write with { Target = Lower(write.Target), Value = Lower(write.Value) },
                _ => s,
            }).ToArray();
            var evaluator = new Evaluator();
            evaluator.Run(statements, 0x100, 0x104);
            a.True(evaluator.Failure is null, "全部复制操作可求值");
            for (var i = 0; i < 19; i++)
                a.Equal(Evaluator.MemoryByte((ulong)(4096 + source.Offset + i)), evaluator.Written[(ulong)(4096 + target.Offset + i)], "复制使用写入前的源快照");
            a.Equal(19, evaluator.Written.Count, "不越过指定长度写入");
            a.Equal((UInt128)(ulong)(4096 + target.Offset), evaluator.Registers[Storage.Gpr(0)], "返回目标地址");
        }
        return a.Finish("frame-memory");
    }
}
