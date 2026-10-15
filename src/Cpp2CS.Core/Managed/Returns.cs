using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Managed;

/// <summary>在 SSA 构建之前绑定方法自身的返回位置，不依赖参数布局是否已知。</summary>
public static class ManagedReturns
{
    public static void Bind(MachineFunction function, AbiValue? result)
    {
        if (result is { Passing: Passing.Stack } || result is { Pieces.Length: 0 })
            throw new InvalidOperationException("返回值没有可用的 ABI 位置");
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Return ret) continue;
                Expr? value = null, buffer = null;
                ReturnPiece[] pieces = [];
                if (result is { Passing: Passing.Indirect })
                {
                    var pointer = result.Pieces.Single();
                    // x8 是入口提供的地址，返回时该寄存器可能已被其他调用破坏。
                    buffer = new Use(new Variable(pointer.Register, 0), pointer.Width);
                }
                else if (result is { Pieces: [var single] }) value = new Read(single.Register, single.Width);
                else if (result is not null)
                    pieces = result.Pieces.Select(p => new ReturnPiece(p.Offset, new Read(p.Register, p.Width))).ToArray();
                block.Statements[i] = ret with { Value = value, Pieces = pieces, Buffer = buffer };
            }
    }
}
