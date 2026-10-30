
namespace Cpp2CS.Facts;

/// <summary>栈参数相对调用时 SP 的位置；Indirect 为大值类型副本的指针，而非值本身。</summary>
public sealed record StackAbiValue(int Index, TypeRef Type, int Offset, int Size, bool Indirect);
public sealed record StackAbiSignature(StackAbiValue[] Parameters, int? MethodInfoOffset, int Size);

public sealed partial class ManagedAbi
{
    public AbiPiece[] StackPieces(StackAbiValue value)
    {
        if (value.Indirect || Kind(value.Type) != ValueKind.Struct) return [];
        if (Hfa(value.Type) is { } hfa)
            return Enumerable.Range(0, hfa.Count).Select(i => new AbiPiece(Ir.Storage.Slot(value.Offset + i * hfa.Width / 8), hfa.Width, i * hfa.Width / 8)).ToArray();
        if (value.Size is <= 0 or > 16) return [];
        return Enumerable.Range(0, (value.Size + 7) / 8).Select(i => new AbiPiece(Ir.Storage.Slot(value.Offset + i * 8), Math.Min(8, value.Size - i * 8) * 8, i * 8)).ToArray();
    }

    /// <summary>
    /// 补齐既有 Stack 分类未表达的存储位置。AAPCS64 B.4 先把大非 HFA 值替换为指针，
    /// C.6/C.17 按至少 8 字节对齐分配栈槽；隐藏 MethodInfo 是最后一个指针参数。
    /// 寄存器分类仍由 Classify 提供；独立 AAPCS 分类器逐签名复核这些偏移。
    /// </summary>
    public StackAbiSignature StackArguments(AbiSignature signature)
    {
        var stack = 0;
        var parameters = new List<StackAbiValue>();
        static int Round(int n, int alignment) => checked((n + alignment - 1) / alignment * alignment);
        for (var i = 0; i < signature.Parameters.Length; i++)
        {
            var value = signature.Parameters[i];
            if (value.Passing != Passing.Stack) continue;
            var indirect = Kind(value.Type) == ValueKind.Struct && Size(value.Type) > 16 && Hfa(value.Type) is null;
            var shape = layouts.SizeAndAlignment(value.Type);
            var size = indirect ? 8 : shape.Size;
            var alignment = indirect ? 8 : Math.Max(8, shape.Alignment);
            stack = Round(stack, alignment);
            parameters.Add(new(i, value.Type, stack, size, indirect));
            stack += Round(size, 8);
        }
        int? methodInfo = null;
        if (signature.MethodInfo is null) { stack = Round(stack, 8); methodInfo = stack; stack += 8; }
        return new(parameters.ToArray(), methodInfo, stack);
    }
}
