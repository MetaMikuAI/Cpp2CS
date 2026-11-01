using System.Reflection;
using Cpp2CS.Ir;

namespace Cpp2CS.Facts;

/// <summary>经指针实参对被指内存的访问。</summary>
[Flags]
public enum MemoryAccess : byte { None = 0, Read = 1, Write = 2, ReadWrite = Read | Write }

/// <summary>托管值跨调用边界的方式。</summary>
public enum Transfer : byte
{
    /// <summary>值本身位于 Pieces（寄存器或栈槽）中。</summary>
    Value,
    /// <summary>Pieces[0] 是值副本的地址（大结构体、完全共享的类型参数）；被调用者只读这份副本。</summary>
    Copy,
    /// <summary>Pieces[0] 是调用者存储的地址（ref/out/in 参数、值类型的 this）。</summary>
    Reference,
    /// <summary>Pieces[0] 是结果缓冲区的地址；被调用者写入返回值。</summary>
    ResultBuffer,
}

/// <summary>
/// 一个 IL 值在机器上的位置。Index：-1 为 this，0.. 为参数，<see cref="MachineSignature.ReturnIndex"/> 为返回值。
/// Pieces 的 Register 为寄存器，或相对调用时 SP（被调用者入口 SP）的栈槽 <see cref="Storage.Slot"/>；
/// Piece.Offset 是该片在值中的字节偏移。Size 为值（或被指内存）的字节数，未知为 -1。
/// </summary>
public sealed record MachineValue(int Index, TypeRef Type, Transfer Transfer, AbiPiece[] Pieces, int Size, MemoryAccess Access)
{
    /// <summary>经指针传递时指针所在的位置。</summary>
    public AbiPiece? Pointer => Transfer == Transfer.Value ? null : Pieces[0];
}

/// <summary>托管方法的完整机器签名：寄存器与栈上的实参、返回值、隐藏的 MethodInfo，以及经指针实参的内存效果。</summary>
public sealed record MachineSignature(MachineValue[] Arguments, MachineValue? Return, AbiPiece? MethodInfo, int StackSize)
{
    public const int ReturnIndex = int.MaxValue;
    /// <summary>隐藏的 MethodInfo 实参在内存效果中的值编号。</summary>
    public const int MethodInfoIndex = int.MinValue;

    public MachineValue? This => Arguments.FirstOrDefault(a => a.Index == -1);

    /// <summary>调用读取或写出被指内存的全部值（含结果缓冲区）。</summary>
    public IEnumerable<MachineValue> Indirections => Return is { Transfer: Transfer.ResultBuffer } ret
        ? Arguments.Where(a => a.Transfer != Transfer.Value).Append(ret) : Arguments.Where(a => a.Transfer != Transfer.Value);
}

public sealed partial class ManagedAbi
{
    /// <summary>方法的机器签名；无法分类时返回 null 并给出原因。</summary>
    public MachineSignature? Machine(MethodRef method, out string? problem)
    {
        if (Classify(method, out problem) is not { } signature) return null;
        var stack = StackArguments(signature);
        var arguments = new List<MachineValue>();
        if (signature.This is { } self)
            arguments.Add(self.Type is ByRefRef byRef
                ? new(-1, self.Type, Transfer.Reference, self.Pieces, Size(byRef.Element), MemoryAccess.ReadWrite)
                : new(-1, self.Type, Transfer.Value, self.Pieces, 8, MemoryAccess.None));
        for (var i = 0; i < signature.Parameters.Length; i++)
        {
            var value = signature.Parameters[i];
            var attributes = method.Method.Parameters[i].Attributes;
            if (value.Passing == Passing.Stack)
            {
                var slot = stack.Parameters.Single(p => p.Index == i);
                if (slot.Indirect)
                    arguments.Add(new(i, value.Type, Transfer.Copy, [new AbiPiece(Storage.Slot(slot.Offset), 64, 0)], Size(value.Type), MemoryAccess.Read));
                else
                    arguments.Add(Direct(i, value.Type, StackPieces(slot) is { Length: > 0 } pieces ? pieces : [new AbiPiece(Storage.Slot(slot.Offset), slot.Size * 8, 0)], attributes));
                continue;
            }
            arguments.Add(value.Passing switch
            {
                Passing.Indirect => new(i, value.Type, Transfer.Copy, value.Pieces, Size(value.Type), MemoryAccess.Read),
                Passing.Shared => new(i, value.Type, Transfer.Copy, value.Pieces, -1, MemoryAccess.Read),
                _ => Direct(i, value.Type, value.Pieces, attributes),
            });
        }
        MachineValue? result = signature.Return switch
        {
            null => null,
            { Passing: Passing.Indirect } r => new(MachineSignature.ReturnIndex, r.Type, Transfer.ResultBuffer, r.Pieces, SharedValue(r.Type) ? -1 : Size(r.Type), MemoryAccess.Write),
            var r => new(MachineSignature.ReturnIndex, r.Type, Transfer.Value, r.Pieces, Size(r.Type), MemoryAccess.None),
        };
        var methodInfo = signature.MethodInfo ?? (stack.MethodInfoOffset is { } offset ? new AbiPiece(Storage.Slot(offset), 64, 0) : null);
        return new MachineSignature(arguments.ToArray(), result, methodInfo, stack.Size);
    }

    /// <summary>按值传递的实参；ref/out/in 参数是调用者存储的地址，按参数特性确定读写方向。</summary>
    private MachineValue Direct(int index, TypeRef type, AbiPiece[] pieces, ParameterAttributes attributes)
    {
        if (type is not ByRefRef byRef) return new(index, type, Transfer.Value, pieces, Size(type), MemoryAccess.None);
        var direction = attributes & (ParameterAttributes.In | ParameterAttributes.Out);
        var access = direction == ParameterAttributes.Out ? MemoryAccess.Write : direction == ParameterAttributes.In ? MemoryAccess.Read : MemoryAccess.ReadWrite;
        return new(index, type, Transfer.Reference, pieces, Size(byRef.Element), access);
    }
}
