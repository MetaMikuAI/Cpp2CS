using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery;

// 只在 L3 内存活；必须在写出前拆回叶子，不能把引用叶子转成整数或让填充成为托管值。
internal sealed record Part(int Low, ManagedValue Value);

internal sealed record Fragment(IReadOnlyList<Part> Parts, TypeRef Type, int Width) : ManagedValue(Type, Width);

/// <summary>一组按 ABI 片汇合的寄存器 φ：整体是一个结构体局部变量，每条入边整体赋值一次。</summary>
internal sealed record StructPhi(LocalValue Local, TypeRef Type, Block Block, Func<int, ManagedValue> Incoming);

internal sealed record AggregatePiece(ManagedValue Root, int Offset, int Width) : ManagedValue(Root.Type, Width);
