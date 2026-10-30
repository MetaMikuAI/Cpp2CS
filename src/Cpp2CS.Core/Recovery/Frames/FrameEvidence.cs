using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed record CopyRange(TypeRef Type, ManagedValue Root, int Offset);

internal sealed record FrameCopy(Define Load, Store Store, CopyRange Source, CopyRange Target, Fragment Snapshot);

internal sealed record FrameRegion(long Offset, TypeRef Type, int Size, LocalValue Local);

internal sealed record FrameWitness(long Offset, TypeRef Type, Stmt Call, bool Writes);

// 只在 L3 内使用的地址见证；保留区域身份，后续栈着色不会把两个局部变量混为一体。
internal sealed record TypedFrame(FrameRegion Region) : Expr(64);

internal sealed record StackEnum(DefinitionRef Type, Expr Value, long Offset, Store[] Stores);
