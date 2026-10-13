using System.Collections.Immutable;
using System.Numerics;
using System.Text.Json.Serialization;

namespace Cpp2CS.Nir;

public readonly record struct NirValueId(int Id);
public readonly record struct NirBlockId(int Id);

[JsonPolymorphic(TypeDiscriminatorPropertyName = "kind")]
[JsonDerivedType(typeof(NirBitsType), "bits")]
[JsonDerivedType(typeof(NirEffectType), "effect")]
[JsonDerivedType(typeof(NirAddressType), "address")]
[JsonDerivedType(typeof(NirFunctionType), "function")]
public abstract record NirType;
public sealed record NirBitsType(int Width) : NirType;
public sealed record NirEffectType : NirType
{
    public static readonly NirEffectType Instance = new();
}
public sealed record NirAddressType(string Space, int Width) : NirType;
public sealed record NirFunctionType(NirSignature Signature, NirOutcomes Outcomes = NirOutcomes.Return | NirOutcomes.Fault | NirOutcomes.Diverge) : NirType;
public sealed record NirSignature(ImmutableArray<NirType> Parameters, ImmutableArray<NirType> Results);
public readonly record struct NirValue(NirValueId Id, NirType Type)
{
    public static NirValue Bits(int id, int width) => new(new(id), new NirBitsType(width));
    public static NirValue Effect(int id) => new(new(id), NirEffectType.Instance);
}
public sealed record NirEffectFlow(NirValue Input, NirValue Output);
public enum NirPureCode
{
    Add, Sub, Mul, And, Or, Xor, Not, Shl, Shr, Sar, UDiv, SDiv,
    Eq, Ult, Slt, Select, Zext, Sext, Extract, Concat, AddressAdd, AddressToBits, BitsToAddress
}
public enum NirByteOrder { Little, Big }

[JsonPolymorphic(TypeDiscriminatorPropertyName = "kind")]
[JsonDerivedType(typeof(NirDirectTarget), "direct")]
[JsonDerivedType(typeof(NirIndirectTarget), "indirect")]
public abstract record NirCallTarget;
public sealed record NirDirectTarget(string Function) : NirCallTarget;
public sealed record NirIndirectTarget(NirValue Function) : NirCallTarget;

[JsonPolymorphic(TypeDiscriminatorPropertyName = "kind")]
[JsonDerivedType(typeof(NirConstant), "constant")]
[JsonDerivedType(typeof(NirPure), "pure")]
[JsonDerivedType(typeof(NirFunctionConstant), "function")]
[JsonDerivedType(typeof(NirLoad), "load")]
[JsonDerivedType(typeof(NirStore), "store")]
[JsonDerivedType(typeof(NirLocalAlloc), "local-alloc")]
[JsonDerivedType(typeof(NirCall), "call")]
[JsonDerivedType(typeof(NirChoose), "choose")]
public abstract record NirOperation;
public sealed record NirConstant(NirValue Result, BigInteger Bits) : NirOperation;
public sealed record NirPure(NirValue Result, NirPureCode Code, ImmutableArray<NirValue> Inputs, int BitOffset = 0) : NirOperation;
public sealed record NirFunctionConstant(NirValue Result, string Function) : NirOperation;
// 内存失败沿函数的 Fault 出口传播；不产生正常结果或提交部分写入。
public sealed record NirLoad(NirValue Result, NirValue Address, NirByteOrder Order, NirEffectFlow Flow) : NirOperation;
public sealed record NirStore(NirValue Address, NirValue Value, NirByteOrder Order, NirEffectFlow Flow) : NirOperation;
public sealed record NirLocalAlloc(NirValue Result, NirValue Size, int Alignment, NirEffectFlow Flow) : NirOperation;
public sealed record NirCall(NirCallTarget Target, ImmutableArray<NirValue> Arguments,
    ImmutableArray<NirValue> Results, NirEffectFlow Flow) : NirOperation;
public sealed record NirChoose(NirValue Result, NirEffectFlow Flow) : NirOperation;

public sealed record NirEdge(NirBlockId Target, ImmutableArray<NirValue> Arguments);

[JsonPolymorphic(TypeDiscriminatorPropertyName = "kind")]
[JsonDerivedType(typeof(NirJump), "jump")]
[JsonDerivedType(typeof(NirBranch), "branch")]
[JsonDerivedType(typeof(NirReturn), "return")]
[JsonDerivedType(typeof(NirTailCall), "tail-call")]
[JsonDerivedType(typeof(NirNoReturnCall), "no-return-call")]
[JsonDerivedType(typeof(NirFault), "fault")]
[JsonDerivedType(typeof(NirTerminate), "terminate")]
public abstract record NirTerminator;
public sealed record NirJump(NirEdge Edge) : NirTerminator;
public sealed record NirBranch(NirValue Condition, NirEdge WhenTrue, NirEdge WhenFalse) : NirTerminator;
public sealed record NirReturn(ImmutableArray<NirValue> Values, NirValue Effect) : NirTerminator;
public sealed record NirTailCall(NirCallTarget Target, ImmutableArray<NirValue> Arguments, NirValue Effect) : NirTerminator;
public sealed record NirNoReturnCall(NirCallTarget Target, ImmutableArray<NirValue> Arguments, NirValue Effect) : NirTerminator;
public sealed record NirFault(string Code, NirValue Effect) : NirTerminator;
public sealed record NirTerminate(string Reason, NirValue Effect) : NirTerminator;
public sealed record NirBlock(NirBlockId Id, ImmutableArray<NirValue> Parameters,
    ImmutableArray<NirOperation> Operations, NirTerminator Terminator);

[Flags]
public enum NirOutcomes { None = 0, Return = 1, Fault = 2, Terminate = 4, Diverge = 8 }
[Flags]
public enum NirExternalEffects { None = 0, ReadMemory = 1, WriteMemory = 2, Environment = 4 }
public sealed record NirFunction(string Id, NirSignature Signature, NirBlockId Entry, ImmutableArray<NirBlock> Blocks)
{
    public ImmutableArray<NirBlockId> AdditionalEntries { get; init; } = [];
    public NirOutcomes Outcomes { get; init; } = NirOutcomes.Return | NirOutcomes.Fault | NirOutcomes.Diverge;
}
public sealed record NirExternalContract(string Id, NirSignature Signature, NirExternalEffects Effects, NirOutcomes Outcomes);
// 局部区间由显式分配合同给出；它不能与模块数据或另一个局部区间重叠。
public sealed record NirMemorySpace(string Id, int AddressWidth, BigInteger LocalBase, BigInteger LocalLength);
public sealed record NirDataObject(string Id, string Space, BigInteger Address, ImmutableArray<byte> Bytes, bool Writable);
public sealed record NirModule(ImmutableArray<NirFunction> Functions, ImmutableArray<NirExternalContract> Externals,
    ImmutableArray<NirMemorySpace> MemorySpaces, ImmutableArray<NirDataObject> DataObjects)
{
    public const string FormatVersion = "cpp2cs.nir/1";
    public string Version { get; init; } = FormatVersion;
}
public sealed record NirDiagnostic(string Code, string Message, string? Function = null, NirBlockId? Block = null, int? Operation = null);
public sealed record NirValidationResult(ImmutableArray<NirDiagnostic> Diagnostics)
{
    public bool IsValid => Diagnostics.Length == 0;
}
