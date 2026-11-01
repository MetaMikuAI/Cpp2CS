using System.Buffers.Binary;
using Cpp2CS.Facts;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>L5 的 ABI 入口；布局来自 L1，分配来自独立 AAPCS64 分类器，绝不以 L3 的分类布置原生实参。</summary>
[ShapeModel("结构体", Basis = "AAPCS64 第 6.8 节的参数与返回值分类（HFA、不超过 16 字节经通用寄存器、更大的按引用、x8 间接返回）；值类型布局取 L1 字段布局")]
internal sealed partial class StructAbi(WorldIndex index)
{
    public Aapcs64Classifier Classifier { get; } = new(index.Facts.Layouts);
    private readonly Dictionary<MethodRef, Aapcs64Classifier.Signature> checkedSignatures = new();

    public Aapcs64Classifier.Signature Signature(MethodRef method)
    {
        if (checkedSignatures.TryGetValue(method, out var cached)) return cached;
        Aapcs64Classifier.Signature native;
        try { native = Classifier.Classify(method); }
        catch (NotSupportedException e)
        {
            if (index.Abi.Classify(method, out _) is not null)
                throw new InvalidDataException($"对照器错误 ABI 单边分类：{method}：独立侧拒绝 {e.Message}");
            throw new Unsupported($"独立 ABI：{e.Message}");
        }
        var managed = index.Abi.Classify(method, out var problem)
            ?? throw new InvalidDataException($"对照器错误 ABI 单边分类：{method}：{problem}");
        void Check(AbiValue? a, Aapcs64Classifier.Location? b)
        {
            if (a is null && b is null) return;
            if (a is null || b is null) throw new InvalidDataException($"对照器错误 ABI 返回类别：{method}");
            var passing = b.StackOffset.HasValue ? Passing.Stack : b.Indirect ? Passing.Indirect : Passing.Registers;
            // 托管 ABI 表示不含完整栈槽和副本标志，此处核对传递类别与寄存器片。
            if (a.Passing != passing || !a.Pieces.Select(p => (p.Register, p.Width, p.Offset))
                .SequenceEqual(b.Pieces.Select(p => (p.Register, p.Width, p.Offset))))
                throw new InvalidDataException($"对照器错误 ABI 位置：{method}：{a} / {b}");
        }
        Check(managed.This, native.This);
        for (var i = 0; i < managed.Parameters.Length; i++) Check(managed.Parameters[i], native.Parameters[i]);
        Check(managed.Return, native.Return);
        if (managed.MethodInfo?.Register != native.MethodInfo.Pieces.FirstOrDefault()?.Register)
            throw new InvalidDataException($"对照器错误 ABI MethodInfo：{method}");
        var stack = index.Abi.StackArguments(managed);
        if (stack.MethodInfoOffset != native.MethodInfo.StackOffset || stack.Size != native.StackBytes
            || stack.Parameters.Any(p => p.Offset != native.Parameters[p.Index].StackOffset || p.Indirect != native.Parameters[p.Index].Indirect))
            throw new InvalidDataException($"对照器错误 ABI 栈布局：{method}");
        checkedSignatures.Add(method, native);
        return native;
    }

    public static TypeRef[] ArgumentTypes(MethodRef method) =>
        [.. method.Method.IsStatic ? Array.Empty<TypeRef>() : [method.Method.Owner.IsValueType ? new ByRefRef(method.DeclaringType) : method.DeclaringType],
         .. method.Method.Parameters.Select(p => p.Type.Substitute(method.TypeArguments, method.MethodArguments))];

    public static Aapcs64Classifier.Location[] Arguments(Aapcs64Classifier.Signature signature) =>
        signature.This is { } self ? [self, .. signature.Parameters] : signature.Parameters;

    public static ulong Bits(ReadOnlySpan<byte> bytes)
    {
        Span<byte> word = stackalloc byte[8];
        word.Clear();
        bytes.CopyTo(word);
        return BinaryPrimitives.ReadUInt64LittleEndian(word);
    }

    public static byte[] Bytes(ulong bits, int size)
    {
        var result = new byte[size];
        for (var i = 0; i < size; i++) result[i] = (byte)(bits >> (8 * i));
        return result;
    }

    /// <summary>ECMA-335 I.8.2.1：值由字段组成；AAPCS 片可能含未指定填充，调用/返回事件只记录叶子。</summary>
    public IEnumerable<ulong> ObservableArgument(Side side, TypeRef type, byte[] bytes)
    {
        if (type is ByRefRef b && Bits(bytes) is var address && side.ArgumentPointer(address) is var logical && logical != address)
        {
            yield return logical;
            var value = new byte[side.World.StorageSize(b.Element)];
            side.Read(address, value);
            foreach (var leaf in Observable(b.Element, value)) yield return leaf;
        }
        else foreach (var leaf in Observable(type, bytes)) yield return leaf;
    }

    public IEnumerable<ulong> Observable(TypeRef type, byte[] bytes) => Classifier.Leaves(type)
        .Select(l => Bits(bytes.AsSpan(l.Offset, l.Size)));
}
