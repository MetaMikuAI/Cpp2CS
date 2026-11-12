using System.Collections.Immutable;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native.Terms;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Binding;

/// <summary>只绑定抽象槽位；不解析间接目标，不读取内存，不改变原生程序。</summary>
public sealed class MethodBinder(ManagedCSignatureBuilder signatures, IAbiClassifier classifier)
{
    public BindingResult<SignatureBinding> Entry(MethodRef method, BindingEntryKind kind)
        => Entry(new BindingEntry(method, kind));

    public BindingResult<SignatureBinding> Definition(MethodRef definition, BindingEntryKind kind, MethodRef? witness)
    {
        if (!GenericWitness.IsGeneric(definition.Method)) return Entry(definition, kind);
        if (witness is null || witness.Method != definition.Method || kind != BindingEntryKind.SharedGeneric
            || !GenericWitness.IsCanonical(witness) && !GenericWitness.IsValueInstance(witness))
            return BindingResult<SignatureBinding>.Fail(BindingFailureKind.SignatureUnavailable, "泛型定义缺少规范引用实例或封闭值类型实例见证");
        var result = Entry(witness, kind);
        return result.Value is { } binding ? new(binding with { Entry = new(definition, kind) }, null) : result;
    }

    public BindingResult<SignatureBinding> Entry(BindingEntry entry)
    {
        if (entry.Method is null)
            return BindingResult<SignatureBinding>.Fail(BindingFailureKind.SignatureUnavailable, "入口没有托管方法身份：" + entry.Detail);
        if (entry.Kind is not (BindingEntryKind.Ordinary or BindingEntryKind.SharedGeneric))
            return BindingResult<SignatureBinding>.Fail(BindingFailureKind.SignatureUnavailable, $"{entry.Kind} 需要专用 C 层签名见证：{entry.Detail}");
        var managed = signatures.Build(entry.Method, entry.Kind == BindingEntryKind.SharedGeneric);
        if (managed.Value is not { } signature)
            return BindingResult<SignatureBinding>.Fail(BindingFailureKind.SignatureUnavailable, managed.Problem!);
        var result = Classify(signature.Signature);
        return result.Value is { } value ? new(value with { Managed = signature, Entry = entry }, null) : result;
    }

    public BindingResult<SignatureBinding> Classify(CSignature signature)
    {
        var result = classifier.Classify(signature);
        return result.Assignment is { } slots ? new(new(signature, slots), null)
            : BindingResult<SignatureBinding>.Fail(BindingFailureKind.ClassificationFailed, result.Problem!);
    }

    /// <summary>index 是 C 形参序号；托管参数用 Managed.ParameterIndices，this 用 Managed.ThisIndex。</summary>
    public BindingResult<BoundValue> Parameter(SignatureBinding signature, int index, TermTable terms,
        IEnumerable<EntryInput> inputs, Term? incomingArgumentArea = null)
        => Value(signature.Signature.Parameters[index], signature.Slots.Parameters[index], terms,
            inputs.Select(i => new SlotValue(i.Slot, i.Value)).ToImmutableArray(), incomingArgumentArea);

    /// <summary>导入与间接调用的目标确定后直接传入方法或 C 层签名；这里不检查或猜测 Target。</summary>
    public BindingResult<BoundCall> Call(Call call, SignatureBinding signature, TermTable terms)
    {
        var arguments = ImmutableArray.CreateBuilder<BoundValue>();
        for (var i = 0; i < signature.Signature.Parameters.Length; i++)
        {
            var argument = Value(signature.Signature.Parameters[i], signature.Slots.Parameters[i], terms,
                call.Arguments, call.OutgoingArgumentArea);
            if (argument.Failure is { } failure) return new(null, failure);
            arguments.Add(argument.Value!);
        }
        var returned = Return(new Return(call.Results), signature, terms, call.Arguments, call.OutgoingArgumentArea);
        return returned.Failure is { } problem ? new(null, problem) : new(new(signature, arguments.ToImmutable(), returned.Value!), null);
    }

    public BindingResult<BoundCall> Call(Call call, MethodRef method, BindingEntryKind kind, TermTable terms)
    {
        var signature = Entry(method, kind);
        return signature.Value is { } value ? Call(call, value, terms) : new(null, signature.Failure);
    }

    public BindingResult<BoundCall> Call(Call call, CSignature signature, TermTable terms)
    {
        var classified = Classify(signature);
        return classified.Value is { } value ? Call(call, value, terms) : new(null, classified.Failure);
    }

    public CallCandidates Call(Call call, ImageFunction target, IBindingCodeMap map, TermTable terms)
    {
        var entries = map.At(target.EntryOffset);
        if (entries.Length == 0) return new([], new(BindingFailureKind.EntryNotMapped, "入口不在代码地图中"));
        var candidates = entries.Select(entry =>
        {
            var signature = Entry(entry);
            return new CandidateBinding(entry, signature.Value is { } value ? Call(call, value, terms) : new(null, signature.Failure));
        }).ToImmutableArray();
        return new(candidates, candidates.Length > 1
            ? new(BindingFailureKind.AmbiguousCandidates, $"入口对应 {candidates.Length} 个候选") : candidates[0].Binding.Failure);
    }

    /// <summary>间接结果缓冲区属于输入槽，须传入口/调用实参；返回终结本身没有缓冲区内容。</summary>
    public BindingResult<BoundValue> Return(Return statement, SignatureBinding signature, TermTable terms,
        ImmutableArray<SlotValue> inputs = default, Term? argumentArea = null)
    {
        var result = signature.Slots.Return;
        if (result.BufferAddress is { } address)
            return Value(signature.Signature.ReturnType, new([], address), terms,
                inputs.IsDefault ? [] : inputs, argumentArea);
        return Value(signature.Signature.ReturnType, new(result.Pieces), terms, statement.Results, null);
    }

    public BindingResult<BoundValue> Return(Return statement, CType type, TermTable terms,
        ImmutableArray<SlotValue> inputs = default, Term? argumentArea = null)
    {
        var signature = Classify(new([], type));
        return signature.Value is { } value ? Return(statement, value, terms, inputs, argumentArea) : new(null, signature.Failure);
    }

    private static BindingResult<BoundValue> Value(CType type, AbiValue assignment, TermTable terms,
        ImmutableArray<SlotValue> values, Term? area)
    {
        if (assignment.CopyAddress is { } pointer)
        {
            var address = Piece(pointer, terms, values, area);
            return address.Value is { } source ? new(new(type, new IndirectSource(source, type.Size), assignment.UnusedBits), null)
                : new(null, address.Failure);
        }
        if (type.Size == 0) return new(new(type, null, assignment.UnusedBits), null);
        var pieces = ImmutableArray.CreateBuilder<BoundPiece>();
        foreach (var piece in assignment.Pieces.OrderBy(p => p.ValueOffset))
        {
            var source = Piece(piece, terms, values, area);
            if (source.Failure is { } failure) return new(null, failure);
            pieces.Add(new(piece.ValueOffset, piece.Length, source.Value!));
        }
        // 分类器允许略去聚合填充；有值的字节不能用未定义项补齐。
        foreach (var leaf in CTypes.Leaves(type))
        {
            var end = leaf.Offset;
            foreach (var piece in pieces)
                if (piece.ValueOffset <= end && piece.ValueOffset + piece.Length > end) end = piece.ValueOffset + piece.Length;
            if (end < leaf.Offset + leaf.Type.Size)
                return BindingResult<BoundValue>.Fail(BindingFailureKind.ClassificationFailed, "分类片段未覆盖有值的字节");
        }
        if (pieces.Any(p => p.Source is not TermSource))
            return new(new(type, new PiecesSource(pieces.ToImmutable()), assignment.UnusedBits), null);
        var parts = new List<Term>();
        var cursor = 0;
        foreach (var piece in pieces)
        {
            if (piece.ValueOffset < cursor || piece.ValueOffset + piece.Length > type.Size)
                return BindingResult<BoundValue>.Fail(BindingFailureKind.ClassificationFailed, "分类片段重叠或越界");
            if (piece.ValueOffset > cursor) parts.Add(terms.Undefined((piece.ValueOffset - cursor) * 8));
            parts.Add(((TermSource)piece.Source).Term);
            cursor = piece.ValueOffset + piece.Length;
        }
        if (cursor < type.Size) parts.Add(terms.Undefined((type.Size - cursor) * 8));
        return new(new(type, new TermSource(terms.Concat(parts.ToArray())), assignment.UnusedBits), null);
    }

    private static BindingResult<BoundSource> Piece(AbiPiece piece, TermTable terms,
        ImmutableArray<SlotValue> values, Term? area)
    {
        if (piece.Slot.Kind == SlotKind.ArgumentArea)
            return area is null ? BindingResult<BoundSource>.Fail(BindingFailureKind.MissingSlot, "缺少栈实参区地址")
                : new(new StackSource(area, piece.Slot.Position + piece.SlotOffset, piece.Length), null);
        var value = values.FirstOrDefault(v => v.Slot == piece.Slot)?.Value;
        if (value is null || value.Width < (piece.SlotOffset + piece.Length) * 8)
            return BindingResult<BoundSource>.Fail(BindingFailureKind.MissingSlot, $"槽 {piece.Slot} 缺少所需的值或位宽");
        return new(new TermSource(terms.Slice(value, piece.SlotOffset * 8, piece.Length * 8)), null);
    }
}
