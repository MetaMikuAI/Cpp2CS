using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Facts;

/// <summary>值在寄存器中的一段：Register 的低 Width 位是值从 Offset 字节起的内容。</summary>
public sealed record AbiPiece(Storage Register, int Width, int Offset);

public enum Passing
{
    /// <summary>值本身在 Pieces 所列寄存器中。</summary>
    Registers,
    /// <summary>寄存器 Pieces[0] 中是值副本的地址（大结构参数；返回值时为 x8 指向的结果缓冲区）。</summary>
    Indirect,
    /// <summary>经栈传递。</summary>
    Stack,
}

public sealed record AbiValue(TypeRef Type, Passing Passing, AbiPiece[] Pieces);

/// <summary>托管方法在机器上的签名。This 为实例方法的接收者（值类型为指向数据的指针），Return 为 null 表示 void。</summary>
public sealed record AbiSignature(AbiValue? This, AbiValue[] Parameters, AbiPiece? MethodInfo, AbiValue? Return)
{
    public IEnumerable<AbiValue> Arguments => This is null ? Parameters : [This, .. Parameters];

    /// <summary>调用读取的寄存器：各参数的寄存器段、MethodInfo 寄存器；间接返回时加 x8。</summary>
    public Storage[] Reads => [.. Arguments.SelectMany(a => a.Pieces).Select(p => p.Register).Distinct(),
        .. MethodInfo is { } m ? [m.Register] : Array.Empty<Storage>(),
        .. Return is { Passing: Passing.Indirect } r ? [r.Pieces[0].Register] : Array.Empty<Storage>()];

    /// <summary>调用写出结果的寄存器（间接返回时没有）。</summary>
    public Storage[] Results => Return is { Passing: Passing.Registers } r ? r.Pieces.Select(p => p.Register).Distinct().ToArray() : [];
}

/// <summary>值的寄存器类别。</summary>
public enum ValueKind { Void, Integer, Reference, Float, Double, Struct }

/// <summary>
/// IL2CPP 托管方法的 AArch64 调用约定（AAPCS64）。IL2CPP 把托管方法生成为 C 函数：
/// (this, 参数..., const MethodInfo*)，值类型的 this 为指向数据的指针。
/// 整数/指针/引用依次占 x0–x7，float/double 依次占 v0–v7；HFA（1–4 个同类浮点成员）占连续 v 寄存器；
/// 其余不超过 16 字节的结构占 1–2 个 x 寄存器（不拆分到栈），更大的结构传副本地址；返回值同理，大结构经 x8 写回。
/// 大小与成员布局取自 <see cref="FieldLayouts"/>；含泛型参数或完全共享占位类型的签名无法分类（返回 null）。
/// </summary>
public sealed partial class ManagedAbi(FieldLayouts layouts)
{
    private const int Registers = 8;

    public ValueKind? Kind(TypeRef type)
    {
        switch (type)
        {
            case PrimitiveRef { Name: "void" }:
                return ValueKind.Void;
            case PointerRef or ByRefRef or ArrayRef:
                return ValueKind.Integer;
            case GenericParameterRef generic:
                return generic.IsReference ? ValueKind.Reference : null;
            case DefinitionRef d:
                if (FieldLayouts.IsFullyShared(d)) return null;
                var t = d.Definition;
                if (t.Assembly == "mscorlib.dll" && t.Namespace == "System" && t.DeclaringType is null)
                    switch (t.Name)
                    {
                        case "Void": return ValueKind.Void;
                        case "Single": return ValueKind.Float;
                        case "Double": return ValueKind.Double;
                    }
                if (!t.IsValueType) return ValueKind.Reference;
                if (t.IsEnum) return ValueKind.Integer;
                return PrimitiveOrStruct(d);
            default:
                return null;
        }
    }

    private ValueKind PrimitiveOrStruct(DefinitionRef d)
    {
        var t = d.Definition;
        return t.Assembly == "mscorlib.dll" && t.Namespace == "System" && t.DeclaringType is null
            && t.Name is "Boolean" or "SByte" or "Byte" or "Int16" or "UInt16" or "Char" or "Int32" or "UInt32" or "Int64" or "UInt64" or "IntPtr" or "UIntPtr"
            ? ValueKind.Integer : ValueKind.Struct;
    }

    /// <summary>值的字节数；无法确定为 -1。</summary>
    public int Size(TypeRef type)
    {
        try { return layouts.SizeAndAlignment(type).Size; }
        catch (Exception e) when (e is InvalidDataException or NotSupportedException) { return -1; }
    }

    /// <summary>值类型的实例字段（偏移相对值的起点，不含对象头）；没有布局为 null。</summary>
    public IReadOnlyList<(TypeRef Type, int Offset)>? Fields(DefinitionRef type) =>
        layouts.Of(type) is { } layout ? layout.Fields.Select(f => (f.Type, f.Offset - RuntimeLayout.ObjectHeaderSize)).ToList() : null;

    /// <summary>签名中的类型以 method 的实参代入。无法分类时返回 null 并给出原因。</summary>
    public AbiSignature? Classify(MethodRef method, out string? problem)
    {
        problem = null;
        var definition = method.Method;
        TypeRef Concrete(TypeRef type) => type.Substitute(method.TypeArguments, method.MethodArguments);
        int gpr = 0, vec = 0;
        AbiValue? self = null;
        if (!definition.IsStatic)
        {
            var owner = method.DeclaringType;
            self = new AbiValue(definition.Owner.IsValueType ? new ByRefRef(owner) : owner, Passing.Registers, [new AbiPiece(Storage.Gpr(gpr++), 64, 0)]);
        }
        var parameters = new AbiValue[definition.Parameters.Count];
        for (var i = 0; i < parameters.Length; i++)
        {
            var type = Concrete(definition.Parameters[i].Type);
            if (Argument(type, ref gpr, ref vec, out problem) is not { } value)
            {
                problem = $"参数 {definition.Parameters[i].Name}: {problem}";
                return null;
            }
            parameters[i] = value;
        }
        AbiPiece? methodInfo = gpr < Registers ? new AbiPiece(Storage.Gpr(gpr), 64, 0) : null;
        var result = ClassifyReturn(Concrete(definition.ReturnType), out problem);
        if (problem is not null)
        {
            problem = $"返回值: {problem}";
            return null;
        }
        return new AbiSignature(self, parameters, methodInfo, result);
    }

    private AbiValue? Argument(TypeRef type, ref int gpr, ref int vec, out string? problem)
    {
        problem = null;
        switch (Kind(type))
        {
            case null:
                problem = $"无法确定类别的类型 {type}";
                return null;
            case ValueKind.Float or ValueKind.Double:
                if (vec >= Registers) return new AbiValue(type, Passing.Stack, []);
                return new AbiValue(type, Passing.Registers, [new AbiPiece(Storage.Vec(vec++), Kind(type) == ValueKind.Float ? 32 : 64, 0)]);
            case ValueKind.Struct:
            {
                var size = Size(type);
                if (size <= 0)
                {
                    problem = $"大小未知的结构 {type}";
                    return null;
                }
                if (Hfa(type) is { } hfa)
                {
                    if (vec + hfa.Count > Registers)
                    {
                        vec = Registers;
                        return new AbiValue(type, Passing.Stack, []);
                    }
                    var pieces = new AbiPiece[hfa.Count];
                    for (var k = 0; k < hfa.Count; k++) pieces[k] = new AbiPiece(Storage.Vec(vec++), hfa.Width, k * hfa.Width / 8);
                    return new AbiValue(type, Passing.Registers, pieces);
                }
                if (size > 16)
                {
                    if (gpr >= Registers) return new AbiValue(type, Passing.Stack, []);
                    return new AbiValue(type, Passing.Indirect, [new AbiPiece(Storage.Gpr(gpr++), 64, 0)]);
                }
                var words = (size + 7) / 8;
                if (gpr + words > Registers)
                {
                    gpr = Registers;
                    return new AbiValue(type, Passing.Stack, []);
                }
                var parts = new AbiPiece[words];
                for (var k = 0; k < words; k++) parts[k] = new AbiPiece(Storage.Gpr(gpr++), Math.Min(64, (size - k * 8) * 8), k * 8);
                return new AbiValue(type, Passing.Registers, parts);
            }
            case ValueKind.Void:
                problem = "void 参数";
                return null;
            default:
                if (gpr >= Registers) return new AbiValue(type, Passing.Stack, []);
                return new AbiValue(type, Passing.Registers, [new AbiPiece(Storage.Gpr(gpr++), Math.Max(8, Size(type) * 8), 0)]);
        }
    }

    public AbiValue? ClassifyReturn(TypeRef type, out string? problem)
    {
        problem = null;
        switch (Kind(type))
        {
            case ValueKind.Void:
                return null;
            case null:
                problem = $"无法确定类别的类型 {type}";
                return null;
            case ValueKind.Float or ValueKind.Double:
                return new AbiValue(type, Passing.Registers, [new AbiPiece(Storage.Vec(0), Kind(type) == ValueKind.Float ? 32 : 64, 0)]);
            case ValueKind.Struct:
            {
                var size = Size(type);
                if (size <= 0)
                {
                    problem = $"大小未知的结构 {type}";
                    return null;
                }
                if (Hfa(type) is { } hfa)
                    return new AbiValue(type, Passing.Registers, Enumerable.Range(0, hfa.Count).Select(k => new AbiPiece(Storage.Vec(k), hfa.Width, k * hfa.Width / 8)).ToArray());
                if (size > 16) return new AbiValue(type, Passing.Indirect, [new AbiPiece(Storage.Gpr(8), 64, 0)]);
                return new AbiValue(type, Passing.Registers, Enumerable.Range(0, (size + 7) / 8)
                    .Select(k => new AbiPiece(Storage.Gpr(k), Math.Min(64, (size - k * 8) * 8), k * 8)).ToArray());
            }
            default:
                return new AbiValue(type, Passing.Registers, [new AbiPiece(Storage.Gpr(0), Math.Max(8, Size(type) * 8), 0)]);
        }
    }

    /// <summary>同质浮点聚合：展开后 1–4 个成员全为 float 或全为 double，且无空洞。</summary>
    private (int Count, int Width)? Hfa(TypeRef type)
    {
        var members = new List<ValueKind>();
        if (!Flatten(type, members) || members.Count is 0 or > 4) return null;
        if (members.Any(m => m != members[0])) return null;
        var width = members[0] == ValueKind.Float ? 32 : 64;
        return Size(type) == members.Count * width / 8 ? (members.Count, width) : null;
    }

    private bool Flatten(TypeRef type, List<ValueKind> members)
    {
        if (type is not DefinitionRef d || Fields(d) is not { } fields) return false;
        var offset = 0;
        foreach (var (fieldType, fieldOffset) in fields.OrderBy(f => f.Offset))
        {
            if (fieldOffset != offset) return false;
            var size = Size(fieldType);
            if (size <= 0) return false;
            offset += size;
            switch (Kind(fieldType))
            {
                case ValueKind.Float or ValueKind.Double:
                    members.Add(Kind(fieldType)!.Value);
                    break;
                case ValueKind.Struct:
                    if (!Flatten(fieldType, members)) return false;
                    break;
                default:
                    return false;
            }
            if (members.Count > 4) return false;
        }
        return offset == Size(type);
    }
}
