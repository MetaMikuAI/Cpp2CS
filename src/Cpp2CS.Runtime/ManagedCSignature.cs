using System.Collections.Immutable;
using Cpp2CS.Model;
using Cpp2CS.Native.Abi;

namespace Cpp2CS.Runtime;

/// <summary>托管参数序号到 C 形参序号的映射；this 与方法信息不混入托管参数序号。</summary>
public sealed record ManagedCSignature(CSignature Signature, int? ThisIndex,
    ImmutableArray<int> ParameterIndices, int MethodInformationIndex);
public sealed record ManagedSignatureResult(ManagedCSignature? Value, string? Problem);

/// <summary>il2cpp 普通入口与封闭规范实例入口的签名推导；布局由调用方提供，ABI 分类另行执行。</summary>
public sealed class ManagedCSignatureBuilder(ITypeLayouts layouts, int pointerBits = 64)
{
    public ManagedSignatureResult Build(MethodRef method, bool sharedCode = false)
    {
        if (method.TypeArguments.Concat(method.MethodArguments).Any(FullyShared))
            return new(null, "完全共享实例的签名尚未支持");
        if (pointerBits != 64) return new(null, "当前只支持 64 位数据模型");
        if (!IsClosed(method))
            return new(null, "泛型实参未完整封闭");
        var parameters = ImmutableArray.CreateBuilder<CType>();
        int? self = method.Method.IsStatic ? null : 0;
        if (self is not null) parameters.Add(new CPointer(pointerBits));
        var indices = ImmutableArray.CreateBuilder<int>();
        foreach (var parameter in method.Method.Parameters)
        {
            var type = Describe(method.Concrete(parameter.Type), [], out var why);
            if (type is null) return new(null, $"参数 {indices.Count}：{why}");
            if (type is CVoid) return new(null, $"参数 {indices.Count}：void 参数");
            indices.Add(parameters.Count);
            parameters.Add(type);
        }
        var result = Describe(method.Concrete(method.Method.ReturnType), [], out var problem);
        if (result is null) return new(null, "返回值：" + problem);
        var information = parameters.Count;
        parameters.Add(new CPointer(pointerBits));
        var signature = new CSignature(parameters.ToImmutable(), result);
        if (CTypes.Validate(signature) is { } invalid) return new(null, invalid);
        return new(new(signature, self, indices.ToImmutable(), information), null);
    }

    public static bool IsClosed(MethodRef method) =>
        method.TypeArguments.Count == method.Method.Owner.GenericParameters.Count
        && method.MethodArguments.Count == method.Method.GenericParameters.Count
        && method.TypeArguments.Concat(method.MethodArguments).All(Closed);

    private static bool Closed(TypeRef type) => type switch
    {
        GenericParameterRef => false,
        DefinitionRef d => d.Arguments.Count == d.Definition.GenericParameters.Count && d.Arguments.All(Closed),
        ArrayRef a => Closed(a.Element),
        PointerRef p => Closed(p.Element),
        ByRefRef r => Closed(r.Element),
        _ => true,
    };

    private static bool FullyShared(TypeRef type) => type switch
    {
        DefinitionRef d => (d.Definition.Namespace == "Unity.IL2CPP.Metadata"
            && d.Definition.Name is "__Il2CppFullySharedGenericType" or "__Il2CppFullySharedGenericStructType")
            || d.Arguments.Any(FullyShared),
        ArrayRef a => FullyShared(a.Element),
        PointerRef p => FullyShared(p.Element),
        ByRefRef r => FullyShared(r.Element),
        _ => false,
    };

    private CType? Describe(TypeRef type, HashSet<TypeRef> active, out string? problem)
    {
        problem = null;
        if (type.ContainsGenericParameter()) { problem = "开放泛型类型"; return null; }
        if (ManagedTypes.IsVoid(type)) return new CVoid();
        if (type is ByRefRef or PointerRef or ArrayRef || ManagedTypes.IsReferenceType(type)) return new CPointer(pointerBits);
        var primitive = ManagedTypes.PrimitiveName(type);
        if (primitive is "IntPtr" or "UIntPtr") return new CPointer(pointerBits);
        if (primitive is "Single" or "Double") return new CFloat(primitive == "Single" ? 32 : 64);
        var bits = primitive switch
        {
            "Boolean" or "Byte" or "SByte" => 8,
            "Char" or "Int16" or "UInt16" => 16,
            "Int32" or "UInt32" => 32,
            "Int64" or "UInt64" => 64,
            _ => 0,
        };
        if (bits != 0) return new CInteger(bits);
        if (type is not DefinitionRef definition) { problem = "未知的生成器类型映射"; return null; }
        if (!active.Add(type)) { problem = "递归值类型布局"; return null; }
        if (definition.Definition.IsEnum)
        {
            var fields = definition.Definition.Fields.Where(f => !f.IsStatic).ToArray();
            if (fields.Length != 1) { problem = "枚举底层字段不唯一"; return null; }
            var scalar = Describe(fields[0].Type.Substitute(definition.Arguments, []), active, out problem);
            active.Remove(type);
            return scalar;
        }
        if (layouts.Of(definition) is not { } layout) { problem = "缺少值类型布局"; return null; }
        var members = ImmutableArray.CreateBuilder<CField>();
        foreach (var field in layout.Fields)
        {
            var member = Describe(field.Type, active, out problem);
            if (member is null) return null;
            members.Add(new(field.Offset - layout.ObjectHeaderSize, member));
        }
        active.Remove(type);
        // 生成器给显式大小的值类型（包括没有实例字段、大小为 1 的空结构体）加一个覆盖整个值的字节数组，
        // 它与字段放在同一个联合里并参与 ABI 分类。
        var explicitSize = definition.Definition.ClassSizeIsDefault != true;
        if (members.Count == 0)
        {
            if (!explicitSize || layout.ValueSize <= 0) { problem = "没有成员也没有显式大小的值类型"; return null; }
            members.Add(new(0, new CArray(new CInteger(8), layout.ValueSize)));
        }
        else if (definition.Definition.ClassSizeIsDefault == false)
        {
            problem = "显式大小的值类型带有与字段重叠的填充数组，联合的分类尚未支持";
            return null;
        }
        return new CAggregate(layout.ValueSize, layout.MinimumAlignment, members.ToImmutable());
    }
}
