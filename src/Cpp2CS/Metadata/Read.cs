using System.Globalization;
using Mono.Cecil;

namespace Cpp2CS.Metadata;

public static class Read
{
    static string? Attribute(Mono.Cecil.ICustomAttributeProvider item, string name, string field) =>
        item.CustomAttributes.SingleOrDefault(a => a.AttributeType.Name == name)?.Fields
            .Single(f => f.Name == field).Argument.Value?.ToString();

    public static string NativeName(string fullName) => fullName.Replace('.', '_').Replace('/', '_') + "_o";

    public static Catalog Load(string directory, CaseSpec spec)
    {
        using var assembly = AssemblyDefinition.ReadAssembly(Path.Combine(directory, spec.Assembly));
        var module = assembly.MainModule;
        var enums = new Dictionary<string, EnumModel>();
        string Type(TypeReference reference)
        {
            var type = module.GetType(reference.FullName);
            if (type?.IsEnum == true)
            {
                if (type.Fields.Single(f => f.Name == "value__").FieldType.FullName != "System.Int32")
                    throw new NotSupportedException($"枚举底层类型尚未支持: {type.FullName}");
                enums.TryAdd(type.FullName, new(type.FullName, type.Fields.Where(f => f.IsLiteral)
                    .ToDictionary(f => f.Name, f => Convert.ToInt64(f.Constant, CultureInfo.InvariantCulture))));
            }
            return reference.FullName;
        }
        string Native(TypeReference reference)
        {
            var name = reference.FullName;
            return name switch
            {
                "System.Void" => "void", "System.Boolean" => "bool", "System.SByte" => "int8_t",
                "System.Byte" => "uint8_t", "System.Int16" => "int16_t", "System.UInt16" => "uint16_t",
                "System.Int32" => "int32_t", "System.UInt32" => "uint32_t",
                "System.Int64" => "int64_t", "System.UInt64" => "uint64_t",
                "System.Single" => "float", "System.Double" => "double",
                _ when module.GetType(name)?.IsEnum == true => "int32_t",
                _ when module.GetType(name)?.IsValueType == true => NativeName(name),
                _ => NativeName(name) + " *"
            };
        }
        var types = spec.Types.Select(name =>
        {
            var type = module.GetType(name) ?? throw new InvalidOperationException($"元数据缺少类型 {name}");
            if (type.HasGenericParameters || (type.BaseType?.FullName is not ("System.Object" or "System.ValueType")))
                throw new NotSupportedException($"类型继承尚未支持: {name}");
            var fields = type.Fields.Where(f => !f.IsStatic).Select(f => new Field(f.Name, Type(f.FieldType),
                Convert.ToInt32(Attribute(f, "FieldOffsetAttribute", "Offset") ?? throw new InvalidOperationException(f.FullName), 16),
                f.IsInitOnly, f.IsPublic)).ToArray();
            var methods = type.Methods.Select(m =>
            {
                if (!m.IsPublic || m.HasGenericParameters || m.IsVirtual)
                    throw new NotSupportedException($"方法声明尚未支持: {m.FullName}");
                var address = Attribute(m, "AddressAttribute", "RVA") ?? throw new InvalidOperationException($"方法没有地址: {m.FullName}");
                var parameters = m.Parameters.Select(p => new Parameter(p.Name, Type(p.ParameterType),
                    p.HasConstant ? Convert.ToString(p.Constant, CultureInfo.InvariantCulture) : null)).ToArray();
                var nativeArgs = new List<string>();
                if (!m.IsStatic) nativeArgs.Add($"{NativeName(name)} *self");
                nativeArgs.AddRange(m.Parameters.Select((p, i) => $"{Native(p.ParameterType)} arg{i}"));
                nativeArgs.Add("const MethodInfo *method");
                var property = type.Properties.SingleOrDefault(p => p.GetMethod == m || p.SetMethod == m)?.Name;
                return new Method(m.Name, Attribute(m, "TokenAttribute", "Token")!, address.ToLowerInvariant(),
                    Type(m.ReturnType), m.IsStatic, property, parameters,
                    $"{Native(m.ReturnType)} __fastcall recovered({string.Join(", ", nativeArgs)});");
            }).ToArray();
            return new TypeModel(name, NativeName(name), type.IsValueType, type.IsSealed, fields, methods);
        }).ToArray();
        using var core = AssemblyDefinition.ReadAssembly(Path.Combine(directory, "mscorlib.dll"));
        var objectCtor = core.MainModule.GetType("System.Object").Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        var objectAddress = Attribute(objectCtor, "AddressAttribute", "RVA") ?? throw new InvalidOperationException("Object 构造地址缺失");
        return new(spec.BinarySha256, spec.Assembly, objectAddress.ToLowerInvariant(), types, enums.Values.ToArray());
    }
}
