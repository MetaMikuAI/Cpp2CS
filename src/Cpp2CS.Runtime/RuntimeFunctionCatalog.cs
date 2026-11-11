using System.Collections.Frozen;
using System.Collections.Immutable;
using System.Text.Json;
using Cpp2CS.Native.Abi;

namespace Cpp2CS.Runtime;

public sealed record RuntimeRecognition(bool Symbol, string? Export, string? CallGraph, string? ReferenceShape, string? Import = null);
public sealed record RuntimeDeclarationSource(string File, int Line);
public sealed record RuntimeFunction(
    string Name, string MangledName, string Declaration, RuntimeDeclarationSource DeclarationSource,
    CSignature? Signature, ImmutableArray<string> Unsupported, bool DeclaredNoReturn,
    RuntimeOperation Operation, ImmutableArray<string> Arguments, string ResultBinding,
    ImmutableArray<string> ParameterTypes, string ResultType,
    ImmutableArray<string> Basis, RuntimeRecognition Recognition)
{
    public CSignature RequireSignature() => Signature ?? throw new NotSupportedException(
        $"运行时原型 {MangledName} 不可表示：{string.Join('；', Unsupported)}");
}

/// <summary>按精确 Unity 版本与目标读取；不做符号之外的识别，也不跨版本回退。</summary>
public sealed class RuntimeFunctionCatalog
{
    private RuntimeFunctionCatalog(string source, string unityVersion, string triple, string dataModel, ImmutableArray<RuntimeFunction> functions)
    {
        Source = source; UnityVersion = unityVersion; Triple = triple; DataModel = dataModel; Functions = functions;
        byMangled = functions.ToFrozenDictionary(f => f.MangledName, StringComparer.Ordinal);
        byName = functions.GroupBy(f => f.Name, StringComparer.Ordinal).ToFrozenDictionary(g => g.Key, g => g.ToImmutableArray(), StringComparer.Ordinal);
    }
    private readonly FrozenDictionary<string, RuntimeFunction> byMangled;
    private readonly FrozenDictionary<string, ImmutableArray<RuntimeFunction>> byName;
    public string Source { get; }
    public string UnityVersion { get; }
    public string Triple { get; }
    public string DataModel { get; }
    public ImmutableArray<RuntimeFunction> Functions { get; }
    // 名称可能重载；保留候选集，不任取第一项。
    public ImmutableArray<RuntimeFunction> ByName(string name) => byName.TryGetValue(name, out var result) ? result :
        throw new KeyNotFoundException($"{Source}：没有运行时函数名称 {name}");
    public RuntimeFunction ByMangledName(string name) => byMangled.TryGetValue(name, out var result) ? result :
        throw new KeyNotFoundException($"{Source}：没有运行时函数修饰名 {name}");

    public static RuntimeFunctionCatalog Load(string path, string unityVersion, string triple, string dataModel)
    {
        using var stream = File.OpenRead(path);
        return Read(stream, path, unityVersion, triple, dataModel);
    }
    public static RuntimeFunctionCatalog LoadWithSystem(string path, string systemPath, string unityVersion, string triple, string dataModel)
    {
        var runtime = Load(path, unityVersion, triple, dataModel);
        using var document = JsonDocument.Parse(File.ReadAllText(systemPath));
        var root = document.RootElement;
        if (root.GetProperty("schema_version").GetInt32() != 1 || Text(root, "libc") != "bionic" ||
            Text(root, "data_model") != dataModel || !Strings(root, "targets").Contains(triple))
            throw new InvalidDataException($"{systemPath}：系统目录不匹配目标与 C 库");
        var system = root.GetProperty("functions").EnumerateArray().Select(f => Parse(f, systemPath)).ToImmutableArray();
        if (system.Any(f => f.Recognition.Import != f.MangledName))
            throw new InvalidDataException($"{systemPath}：系统目录缺少精确导入名");
        var functions = runtime.Functions.AddRange(system);
        if (functions.Select(f => f.MangledName).Distinct(StringComparer.Ordinal).Count() != functions.Length)
            throw new InvalidDataException($"{systemPath}：系统与运行时目录符号冲突");
        return new(path, unityVersion, triple, dataModel, functions);
    }
    public static RuntimeFunctionCatalog Read(Stream stream, string source, string unityVersion, string triple, string dataModel)
    {
        using var document = JsonDocument.Parse(stream);
        var root = document.RootElement;
        if (!root.TryGetProperty("schema_version", out var version) || version.ValueKind != JsonValueKind.Number || !version.TryGetInt32(out var number) || number != 1)
            throw new InvalidDataException($"{source}：未知目录 schema_version");
        var target = root.GetProperty("target");
        if (Text(root, "unity_version") != unityVersion || Text(target, "triple") != triple || Text(target, "data_model") != dataModel)
            throw new InvalidDataException($"{source}：目录不匹配 Unity={unityVersion}, target={triple}, data_model={dataModel}");
        var functions = root.GetProperty("functions").EnumerateArray().Select(f => Parse(f, source)).ToImmutableArray();
        if (functions.Length == 0 || functions.Select(f => f.MangledName).Distinct(StringComparer.Ordinal).Count() != functions.Length)
            throw new InvalidDataException($"{source}：目录为空或修饰名重复");
        return new(source, unityVersion, triple, dataModel, functions);
    }

    private static RuntimeFunction Parse(JsonElement f, string source)
    {
        var name = Text(f, "name");
        var prototype = f.GetProperty("prototype");
        var parameters = prototype.GetProperty("parameters").EnumerateArray().ToArray();
        var unsupported = Strings(f, "unsupported");
        var op = RuntimeOperations.Get(Text(f, "operation"));
        var args = Strings(f, "arguments");
        var types = Strings(f, "parameter_types");
        if (args.Length != parameters.Length || types.Length != parameters.Length || args.Length != op.Inputs.Length ||
            args.Distinct(StringComparer.Ordinal).Count() != args.Length || args.Any(a => !op.Inputs.Any(i => i.Name == a)))
            throw new InvalidDataException($"{source}：{name} 实参映射必须覆盖全部操作输入并与原型形参数量一致");
        var result = Text(f, "result");
        if (result is not ("operation" or "discard" or "void") ||
            (result == "void") != (op.Result.Kind == RuntimeValueKind.Void))
            throw new InvalidDataException($"{source}：{name} 的结果映射不合法");
        var hasUnsupported = parameters.Append(prototype.GetProperty("result")).Any(t => Text(t, "kind") == "unsupported");
        if (hasUnsupported != (unsupported.Length != 0))
            throw new InvalidDataException($"{source}：{name} 的不支持类型诊断与原型不一致");
        CSignature? signature = null;
        if (!hasUnsupported)
        {
            signature = new(parameters.Select(Type).ToImmutableArray(), Type(prototype.GetProperty("result")), prototype.GetProperty("variadic").GetBoolean());
            if (CTypes.Validate(signature) is { } why) throw new InvalidDataException($"{source}：{name}：{why}");
            if ((result is "void" or "discard") != (signature.ReturnType is CVoid))
                throw new InvalidDataException($"{source}：{name} 的 C 返回值与结果映射不一致");
            for (var index = 0; index < args.Length; index++)
            {
                var input = op.Inputs.Single(i => i.Name == args[index]);
                var scalar = input.Kind is RuntimeValueKind.Integer or RuntimeValueKind.Boolean && input.Use == RuntimeInputUse.Value;
                if (scalar ? signature.Parameters[index] is not CInteger : signature.Parameters[index] is not CPointer)
                    throw new InvalidDataException($"{source}：{name} 的输入 {input.Name} 与 C 类型不一致");
            }
        }
        var location = f.GetProperty("declaration_source");
        var recognition = f.GetProperty("recognition");
        var declaredNoReturn = f.GetProperty("declared_noreturn").GetBoolean();
        if (declaredNoReturn && !op.DoesNotReturn) throw new InvalidDataException($"{source}：{name} 的 noreturn 声明与操作冲突");
        return new(name, Text(f, "mangled_name"), Text(f, "declaration"), new(Text(location, "file"), location.GetProperty("line").GetInt32()),
            signature, unsupported, declaredNoReturn, op, args, result, types, Text(f, "result_type"), Strings(f, "basis"),
            new(recognition.GetProperty("symbol").GetBoolean(), Optional(recognition, "export"), Optional(recognition, "call_graph"), Optional(recognition, "reference_shape"), recognition.TryGetProperty("import", out var import) ? import.GetString() : null));
    }
    private static CType Type(JsonElement t) => Text(t, "kind") switch
    {
        "void" => new CVoid(), "pointer" => new CPointer(t.GetProperty("bits").GetInt32()),
        "integer" => new CInteger(t.GetProperty("bits").GetInt32()), "float" => new CFloat(t.GetProperty("bits").GetInt32()),
        var kind => throw new InvalidDataException($"目录中未知 C 类型 {kind}")
    };
    private static string Text(JsonElement e, string key) => e.GetProperty(key).GetString() is { Length: > 0 } value ? value :
        throw new InvalidDataException($"目录属性 {key} 不能为空");
    private static string? Optional(JsonElement e, string key) => e.GetProperty(key).GetString();
    private static ImmutableArray<string> Strings(JsonElement e, string key) => e.GetProperty(key).EnumerateArray().Select(v => v.GetString()
        ?? throw new InvalidDataException($"目录 {key} 不能包含 null")).ToImmutableArray();
}
