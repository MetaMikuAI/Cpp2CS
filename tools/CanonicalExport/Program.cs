using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Model;

if (args.Length is not (3 or 4))
{
    Console.Error.WriteLine("用法：CanonicalExport <ELF> <元数据> <输出.jsonl> [字段偏移来源.tsv]");
    return 2;
}
var input = Il2CppInput.Load(args[0], args[1]);
var model = input.Model;
var code = input.Code;
using var output = new StreamWriter(args[2], false, new UTF8Encoding(false), 65536);
using var evidence = args.Length == 4 ? new StreamWriter(args[3]) : null;
evidence?.WriteLine("index\towner\tordinal\tgenericCount\tvirtualAddress\tfileOffset\traw");
var counts = new SortedDictionary<string, int>(StringComparer.Ordinal);

void Emit<T>(string kind, T row)
{
    output.WriteLine(JsonSerializer.Serialize(row));
    counts[kind] = counts.GetValueOrDefault(kind) + 1;
}

static string Arguments(IEnumerable<TypeReference> args) => "<" + string.Join(",", args.Select(Type)) + ">";
static string Type(TypeReference type) => type switch
{
    NamedType t => "D" + t.Definition + (t.Arguments.Count == 0 ? "" : Arguments(t.Arguments)),
    ArrayType a => Type(a.Element) + (a.Vector ? "[]" : $"[{a.Rank}]"),
    VariableType v => (v.Method ? "!!M" : "!D") + v.Owner + "." + v.Position,
    ReferenceType r => Type(r.Element) + "&",
    PointerType p => Type(p.Element) + "*",
    _ => throw new InvalidDataException($"没有定义类型的规范写法 {type}")
};
static object[] Parameters(IReadOnlyList<GenericParameter> ps) => ps.Select(p =>
    (object)new { constraints = p.Constraints.Select(Type), flags = (int)p.Flags, name = p.Name, position = p.Position }).ToArray();

for (int index = 0; index < model.Fields.Count; index++)
{
    var f = model.Fields[index];
    Emit("field", new { flags = (int)f.Flags, index, instanceOffset = f.Storage == FieldStorage.Instance ? f.Offset : null, kind = "field",
        name = f.Name, ordinal = f.Ordinal, owner = f.Owner, staticOffset = f.Storage == FieldStorage.Static ? f.Offset : null,
        threadStaticOffset = f.Storage == FieldStorage.ThreadStatic ? f.Offset : null, type = Type(f.Type) });
    if (evidence != null)
    {
        var s = input.FieldOffsetSource(index);
        evidence.WriteLine($"{index}\t{f.Owner}\t{f.Ordinal}\t{model.Types[f.Owner].GenericParameters.Count}\t{s?.Address:x}\t{s?.FileOffset:x}\t{s?.Value}");
    }
}
for (int index = 0; index < model.MethodInstances.Count; index++)
{
    var m = model.MethodInstances[index];
    var instance = $"M{m.Definition}{Arguments(m.TypeArguments)}{Arguments(m.MethodArguments)}";
    var mapping = code.MethodInstances[index];
    Emit("generic-method", new { entry = mapping.Entry, index, instance, invoker = mapping.Invoker, kind = "generic-method" });
}
for (int index = 0; index < model.Images.Count; index++)
{
    var image = model.Images[index];
    var a = model.Assemblies[image.Assembly];
    var version = a.Build < 0 ? new Version(a.Major, a.Minor) : new Version(a.Major, a.Minor, a.Build, a.Revision);
    Emit("image", new { assembly = a.Name, culture = a.Culture, end = image.FirstType + image.TypeCount, index, kind = "image",
        name = image.Name, start = image.FirstType, version = version.ToString() });
}
for (int index = 0; index < code.Invokers.Count; index++)
    if (code.Invokers[index] is { } entry) Emit("invoker", new { entry, index, kind = "invoker" });

for (int index = 0; index < model.Methods.Count; index++)
{
    var m = model.Methods[index];
    var mapping = code.Methods[index];
    Emit("method", new { entry = mapping.Entry, flags = (int)m.Flags, genericParameters = Parameters(m.GenericParameters),
        implFlags = (int)m.ImplFlags, index, invoker = mapping.Invoker, kind = "method", name = m.Name, owner = m.Owner,
        signature = $"{Type(m.ReturnType)}`{m.GenericParameters.Count}({string.Join(",", m.Parameters.Select(p => Type(p.Type)))})", token = m.Token });
}
Emit("registration", new { code = code.CodeRegistration, index = 0, kind = "registration", metadata = code.MetadataRegistration });
for (int index = 0; index < model.RuntimeTypes.Count; index++)
    Emit("runtime-type", new { index, kind = "runtime-type", type = Type(model.RuntimeTypes[index]) });
for (int index = 0; index < model.StringLiterals.Count; index++)
    Emit("string-literal", new { index, kind = "string-literal", sha256 = Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(model.StringLiterals[index]))) });
for (int index = 0; index < model.Types.Count; index++)
{
    var t = model.Types[index];
    Emit("type", new { declaring = t.DeclaringType, fields = t.FieldCount, flags = (uint)t.Flags,
        genericCount = t.GenericParameters.Count, genericParameters = Parameters(t.GenericParameters), index,
        interfaces = t.Interfaces.Select(Type), kind = "type", methods = t.MethodCount, name = t.Name, @namespace = t.Namespace,
        parent = t.Parent == null ? null : Type(t.Parent) });
}
output.WriteLine(JsonSerializer.Serialize(new { counts, index = 0, kind = "summary" }));
return 0;
