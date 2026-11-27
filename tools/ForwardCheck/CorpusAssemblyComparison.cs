using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;

namespace Cpp2CS.Tools.ForwardCheck;

internal static class CorpusAssemblyComparison
{
    // 真实程序集的修饰符、数组界与调用约定都参与比较。重载以完整签名作多重集配对。
    private sealed class Names(MetadataReader md) : ISignatureTypeProvider<string, object?>
    {
        private readonly Dictionary<EntityHandle, string> cache = [];
        public string Type(EntityHandle h)
        {
            if (h.IsNil) return "";
            if (cache.TryGetValue(h, out var value)) return value;
            string Top(string scope, StringHandle ns, StringHandle name) => $"[{scope}]{md.GetString(ns)}.{md.GetString(name)}";
            string assembly = md.GetString(md.GetAssemblyDefinition().Name);
            switch (h.Kind)
            {
                case HandleKind.TypeDefinition:
                    var d = md.GetTypeDefinition((TypeDefinitionHandle)h);
                    value = d.GetDeclaringType().IsNil ? Top(assembly, d.Namespace, d.Name) : Type(d.GetDeclaringType()) + "+" + md.GetString(d.Name);
                    break;
                case HandleKind.TypeReference:
                    var r = md.GetTypeReference((TypeReferenceHandle)h);
                    var scope = r.ResolutionScope;
                    value = scope.Kind == HandleKind.TypeReference ? Type(scope) + "+" + md.GetString(r.Name) :
                        Top(scope.Kind == HandleKind.AssemblyReference ? md.GetString(md.GetAssemblyReference((AssemblyReferenceHandle)scope).Name) : assembly, r.Namespace, r.Name);
                    break;
                case HandleKind.TypeSpecification: value = md.GetTypeSpecification((TypeSpecificationHandle)h).DecodeSignature(this, null); break;
                default: throw new BadImageFormatException("无效的类型句柄");
            }
            return cache[h] = value;
        }
        public static string Signature(MethodSignature<string> s) =>
            $"{s.Header.RawValue}/{s.GenericParameterCount}/{s.RequiredParameterCount} {s.ReturnType}({string.Join(",", s.ParameterTypes)})";
        public string GetPrimitiveType(PrimitiveTypeCode c) => c.ToString();
        public string GetTypeFromDefinition(MetadataReader _, TypeDefinitionHandle h, byte k) => k + Type(h);
        public string GetTypeFromReference(MetadataReader _, TypeReferenceHandle h, byte k) => k + Type(h);
        public string GetTypeFromSpecification(MetadataReader _, object? c, TypeSpecificationHandle h, byte k) => Type(h);
        public string GetGenericInstantiation(string d, ImmutableArray<string> a) => d + "<" + string.Join(",", a) + ">";
        public string GetGenericMethodParameter(object? c, int i) => "!!" + i;
        public string GetGenericTypeParameter(object? c, int i) => "!" + i;
        public string GetSZArrayType(string e) => e + "[]";
        public string GetArrayType(string e, ArrayShape s) => $"{e}[{s.Rank}:{string.Join(",",s.Sizes)}:{string.Join(",",s.LowerBounds)}]";
        public string GetPointerType(string e) => e + "*";
        public string GetByReferenceType(string e) => e + "&";
        public string GetModifiedType(string m, string e, bool r) => $"{(r ? "modreq" : "modopt")}({m}){e}";
        public string GetPinnedType(string e) => "pinned " + e;
        public string GetFunctionPointerType(MethodSignature<string> s) => "fn " + Signature(s);
    }

    private sealed record Row(string Kind, string Name, string Signature);
    private static IEnumerable<Row> Rows(Module module)
    {
        var md = module.Md;
        var names = new Names(md);
        string Generics(GenericParameterHandleCollection handles) => string.Join("|", handles.Select(h =>
        {
            var p = md.GetGenericParameter(h);
            return $"{md.GetString(p.Name)}/{p.Attributes}/{string.Join(",", p.GetConstraints().Select(c => names.Type(md.GetGenericParameterConstraint(c).Type)).Order(StringComparer.Ordinal))}";
        }));
        foreach (var h in md.TypeDefinitions)
        {
            var d = md.GetTypeDefinition(h);
            string name = names.Type(h);
            var interfaces = d.GetInterfaceImplementations().Select(i => names.Type(md.GetInterfaceImplementation(i).Interface)).Order(StringComparer.Ordinal);
            yield return new("类型", name, $"{names.Type(d.BaseType)} {string.Join(",", interfaces)} {Generics(d.GetGenericParameters())}");
            foreach (var f in d.GetFields())
            {
                var field = md.GetFieldDefinition(f);
                yield return new("字段", name + "::" + md.GetString(field.Name), field.DecodeSignature(names, null));
                if (!field.GetDefaultValue().IsNil)
                {
                    var constant = md.GetConstant(field.GetDefaultValue());
                    yield return new("字段常量", name+"::"+md.GetString(field.Name), constant.TypeCode + "/" + Convert.ToHexString(md.GetBlobBytes(constant.Value)));
                }
            }
            foreach (var m in d.GetMethods())
            {
                var method = md.GetMethodDefinition(m);
                yield return new("方法", name + "::" + md.GetString(method.Name), Names.Signature(method.DecodeSignature(names, null)) + " " + Generics(method.GetGenericParameters()));
            }
        }
    }

    public static void Compare(SrmMetadata original, SrmMetadata generated)
    {
        var a = new List<Row>();
        var b = new List<Row>();
        long[] omitted = new long[3];
        foreach (var image in generated.Facts.Model.Images)
        {
            b.AddRange(Rows(generated.LoadImage(image.Name)!));
            var source = original.LoadImage(image.Name);
            if (source == null)
            {
                Console.WriteLine($"元数据独有映像 {image.Name}");
                continue;
            }
            a.AddRange(Rows(source));
            omitted[0] += source.Md.PropertyDefinitions.Count;
            omitted[1] += source.Md.EventDefinitions.Count;
            omitted[2] += source.Md.CustomAttributes.Count;
        }
        foreach (string kind in new[] { "类型", "字段", "方法", "字段常量" })
        {
            var before = a.Where(r => r.Kind == kind).ToLookup(r => r.Name);
            var after = b.Where(r => r.Kind == kind).ToLookup(r => r.Name);
            int same = 0, different = 0, missing = 0, additional = 0;
            foreach (var key in before.Select(g => g.Key).Union(after.Select(g => g.Key)))
            {
                var l = before[key].ToArray();
                var r = after[key].ToArray();
                var counts = r.CountBy(row => row.Signature).ToDictionary();
                int matched = 0;
                foreach (var row in l)
                    if (counts.GetValueOrDefault(row.Signature) > 0) { matched++; counts[row.Signature]--; }
                same += matched;
                different += Math.Min(l.Length, r.Length) - matched;
                missing += Math.Max(0, l.Length-r.Length);
                additional += Math.Max(0, r.Length-l.Length);
                if (matched != Math.Max(l.Length, r.Length))
                    Console.WriteLine($"  {kind}差异 {key} 真值 {string.Join(" | ", l.Select(v=>v.Signature))} 生成 {string.Join(" | ", r.Select(v=>v.Signature))}");
            }
            Console.WriteLine($"{kind} 真值 {same+different+missing}，生成 {same+different+additional}，相同 {same}，签名差异 {different}，缺少 {missing}，新增 {additional}");
        }
        Console.WriteLine($"真值属性 {omitted[0]}，事件 {omitted[1]}，自定义特性 {omitted[2]}，生成均为 0");
    }
}
