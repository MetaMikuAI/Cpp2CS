using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using Cpp2CS.Facts;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using M = Cpp2CS.Model;
using MethodBody = Cpp2CS.Kernel.Forward.MethodBody;

namespace Cpp2CS.Tools.ForwardCheck;

internal sealed partial class SrmMetadata
{
    public int DecodedMethods { get; private set; }
    private readonly Dictionary<(string Image, int Token), EntityRef> specialized = [];

    // II.22。两遍索引先按程序集、嵌套关系与名称配对类型，随后才解码引用它们的签名。
    // 生成器的行号、缓存以及模型里的原模块记号均不参与配对。
    private void IndexGenerated(M.AssemblyMetadata extra)
    {
        generatedDefinitions = [];
        var model = Facts.Model;
        foreach (var image in model.Images)
        {
            var module = LoadImage(image.Name) ?? throw Unresolved(image.Name);
            var md = module.Md;
            var assembly = md.GetAssemblyDefinition();
            var expected = model.Assemblies[image.Assembly];
            var identity = extra.Identities[image.Assembly];
            if (module.Image != image.Name || md.GetString(assembly.Name) != expected.Name ||
                md.GetString(assembly.Culture) != expected.Culture ||
                assembly.Flags != identity.Flags || assembly.HashAlgorithm != identity.HashAlgorithm ||
                !md.GetBlobBytes(assembly.PublicKey).SequenceEqual(identity.PublicKey) ||
                assembly.Version != new Version(expected.Major, expected.Minor, expected.Build, expected.Revision))
                throw Unresolved("生成的程序集身份不符");
            var referenced = md.AssemblyReferences.Select(r => AssemblyScope(module, r)?.Image ?? throw Unresolved("程序集引用缺少目标")).ToHashSet();
            if (identity.References.Any(r => !referenced.Contains(model.Images[model.Assemblies[r].Image].Name)))
                throw Unresolved($"映像 {image.Name} 缺少声明的程序集引用");
            var candidates = Enumerable.Range(image.FirstType, image.TypeCount)
                .ToLookup(i => (model.Types[i].DeclaringType, model.Types[i].Namespace, model.Types[i].Name));
            int Match(TypeDefinitionHandle h)
            {
                var key = (module.Image, MetadataTokens.GetToken(h));
                if (types.TryGetValue(key, out int cached)) return cached;
                var t = md.GetTypeDefinition(h);
                int? outer = t.GetDeclaringType().IsNil ? null : Match(t.GetDeclaringType());
                int index = Unique(candidates[(outer, md.GetString(t.Namespace), md.GetString(t.Name))], $"类型 {md.GetString(t.Name)}");
                generatedDefinitions.Add(index, (module, h));
                types.Add(key, index);
                return index;
            }
            int count = 0;
            foreach (var h in md.TypeDefinitions)
            {
                var d = md.GetTypeDefinition(h);
                if (MetadataTokens.GetRowNumber(h) == 1 && !candidates.Contains((null, "", "<Module>")) &&
                    md.StringComparer.Equals(d.Name, "<Module>") && d.GetMethods().Count == 0 && d.GetFields().Count == 0) continue;
                Match(h);
                count++;
            }
            if (count != image.TypeCount) throw Unresolved($"映像 {image.Name} 的类型数不符");
        }
        foreach (var (i, (module, h)) in generatedDefinitions)
        {
            var d = model.Types[i];
            var md = module.Md;
            var def = md.GetTypeDefinition(h);
            var provider = new Provider(this, module);
            void CheckGenerics(GenericParameterHandleCollection parameters, IReadOnlyList<M.GenericParameter> expected)
            {
                if (parameters.Count != expected.Count) throw Unresolved($"类型 {i} 的泛型元数不符");
                int k = 0;
                foreach (var ph in parameters)
                {
                    var p = md.GetGenericParameter(ph);
                    var e = expected[k++];
                    var constraints = p.GetConstraints().Select(c => ReadType(module, md.GetGenericParameterConstraint(c).Type, null).Identity);
                    if (p.Index != e.Position || md.GetString(p.Name) != e.Name || p.Attributes != e.Flags ||
                        !constraints.SequenceEqual(e.Constraints.Select(TypeIdentity)))
                        throw Unresolved($"类型 {i} 的泛型参数 {p.Index} 不符");
                }
            }
            var byName = Range(d.FirstMethod, d.MethodCount).ToLookup(m => model.Methods[m].Name);
            var fieldNames = Range(d.FirstField, d.FieldCount).ToLookup(f => model.Fields[f].Name);
            if (def.Attributes != d.Flags || (def.BaseType.IsNil ? null : ReadType(module, def.BaseType, null).Identity) !=
                (d.Parent == null ? null : TypeIdentity(d.Parent))) throw Unresolved($"类型 {i} 的属性或基类不符");
            CheckGenerics(def.GetGenericParameters(), d.GenericParameters);
            var layout = def.GetLayout();
            if (extra.Layouts.TryGetValue(i, out var expectedLayout))
            {
                if (layout.PackingSize != expectedLayout.Pack || layout.Size != expectedLayout.Size)
                    throw Unresolved($"类型 {i} 的布局不符");
            }
            else if (!layout.IsDefault) throw Unresolved($"类型 {i} 出现额外布局");
            if (!def.GetInterfaceImplementations().Select(v => ReadType(module, md.GetInterfaceImplementation(v).Interface, null).Identity)
                .SequenceEqual(d.Interfaces.Select(TypeIdentity))) throw Unresolved($"类型 {i} 的接口不符");
            foreach (var mh in def.GetMethods())
            {
                var method = md.GetMethodDefinition(mh);
                var signature = Signature(method.DecodeSignature(provider, null));
                DecodedMethods++;
                string name = md.GetString(method.Name);
                var key = (module.Image, MetadataTokens.GetToken(mh));
                if (!byName.Contains(name) && name.StartsWith("<IL2CPP:", StringComparison.Ordinal) && name.EndsWith('>') &&
                    long.TryParse(name.AsSpan(8, name.Length - 9), out long instance))
                {
                    var entity = new EntityRef(EntityKind.Method, instance);
                    var m = Facts.Keys.DescribeMethod(entity) ?? throw Unresolved($"实例体 {name}");
                    if (m.TypeArguments.Count + m.MethodArguments.Count == 0 || model.Methods[m.Definition].Owner != i ||
                        SpecializedIdentity(m) != signature) throw Unresolved($"实例体 {name} 的签名不符");
                    specialized.Add(key, entity);
                    continue;
                }
                int index = Unique(byName[name].Where(m => MethodIdentity(model.Methods[m]) == signature), $"方法 {i}::{name} {signature}");
                var original = model.Methods[index];
                if (method.Attributes != original.Flags || method.ImplAttributes != original.ImplFlags)
                    throw Unresolved($"方法 {index} 的属性不符");
                CheckGenerics(method.GetGenericParameters(), original.GenericParameters);
                var ps = method.GetParameters().Select(p => md.GetParameter(p)).Where(p => p.SequenceNumber > 0)
                    .Select(p => (md.GetString(p.Name), p.Attributes, p.SequenceNumber));
                if (!ps.SequenceEqual(original.Parameters.Select((p, j) => (p.Name, extra.UnknownParameterDefaults.ContainsKey((index, j + 1))
                    ? p.Flags & ~ParameterAttributes.HasDefault : p.Flags, j + 1))))
                    throw Unresolved($"方法 {index} 的参数不符");
                methods.Add(key, index);
            }
            foreach (var fh in def.GetFields())
            {
                var field = md.GetFieldDefinition(fh);
                string name = md.GetString(field.Name);
                string sig = field.DecodeSignature(provider, null).Identity;
                int index = Unique(fieldNames[name].Where(f => TypeIdentity(model.Fields[f].Type) == sig), $"字段 {i}::{name} {sig}");
                if (field.Attributes != model.Fields[index].Flags) throw Unresolved($"字段 {index} 属性不符");
                var constant = field.GetDefaultValue();
                if (extra.FieldConstants.TryGetValue(index, out var value))
                {
                    if (constant.IsNil) throw Unresolved($"字段 {index} 缺少常量");
                    var c = md.GetConstant(constant);
                    if (!Equals(md.GetBlobReader(c.Value).ReadConstant(c.TypeCode), value)) throw Unresolved($"字段 {index} 的常量值不符");
                }
                else if (!constant.IsNil) throw Unresolved($"字段 {index} 出现额外常量");
                if (extra.FieldData.TryGetValue(index, out var data))
                {
                    int rva = field.GetRelativeVirtualAddress();
                    if (rva == 0 || !module.Pe.GetSectionData(rva).GetContent(0, data.Length).AsSpan().SequenceEqual(data))
                        throw Unresolved($"字段 {index} 的初始数据不符");
                }
                fields.Add((module.Image, MetadataTokens.GetToken(fh)), index);
            }
        }
        if (methods.Values.Distinct().Count() != model.Methods.Count || fields.Values.Distinct().Count() != model.Fields.Count)
            throw Unresolved("生成的程序集没有逐一覆盖模型的成员定义");
    }

    private static IEnumerable<int> Range(int start, int count) => Enumerable.Range(count == 0 ? 0 : start, count);
    private static int Unique(IEnumerable<int> candidates, string description)
    {
        using var e = candidates.GetEnumerator();
        if (!e.MoveNext()) throw Unresolved(description + " 没有匹配");
        int i = e.Current;
        if (e.MoveNext()) throw Unresolved(description + " 有多个匹配");
        return i;
    }

    private static string TypeIdentity(M.TypeReference t) => t switch
    {
        M.NamedType { Arguments.Count: 0 } n => $"D{n.Definition}",
        M.NamedType n => $"D{n.Definition}<{string.Join(",", n.Arguments.Select(TypeIdentity))}>",
        M.VariableType v => (v.Method ? "!!" : "!") + v.Position,
        M.ReferenceType r => TypeIdentity(r.Element) + "&",
        M.PointerType p => TypeIdentity(p.Element) + "*",
        M.ArrayType a => TypeIdentity(a.Element) + (a.Vector ? "[]" : $"[{a.Rank}::{string.Join(",", Enumerable.Repeat(0, a.Rank))}]"),
        _ => throw Unresolved($"类型签名 {t}"),
    };
    private static string MethodIdentity(M.MethodDefinition m)
    {
        int header = (m.Flags.HasFlag(MethodAttributes.Static) ? 0 : 32) + (m.GenericParameters.Count == 0 ? 0 : 16);
        return $"{header}:{m.GenericParameters.Count}:{m.Parameters.Count}:{TypeIdentity(m.ReturnType)}({string.Join(",", m.Parameters.Select(p => TypeIdentity(p.Type)))})";
    }

    private string SpecializedIdentity(M.MethodInstance m)
    {
        var d = Facts.Model.Methods[m.Definition];
        var owner = new M.NamedType(d.Owner, m.TypeArguments);
        var parameters = d.Parameters.Select(p => EntityKeys.Inflate(p.Type, owner, m.Definition, m.MethodArguments)).ToList();
        if (!d.Flags.HasFlag(MethodAttributes.Static))
            parameters.Insert(0, Facts.Model.Types[d.Owner].ValueType ? new M.ReferenceType(owner) : owner);
        return $"0:0:{parameters.Count}:{TypeIdentity(EntityKeys.Inflate(d.ReturnType, owner, m.Definition, m.MethodArguments))}({string.Join(",", parameters.Select(TypeIdentity))})";
    }

    public (MethodBody Body, ITokenResolver Tokens, int Peak) GeneratedBody(Module module, int token, ManagedBody expected)
    {
        var key = (module.Image, token);
        bool closed = specialized.TryGetValue(key, out var entity);
        if (!closed) entity = Tokens(module).Method(token);
        if (entity != expected.Host.Entity) throw Unresolved($"生成的方法体所属实体 {entity} 与 {expected.Host.Entity} 不同");
        var h = (MethodDefinitionHandle)MetadataTokens.EntityHandle(token);
        var m = module.Md.GetMethodDefinition(h);
        var context = closed ? null : Context(entity);
        var body = ReadBody(module, m, Facts.Method(entity), context);
        var tokens = Tokens(module, closed ? null : entity);
        var decoded = IlDecoder.Decode(body.Code.AsSpan());
        EmitChecks.Instructions(expected, decoded, tokens);
        var block = module.Pe.GetMethodBody(m.RelativeVirtualAddress);
        int peak = EmitChecks.Stack(decoded, tokens, Facts, body.Method, block.MaxStack);
        ImmutableArray<Sig> signatures = block.LocalSignature.IsNil ? [] : module.Md.GetStandaloneSignature(block.LocalSignature)
            .DecodeLocalSignature(new Provider(this, module), context);
        if (body.Locals.Length != expected.Locals.Length) throw Unresolved("写出前后的局部变量数不符");
        for (int i = 0; i < body.Locals.Length; i++)
        {
            var a = expected.Locals[i];
            var b = body.Locals[i];
            if (signatures[i].Identity != TypeIdentity(signatures[i].Concrete)) throw Unresolved($"局部变量 {i} 带有模型未表达的签名成分");
            if ((a.Kind, a.StorageBits, a.Signed, a.TwoValued) != (b.Kind, b.StorageBits, b.Signed, b.TwoValued))
                throw Unresolved($"局部变量 {i} 的存储形状不同");
            if (a.Entity != default && Facts.Type(a.Entity) is var e &&
                (a.Kind == StackKind.ByRef || e.StorageBits == a.StorageBits) && a.Entity != b.Entity)
                throw Unresolved($"局部变量 {i} 的类型实体不同");
        }
        return (body, tokens, peak);
    }
}
