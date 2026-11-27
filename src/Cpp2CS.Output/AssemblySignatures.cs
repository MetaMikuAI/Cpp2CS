using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using Cpp2CS.Facts;
using Cpp2CS.Snapshot;
using M = Cpp2CS.Model;

namespace Cpp2CS.Output;

public sealed partial class AssemblyImage
{
    private EntityHandle Definition(int i)
    {
        if (types.TryGetValue(i, out var definition)) return definition;
        if (references.TryGetValue(i, out var reference)) return reference;
        var d = model.Types[i];
        EntityHandle parent = d.DeclaringType is int outer ? Definition(outer) :
            Assembly(model.Images.Single(im => i >= im.FirstType && i < im.FirstType + im.TypeCount).Assembly);
        return references[i] = tables.AddTypeReference(parent, S(d.Namespace), S(d.Name));
    }

    private EntityHandle TypeHandle(M.TypeReference type)
    {
        if (type is M.NamedType { Arguments.Count: 0 } named) return Definition(named.Definition);
        var b = new BlobBuilder();
        TypeSignature(b, type);
        var sig = tables.GetOrAddBlob(b);
        if (!specs.TryGetValue(sig, out var h)) specs.Add(sig, h = tables.AddTypeSpecification(sig));
        return h;
    }

    // ECMA-335 II.23.2.12。签名中的泛型变量按位置绑定，成员引用使用定义签名。
    private void TypeSignature(BlobBuilder b, M.TypeReference t, M.MethodInstance? caller = null)
    {
        switch (t)
        {
            case M.NamedType n:
                var d = model.Types[n.Definition];
                if (n.Arguments.Count == 0 && d.Namespace == "System" && d.DeclaringType == null &&
                    Enum.TryParse<PrimitiveTypeCode>(d.Name, out var code) && code.ToString() == d.Name &&
                    facts.CoreType(d.Name).Definition == n.Definition)
                {
                    b.WriteByte((byte)code);
                    break;
                }
                if (n.Arguments.Count > 0) b.WriteByte(0x15);
                b.WriteByte(d.ValueType ? (byte)0x11 : (byte)0x12);
                b.WriteCompressedInteger(CodedIndex.TypeDefOrRef(Definition(n.Definition)));
                if (n.Arguments.Count > 0)
                {
                    b.WriteCompressedInteger(n.Arguments.Count);
                    foreach (var a in n.Arguments) TypeSignature(b, a, caller);
                }
                break;
            case M.VariableType v:
                if (caller != null && (v.Owner != (v.Method ? caller.Definition : model.Methods[caller.Definition].Owner)
                    || (v.Method ? caller.MethodArguments : caller.TypeArguments).Count > 0))
                    throw new InvalidDataException("方法体含未绑定到其作用域的泛型变量");
                b.WriteByte(v.Method ? (byte)0x1e : (byte)0x13);
                b.WriteCompressedInteger(v.Position);
                break;
            case M.ArrayType a:
                b.WriteByte(a.Vector ? (byte)0x1d : (byte)0x14);
                TypeSignature(b, a.Element, caller);
                if (!a.Vector)
                {
                    b.WriteCompressedInteger(a.Rank);
                    b.WriteCompressedInteger(0);
                    b.WriteCompressedInteger(a.Rank);
                    for (int j = 0; j < a.Rank; j++) b.WriteCompressedSignedInteger(0);
                }
                break;
            case M.PointerType p: b.WriteByte(0x0f); TypeSignature(b, p.Element, caller); break;
            case M.ReferenceType r: b.WriteByte(0x10); TypeSignature(b, r.Element, caller); break;
            default: throw new InvalidDataException($"不支持的签名元素 {t}");
        }
    }

    private BlobHandle FieldSignature(M.FieldDefinition f)
    {
        var b = new BlobBuilder();
        b.WriteByte(6);
        TypeSignature(b, f.Type);
        return tables.GetOrAddBlob(b);
    }

    private BlobHandle MethodSignature(M.MethodDefinition m)
    {
        var b = new BlobBuilder();
        int arity = m.GenericParameters.Count;
        b.WriteByte((byte)((m.Flags.HasFlag(MethodAttributes.Static) ? 0 : 0x20) | (arity == 0 ? 0 : 0x10)));
        if (arity > 0) b.WriteCompressedInteger(arity);
        b.WriteCompressedInteger(m.Parameters.Count);
        TypeSignature(b, m.ReturnType);
        foreach (var p in m.Parameters) TypeSignature(b, p.Type);
        return tables.GetOrAddBlob(b);
    }

    // 一份实例体只证明了该封闭实例。单列静态方法，显式传入代入实参后的接收方。
    private BlobHandle SpecializedSignature(M.MethodInstance m)
    {
        var d = model.Methods[m.Definition];
        var owner = new M.NamedType(d.Owner, m.TypeArguments);
        M.TypeReference Inflate(M.TypeReference t) => EntityKeys.Inflate(t, owner, m.Definition, m.MethodArguments);
        var b = new BlobBuilder();
        b.WriteByte(0);
        bool instance = !d.Flags.HasFlag(MethodAttributes.Static);
        b.WriteCompressedInteger(d.Parameters.Count + (instance ? 1 : 0));
        TypeSignature(b, Inflate(d.ReturnType), m);
        if (instance) TypeSignature(b, model.Types[d.Owner].ValueType ? new M.ReferenceType(owner) : owner, m);
        foreach (var p in d.Parameters) TypeSignature(b, Inflate(p.Type), m);
        return tables.GetOrAddBlob(b);
    }

    private EntityHandle Member(EntityHandle parent, string name, BlobHandle signature)
    {
        var key = (parent, S(name), signature);
        if (!members.TryGetValue(key, out var h)) members.Add(key, h = tables.AddMemberReference(parent, key.Item2, signature));
        return h;
    }

    private sealed class Tokens(AssemblyImage image, EntityRef host) : IEntityTokens
    {
        private readonly M.MethodInstance caller = image.facts.Keys.DescribeMethod(host) ?? throw Missing(host);
        public ImmutableArray<byte> Signature(EntityRef entity)
        {
            var b = new BlobBuilder();
            image.TypeSignature(b, image.facts.Keys.DescribeType(entity) ?? throw Missing(entity), caller);
            return b.ToImmutableArray();
        }
        public int Type(EntityRef entity) => MetadataTokens.GetToken(image.TypeHandle(image.facts.Keys.DescribeType(entity) ?? throw Missing(entity)));
        public int Field(EntityRef entity)
        {
            var (i, owner) = image.facts.Keys.DescribeField(entity) ?? throw Missing(entity);
            if (owner.Arguments.Count == 0 && image.fields.TryGetValue(i, out var h)) return MetadataTokens.GetToken(h);
            var f = image.model.Fields[i];
            return MetadataTokens.GetToken(image.Member(image.TypeHandle(owner), f.Name, image.FieldSignature(f)));
        }
        public int Method(EntityRef entity)
        {
            var m = image.facts.Keys.DescribeMethod(entity) ?? throw Missing(entity);
            var d = image.model.Methods[m.Definition];
            EntityHandle h = m.TypeArguments.Count == 0 && image.methods.TryGetValue(m.Definition, out var local) ? local :
                image.Member(image.TypeHandle(new M.NamedType(d.Owner, m.TypeArguments)), d.Name, image.MethodSignature(d));
            if (m.MethodArguments.Count > 0)
            {
                var b = new BlobBuilder();
                b.WriteByte(0x0a);
                b.WriteCompressedInteger(m.MethodArguments.Count);
                foreach (var a in m.MethodArguments) image.TypeSignature(b, a, caller);
                var blob = image.tables.GetOrAddBlob(b);
                if (!image.instances.TryGetValue((h, blob), out var spec))
                    image.instances.Add((h, blob), spec = image.tables.AddMethodSpecification(h, blob));
                h = spec;
            }
            return MetadataTokens.GetToken(h);
        }
    }
}
