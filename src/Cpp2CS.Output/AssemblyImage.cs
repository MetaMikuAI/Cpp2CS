using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using AsmResolver;
using AsmResolver.IO;
using AsmResolver.PE;
using AsmResolver.PE.Builder;
using AsmResolver.PE.DotNet;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata;
using Cpp2CS.Facts;
using Cpp2CS.Kernel;
using Cpp2CS.Snapshot;
using M = Cpp2CS.Model;
using MethodRow = AsmResolver.PE.DotNet.Metadata.Tables.MethodDefinitionRow;

namespace Cpp2CS.Output;

/// <summary>每个映像独立分配表行。先排定定义，再按签名和方法体实际需要登记引用。</summary>
public sealed partial class AssemblyImage
{
    private readonly ModelMetadata facts;
    private readonly M.MetadataModel model;
    private readonly M.AssemblyMetadata extra;
    private readonly M.ImageDefinition image;
    private readonly MetadataBuilder tables = new();
    private readonly Dictionary<int, TypeDefinitionHandle> types = [];
    private readonly Dictionary<int, FieldDefinitionHandle> fields = [];
    private readonly Dictionary<int, MethodDefinitionHandle> methods = [];
    private readonly Dictionary<int, AssemblyReferenceHandle> assemblies = [];
    private readonly Dictionary<int, TypeReferenceHandle> references = [];
    private readonly Dictionary<BlobHandle, TypeSpecificationHandle> specs = [];
    private readonly Dictionary<(EntityHandle, StringHandle, BlobHandle), MemberReferenceHandle> members = [];
    private readonly Dictionary<(EntityHandle, BlobHandle), MethodSpecificationHandle> instances = [];
    private readonly Dictionary<BlobHandle, StandaloneSignatureHandle> locals = [];
    private readonly List<(EntityHandle Owner, IReadOnlyList<M.GenericParameter> Parameters)> generic = [];
    private readonly Dictionary<MethodDefinitionHandle, CilMethodBody> written = [];
    private readonly List<byte[]> rvaData = [];
    private readonly Dictionary<EntityRef, ManagedBody> bodies;
    private readonly ILookup<int, M.MethodInstance> specializations;
    private readonly Dictionary<EntityRef, int> hosts = [];
    private bool NeedsModuleType => image.TypeCount == 0 || model.Types[image.FirstType] is not { Name: "<Module>", Namespace.Length: 0, DeclaringType: null };

    public AssemblyImage(ModelMetadata facts, M.AssemblyMetadata extra, M.ImageDefinition image, IEnumerable<ManagedBody> recovered)
    {
        this.facts = facts;
        model = facts.Model;
        this.extra = extra;
        this.image = image;
        bodies = recovered.ToDictionary(b => b.Host.Entity);
        specializations = bodies.Keys.Select(e => facts.Keys.DescribeMethod(e) ?? throw Missing(e))
            .Where(m => m.TypeArguments.Count + m.MethodArguments.Count > 0)
            .ToLookup(m => model.Methods[m.Definition].Owner);
        int nextField = 1, nextMethod = 1;
        for (int k = 0; k < image.TypeCount; k++)
        {
            int i = image.FirstType + k;
            var d = model.Types[i];
            types.Add(i, MetadataTokens.TypeDefinitionHandle(k + (NeedsModuleType ? 2 : 1)));
            for (int f = d.FirstField; f < d.FirstField + d.FieldCount; f++)
                fields.Add(f, MetadataTokens.FieldDefinitionHandle(nextField++));
            for (int m = d.FirstMethod; m < d.FirstMethod + d.MethodCount; m++)
                methods.Add(m, MetadataTokens.MethodDefinitionHandle(nextMethod++));
            nextMethod += specializations[i].Count();
        }
    }

    private static InvalidDataException Missing(EntityRef entity) => new($"模型无法解释实体 {entity}");
    private static Version Version(M.AssemblyDefinition a) => new(a.Major, a.Minor, a.Build, a.Revision);
    private StringHandle S(string s) => tables.GetOrAddString(s);
    private AssemblyReferenceHandle Assembly(int i)
    {
        if (assemblies.TryGetValue(i, out var h)) return h;
        var a = model.Assemblies[i];
        var id = extra.Identities[i];
        return assemblies[i] = tables.AddAssemblyReference(S(a.Name), Version(a), S(a.Culture),
            tables.GetOrAddBlob(id.Token), id.Flags & ~AssemblyFlags.PublicKey, default);
    }

    public IReadOnlyDictionary<EntityRef, int> Write(string directory)
    {
        if (Path.GetFileName(image.Name) != image.Name || image.Name is "" or "." or "..")
            throw new InvalidDataException("映像名不是文件名");
        var a = model.Assemblies[image.Assembly];
        var id = extra.Identities[image.Assembly];
        tables.AddModule(0, S(image.Name), tables.GetOrAddGuid(Guid.NewGuid()), default, default);
        tables.AddAssembly(S(a.Name), Version(a), S(a.Culture), tables.GetOrAddBlob(id.PublicKey), id.Flags, id.HashAlgorithm);
        foreach (int reference in id.References) Assembly(reference);
        if (NeedsModuleType)
            tables.AddTypeDefinition(0, default, S("<Module>"), default, MetadataTokens.FieldDefinitionHandle(1), MetadataTokens.MethodDefinitionHandle(1));
        for (int i = image.FirstType; i < image.FirstType + image.TypeCount; i++)
        {
            var d = model.Types[i];
            var type = tables.AddTypeDefinition(d.Flags, S(d.Namespace), S(d.Name), d.Parent == null ? default : TypeHandle(d.Parent),
                MetadataTokens.FieldDefinitionHandle(tables.GetRowCount(TableIndex.Field) + 1),
                MetadataTokens.MethodDefinitionHandle(tables.GetRowCount(TableIndex.MethodDef) + 1));
            if (type != types[i]) throw new InvalidDataException("类型定义行次序不符");
            if (extra.Layouts.TryGetValue(i, out var layout)) tables.AddTypeLayout(type, layout.Pack, layout.Size);
            if (d.DeclaringType is int parent) tables.AddNestedType(type, types[parent]);
            foreach (var item in d.Interfaces) tables.AddInterfaceImplementation(type, TypeHandle(item));
            if (d.GenericParameters.Count > 0) generic.Add((type, d.GenericParameters));
            for (int f = d.FirstField; f < d.FirstField + d.FieldCount; f++)
            {
                var field = model.Fields[f];
                var h = tables.AddFieldDefinition(field.Flags, S(field.Name), FieldSignature(field));
                if (h != fields[f]) throw new InvalidDataException("字段定义行次序不符");
                if (extra.FieldConstants.TryGetValue(f, out var value)) tables.AddConstant(h, value);
                if (extra.FieldData.TryGetValue(f, out var data))
                {
                    tables.AddFieldRelativeVirtualAddress(h, 0);
                    rvaData.Add(data);
                }
                if ((d.Flags & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout && field.Storage == M.FieldStorage.Instance && field.Offset is int offset)
                    tables.AddFieldLayout(h, offset);
            }
            for (int m = d.FirstMethod; m < d.FirstMethod + d.MethodCount; m++)
            {
                var method = model.Methods[m];
                var h = tables.AddMethodDefinition(method.Flags, method.ImplFlags, S(method.Name), MethodSignature(method), -1, NextParameter());
                if (h != methods[m]) throw new InvalidDataException("方法定义行次序不符");
                for (int j = 0; j < method.Parameters.Count; j++)
                {
                    var p = method.Parameters[j];
                    var flags = extra.UnknownParameterDefaults.ContainsKey((m, j + 1)) ? p.Flags & ~ParameterAttributes.HasDefault : p.Flags;
                    var param = tables.AddParameter(flags, S(p.Name), j + 1);
                    if (extra.ParameterConstants.TryGetValue((m, j + 1), out var value)) tables.AddConstant(param, value);
                }
                if (method.GenericParameters.Count > 0) generic.Add((h, method.GenericParameters));
                var entity = new EntityRef(EntityKind.Method, m);
                if (bodies.TryGetValue(entity, out var body)) WriteBody(h, body);
            }
            foreach (var m in specializations[i])
            {
                var entity = new EntityRef(EntityKind.Method, facts.Keys.MethodKey(m)!.Value);
                string name = $"<IL2CPP:{entity.Key}>";
                if (Enumerable.Range(d.FirstMethod < 0 ? 0 : d.FirstMethod, d.MethodCount).Any(j => model.Methods[j].Name == name))
                    throw new InvalidDataException("实例体的名称与原方法冲突");
                var h = tables.AddMethodDefinition(MethodAttributes.Private | MethodAttributes.Static, MethodImplAttributes.IL,
                    S(name), SpecializedSignature(m), -1, NextParameter());
                WriteBody(h, bodies[entity]);
            }
        }
        if (hosts.Count != bodies.Count) throw new InvalidDataException("恢复的方法不全属于此映像");
        foreach (var (owner, parameters) in generic.OrderBy(p => CodedIndex.TypeOrMethodDef(p.Owner)))
            foreach (var p in parameters)
            {
                var h = tables.AddGenericParameter(owner, p.Flags, S(p.Name), p.Position);
                foreach (var constraint in p.Constraints) tables.AddGenericParameterConstraint(h, TypeHandle(constraint));
            }
        var blob = new BlobBuilder();
        new MetadataRootBuilder(tables).Serialize(blob, 0, 0);
        var md = MetadataDirectory.FromBytes(blob.ToArray());
        var rows = md.GetStream<TablesStream>().GetTable<MethodRow>();
        var rvas = md.GetStream<TablesStream>().GetTable<AsmResolver.PE.DotNet.Metadata.Tables.FieldRvaRow>();
        for (int j = 0; j < rvaData.Count; j++)
        {
            var row = rvas[j];
            row.Data = new DataSegment(rvaData[j]).ToReference();
            rvas.SetByRid((uint)j + 1, row);
        }
        foreach (var (handle, body) in written)
        {
            uint rid = (uint)MetadataTokens.GetRowNumber(handle);
            var row = rows.GetByRid(rid);
            var reader = new BinaryStreamReader(body.Bytes.ToArray());
            var raw = CilRawMethodBody.FromReader(ref reader) ?? throw new InvalidDataException("无法读取写出的方法头");
            row.Body = raw.ToReference();
            rows.SetByRid(rid, row);
        }
        var pe = new PEImage { DotNetDirectory = new DotNetDirectory { Metadata = md, Flags = DotNetDirectoryFlags.ILOnly } };
        pe.Characteristics |= AsmResolver.PE.File.Characteristics.Dll;
        new ManagedPEFileBuilder().CreateFile(pe).Write(Path.Combine(directory, image.Name));
        return hosts;
    }

    private ParameterHandle NextParameter() => MetadataTokens.ParameterHandle(tables.GetRowCount(TableIndex.Param) + 1);
    private void WriteBody(MethodDefinitionHandle h, ManagedBody body)
    {
        var tokens = new Tokens(this, body.Host.Entity);
        var result = CilWriter.Write(body, tokens, facts, Register, tokens.Signature);
        written.Add(h, result.Body ?? throw new InvalidDataException(result.Reason));
        hosts.Add(body.Host.Entity, MetadataTokens.GetToken(h));
    }
    private int Register(ImmutableArray<byte> bytes)
    {
        var blob = tables.GetOrAddBlob(bytes);
        if (!locals.TryGetValue(blob, out var h)) locals.Add(blob, h = tables.AddStandaloneSignature(blob));
        return MetadataTokens.GetToken(h);
    }
}
