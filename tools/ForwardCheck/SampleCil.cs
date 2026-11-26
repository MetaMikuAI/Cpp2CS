using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using Cpp2CS.Facts;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Output;
using Cpp2CS.Snapshot;
using M = Cpp2CS.Model;
using MethodBody = Cpp2CS.Kernel.Forward.MethodBody;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>定义记号按映像分域。原始元数据没有引用表时，只写可在调用方上下文中往返的定义。</summary>
internal sealed class DefinitionTokens(ModelMetadata facts)
{
    private readonly Dictionary<M.ImageDefinition, Dictionary<int, int>> maps = [];

    public sealed class Scope(DefinitionTokens source, ModelMetadata facts, M.ImageDefinition image, M.MethodInstance caller)
        : IEntityTokens, ITokenResolver
    {
        private M.MetadataModel Model => facts.Model;
        private M.NamedType Owner => new(Model.Methods[caller.Definition].Owner, caller.TypeArguments);
        private ExpansionException Missing(string what) => new("缺少宿主模块记号", $"{image.Name}，{what}");
        public int Index(int token) => source.maps[image].TryGetValue(token, out int i) ? i : throw Missing($"0x{token:x8}");

        public EntityRef Method(int token)
        {
            int i = Index(token);
            if (caller.TypeArguments.Count == 0 || Model.Methods[i].Owner != Owner.Definition) return new(EntityKind.Method, i);
            return new(EntityKind.Method, facts.Keys.MethodKey(new M.MethodInstance(i, caller.TypeArguments, [])) ?? throw Missing($"方法实例 {i}"));
        }
        public EntityRef Field(int token)
        {
            int i = Index(token);
            return Model.Fields[i].Owner == Owner.Definition
                ? new(EntityKind.Field, facts.Keys.FieldKey(i, Owner) ?? throw Missing($"字段实例 {i}")) : new(EntityKind.Field, i);
        }
        public EntityRef Type(int token) => facts.TypeEntity(new M.NamedType(Index(token), []));
        public EntityRef String(int token) => throw Missing($"用户字符串 0x{token:x8}");

        private int Check(uint token, EntityRef entity, Func<int, EntityRef> resolve, int definition)
        {
            int value = checked((int)token);
            if (Index(value) != definition || resolve(value) != entity) throw Missing($"{entity}");
            return value;
        }
        public int Method(EntityRef entity)
        {
            int i = (facts.Keys.DescribeMethod(entity) ?? throw Missing($"{entity}")).Definition;
            return Check(Model.Methods[i].Token, entity, Method, i);
        }
        public int Field(EntityRef entity)
        {
            int i = (facts.Keys.DescribeField(entity) ?? throw Missing($"{entity}")).Index;
            return Check(Model.Fields[i].Token, entity, Field, i);
        }
        public int Type(EntityRef entity)
        {
            var t = Model.RuntimeTypes[checked((int)entity.Key)];
            if ((t is M.ReferenceType r ? r.Element : t) is not M.NamedType n) throw Missing($"{entity}");
            return Check(Model.Types[n.Definition].Token, entity, Type, n.Definition);
        }
        public EntityHandle Definition(int i)
        {
            int token = checked((int)Model.Types[i].Token);
            if (Index(token) != i) throw Missing($"类型定义 {i}");
            return MetadataTokens.EntityHandle(token);
        }
    }

    public Scope For(EntityRef method)
    {
        var caller = facts.Keys.DescribeMethod(method)!;
        int owner = facts.Model.Methods[caller.Definition].Owner;
        var image = facts.Model.Images.Single(m => owner >= m.FirstType && owner < m.FirstType + m.TypeCount);
        if (!maps.ContainsKey(image))
        {
            var map = new Dictionary<int, int>();
            for (int i = image.FirstType; i < image.FirstType + image.TypeCount; i++)
            {
                var t = facts.Model.Types[i];
                map.Add((int)t.Token, i);
                for (int j = t.FirstMethod; j < t.FirstMethod + t.MethodCount; j++) map.Add((int)facts.Model.Methods[j].Token, j);
                for (int j = t.FirstField; j < t.FirstField + t.FieldCount; j++) map.Add((int)facts.Model.Fields[j].Token, j);
            }
            maps.Add(image, map);
        }
        return new(this, facts, image, caller);
    }
}

internal sealed partial class SrmMetadata
{
    /// <summary>方法体字节交给 SRM 解码。新增的局部签名登记在本次写出的 StandAloneSig 表中。</summary>
    internal static MethodBody SampleBody(ManagedBody input, ModelMetadata facts, DefinitionTokens.Scope tokens, Action written)
    {
        var tables = new MetadataBuilder();
        tables.AddModule(0, tables.GetOrAddString("CIL"), default, default, default);
        int Register(ImmutableArray<byte> blob) =>
            MetadataTokens.GetToken(tables.AddStandaloneSignature(tables.GetOrAddBlob(blob)));
        var result = CilWriter.Write(input, tokens, facts, Register, e => EncodeType(facts, input.Host.Entity, e, tokens.Definition));
        var body = result.Body ?? throw new InvalidDataException(result.Reason);
        written();
        var bytes = tables.GetOrAddBlob(body.Bytes);
        var data = new BlobBuilder();
        new MetadataRootBuilder(tables).Serialize(data, 0, 0);
        using var storage = MetadataReaderProvider.FromMetadataImage(data.ToImmutableArray());
        var reader = storage.GetMetadataReader();
        var blobReader = reader.GetBlobReader(bytes);
        var block = MethodBodyBlock.Create(blobReader);
        if (block.Size != body.Bytes.Length) throw new InvalidDataException("方法头中的长度与写出字节不一致");
        var provider = new Provider(facts, h => tokens.Index(MetadataTokens.GetToken(h)), h => throw Unresolved($"缺少 TypeRef {h}"));
        var m = facts.Keys.DescribeMethod(input.Host.Entity)!;
        var scope = new Scope(new(facts.Model.Methods[m.Definition].Owner, m.TypeArguments), m);
        ImmutableArray<TypeShape> locals = block.LocalSignature.IsNil ? [] :
            [.. reader.GetStandaloneSignature(block.LocalSignature).DecodeLocalSignature(provider, scope).Select(t => facts.Shape(t.Concrete))];
        var code = block.GetILContent();
        var instructions = IlDecoder.Decode(code.AsSpan());
        EmitChecks.Instructions(input, instructions, tokens);
        EmitChecks.Stack(instructions, tokens, facts, input.Host, block.MaxStack);
        return new(input.Host, locals, code, block.ExceptionRegions.Length, block.LocalVariablesInitialized)
            { InitializerOf = input.Host.IsTypeInitializer ? input.Host.DeclaringType : null };
    }
}
