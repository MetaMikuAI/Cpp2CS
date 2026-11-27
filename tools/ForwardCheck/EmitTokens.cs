using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Output;
using Cpp2CS.Snapshot;
using M = Cpp2CS.Model;

namespace Cpp2CS.Tools.ForwardCheck;

internal sealed partial class SrmMetadata
{
    /// <summary>记号只在当前模块和调用方的泛型上下文里反查；候选经正向解析后按完整实体匹配。</summary>
    internal sealed class EmitTokens(SrmMetadata metadata, Module module, EntityRef caller) : IEntityTokens
    {
        private readonly ITokenResolver resolver = metadata.Tokens(module, caller);
        private readonly Dictionary<EntityRef, int> found = [];

        public int Method(EntityRef entity) => Find(entity, resolver.Method, TableIndex.MethodDef, TableIndex.MemberRef, TableIndex.MethodSpec);
        public int Field(EntityRef entity) => Find(entity, resolver.Field, TableIndex.Field, TableIndex.MemberRef);
        public int Type(EntityRef entity) => Find(entity, resolver.Type, TableIndex.TypeDef, TableIndex.TypeRef, TableIndex.TypeSpec);

        private int Find(EntityRef entity, Func<int, EntityRef> resolve, params ReadOnlySpan<TableIndex> tables)
        {
            if (found.TryGetValue(entity, out int existing)) return existing;
            foreach (var table in tables)
            {
                for (int row = 1; row <= module.Md.GetTableRowCount(table); row++)
                {
                    var h = MetadataTokens.EntityHandle(table, row);
                    if (table == TableIndex.MemberRef && (entity.Kind == EntityKind.Method) !=
                        (module.Md.GetMemberReference((MemberReferenceHandle)h).GetKind() == MemberReferenceKind.Method)) continue;
                    int token = MetadataTokens.GetToken(h);
                    // 模块可能引用模型未登记的外部实体或泛型实例；这种行不能给所求实体作记号。
                    EntityRef candidate;
                    try { candidate = resolve(token); }
                    catch (ExpansionException) { continue; }
                    found.TryAdd(candidate, token);
                    if (candidate == entity) return token;
                }
            }
            throw Unresolved($"模块 {module.Image} 在调用方 {caller} 下没有可解析为 {entity} 的记号");
        }

        private EntityHandle DefinitionHandle(int index)
        {
            var definition = metadata.Definition(index);
            if (definition.Module == module) return definition.Handle;
            foreach (var h in module.Md.TypeReferences)
            {
                var reference = module.Md.GetTypeReference(h);
                if (!module.Md.StringComparer.Equals(reference.Name, metadata.Facts.Model.Types[index].Name)) continue;
                try { if (metadata.Resolve(module, h) == definition) return h; }
                catch (ExpansionException) { continue; }
            }
            throw Unresolved($"模块 {module.Image} 缺少类型定义 {index} 的 TypeRef");
        }

        public ImmutableArray<byte> TypeSignature(EntityRef entity) =>
            EncodeType(metadata.Facts, caller, entity, DefinitionHandle);
    }

    /// <summary>II.23.2.12。具名的基元取短编码，复合类型内嵌元素与实参，保留调用方的类型和方法参数作用域。</summary>
    internal static ImmutableArray<byte> EncodeType(Cpp2CS.Facts.ModelMetadata facts, EntityRef caller, EntityRef entity,
        Func<int, EntityHandle> definitionHandle)
    {
        if (entity.Kind != EntityKind.Type || (ulong)entity.Key >= (ulong)facts.Model.RuntimeTypes.Count)
            throw Unresolved($"局部变量类型实体 {entity}");
        var type = facts.Model.RuntimeTypes[(int)entity.Key];
        var blob = new BlobBuilder();
        WriteType(type is M.ReferenceType reference ? reference.Element : type);
        return blob.ToImmutableArray();

        void WriteType(M.TypeReference t)
        {
            switch (t)
            {
                case M.NamedType named:
                    var d = facts.Model.Types[named.Definition];
                    if (named.Arguments.Count == 0 && d.Namespace == "System"
                        && Enum.TryParse<PrimitiveTypeCode>(d.Name, out var primitive) && primitive.ToString() == d.Name
                        && facts.CoreType(d.Name).Definition == named.Definition)
                    {
                        blob.WriteByte((byte)primitive);
                        return;
                    }
                    if (named.Arguments.Count > 0) blob.WriteByte((byte)SignatureTypeCode.GenericTypeInstance);
                    blob.WriteByte(d.ValueType ? (byte)0x11 : (byte)0x12);
                    blob.WriteCompressedInteger(CodedIndex.TypeDefOrRef(definitionHandle(named.Definition)));
                    if (named.Arguments.Count > 0)
                    {
                        blob.WriteCompressedInteger(named.Arguments.Count);
                        foreach (var argument in named.Arguments) WriteType(argument);
                    }
                    break;
                case M.ArrayType array:
                    blob.WriteByte((byte)(array.Vector ? SignatureTypeCode.SZArray : SignatureTypeCode.Array));
                    WriteType(array.Element);
                    if (!array.Vector)
                    {
                        blob.WriteCompressedInteger(array.Rank);
                        blob.WriteCompressedInteger(0);
                        blob.WriteCompressedInteger(0);
                    }
                    break;
                case M.PointerType pointer:
                    blob.WriteByte((byte)SignatureTypeCode.Pointer);
                    WriteType(pointer.Element);
                    break;
                case M.VariableType variable:
                    var context = facts.Keys.DescribeMethod(caller) ?? throw Unresolved($"调用方 {caller}");
                    if (variable.Owner != (variable.Method ? context.Definition : facts.Model.Methods[context.Definition].Owner))
                        throw Unresolved("泛型形参的作用域与写出方法不符");
                    blob.WriteByte((byte)(variable.Method ? SignatureTypeCode.GenericMethodParameter : SignatureTypeCode.GenericTypeParameter));
                    blob.WriteCompressedInteger(variable.Position);
                    break;
                default: throw Unresolved($"局部变量元素类型 {t}");
            }
        }
    }
}
