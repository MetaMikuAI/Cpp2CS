using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using Cpp2CS.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using M = Cpp2CS.Model;
using MethodBody = Cpp2CS.Kernel.Forward.MethodBody;
using System.Reflection.PortableExecutable;

namespace Cpp2CS.Tools.ForwardCheck;

internal sealed partial class SrmMetadata
{
    private static int Index(Dictionary<(string Image, int Token), int> table, Module module, EntityHandle handle) =>
        table.TryGetValue((module.Image, MetadataTokens.GetToken(handle)), out int index) ? index :
        throw Unresolved($"{module.Image} 记号 0x{MetadataTokens.GetToken(handle):x8} 在模型中没有定义");

    // II.23.2：比较完整签名（含调用约定、返回类型、泛型元数、修饰符与数组形状）。
    // 泛型参数在签名里按位置区分。解析具体实例时再代入所属类型和方法的实参。
    private sealed record Sig(string Identity, M.TypeReference? Value)
    {
        public M.TypeReference Concrete => Value ?? throw Unresolved($"签名 {Identity} 没有模型表示");
    }

    private sealed record Scope(M.NamedType Type, M.MethodInstance Method)
    {
        public M.TypeReference? Parameter(bool method, int index)
        {
            var args = method ? Method.MethodArguments : Type.Arguments;
            if (index < args.Count) return args[index];
            return new M.VariableType(-1, method, method ? Method.Definition : Type.Definition, index);
        }
    }

    private Scope? Context(EntityRef? entity)
    {
        if (entity == null) return null;
        var m = Facts.Keys.DescribeMethod(entity.Value) ?? throw Unresolved($"调用方实体 {entity}");
        return new(new(Facts.Model.Methods[m.Definition].Owner, m.TypeArguments), m);
    }

    private sealed class Provider(SrmMetadata owner, Module module) : ISignatureTypeProvider<Sig, Scope?>
    {
        private Sig Named(int i) => new($"D{i}", new M.NamedType(i, []));
        public Sig GetPrimitiveType(PrimitiveTypeCode code) => Named(owner.Facts.CoreType(code.ToString()).Definition);
        public Sig GetTypeFromDefinition(MetadataReader reader, TypeDefinitionHandle h, byte kind) => Named(Index(owner.types, module, h));
        public Sig GetTypeFromReference(MetadataReader reader, TypeReferenceHandle h, byte kind)
        {
            var (target, handle) = owner.Resolve(module, h);
            return Named(Index(owner.types, target, handle));
        }
        public Sig GetTypeFromSpecification(MetadataReader r, Scope? c, TypeSpecificationHandle h, byte kind) =>
            r.GetTypeSpecification(h).DecodeSignature(this, c);
        public Sig GetGenericInstantiation(Sig definition, ImmutableArray<Sig> args) =>
            new($"{definition.Identity}<{string.Join(",", args.Select(a => a.Identity))}>",
                definition.Value is M.NamedType n && args.All(a => a.Value != null) ? n with { Arguments = args.Select(a => a.Concrete).ToArray() } : null);
        public Sig GetGenericMethodParameter(Scope? c, int index) => new($"!!{index}", c?.Parameter(true, index));
        public Sig GetGenericTypeParameter(Scope? c, int index) => new($"!{index}", c?.Parameter(false, index));
        public Sig GetSZArrayType(Sig element) => new(element.Identity + "[]", element.Value is { } e ? new M.ArrayType(e, 1, true) : null);
        public Sig GetArrayType(Sig element, ArrayShape s) =>
            new($"{element.Identity}[{s.Rank}:{string.Join(",", s.Sizes)}:{string.Join(",", s.LowerBounds)}]",
                element.Value is { } e && s.Sizes.IsEmpty && s.LowerBounds.All(i => i == 0) ? new M.ArrayType(e, s.Rank, false) : null);
        public Sig GetPointerType(Sig e) => new(e.Identity + "*", e.Value is { } v ? new M.PointerType(v) : null);
        public Sig GetByReferenceType(Sig e) => new(e.Identity + "&", e.Value is { } v ? new M.ReferenceType(v) : null);
        public Sig GetModifiedType(Sig modifier, Sig type, bool required) => new($"{(required ? "req" : "opt")}({modifier.Identity}){type.Identity}", type.Value);
        public Sig GetPinnedType(Sig type) => new($"pinned({type.Identity})", type.Value);
        public Sig GetFunctionPointerType(MethodSignature<Sig> signature) => new("fn" + Signature(signature), null);
    }

    private static string Signature(MethodSignature<Sig> s) =>
        $"{s.Header.RawValue}:{s.GenericParameterCount}:{s.RequiredParameterCount}:{s.ReturnType.Identity}({string.Join(",", s.ParameterTypes.Select(p => p.Identity))})";

    private Sig ReadType(Module module, EntityHandle h, Scope? scope)
    {
        var p = new Provider(this, module);
        return h.Kind switch
        {
            HandleKind.TypeDefinition => p.GetTypeFromDefinition(module.Md, (TypeDefinitionHandle)h, 0),
            HandleKind.TypeReference => p.GetTypeFromReference(module.Md, (TypeReferenceHandle)h, 0),
            HandleKind.TypeSpecification => p.GetTypeFromSpecification(module.Md, scope, (TypeSpecificationHandle)h, 0),
            _ => throw Unresolved($"类型记号 {h.Kind}"),
        };
    }

    private (Module Module, TypeDefinitionHandle Handle) Definition(int index)
    {
        var image = Facts.Model.Images.Single(i => index >= i.FirstType && index < i.FirstType + i.TypeCount);
        var target = LoadImage(image.Name) ?? throw Unresolved($"模块 {image.Name}");
        return (target, (TypeDefinitionHandle)MetadataTokens.EntityHandle((int)Facts.Model.Types[index].Token));
    }

    private (int Index, M.NamedType Owner) ResolveMember(Module module, MemberReferenceHandle handle, bool method, Scope? scope)
    {
        var r = module.Md.GetMemberReference(handle);
        if ((r.GetKind() == MemberReferenceKind.Method) != method) throw Unresolved("成员引用的种类不符");
        if (ReadType(module, r.Parent, scope).Concrete is not M.NamedType parent) throw Unresolved("成员所属类型没有定义");
        string name = module.Md.GetString(r.Name);
        var p = new Provider(this, module);
        string wanted = method ? Signature(r.DecodeMethodSignature(p, null)) : r.DecodeFieldSignature(p, null).Identity;
        var visited = new HashSet<int>();
        // ECMA-335 I.8.10.2：本类型没有匹配的成员时，继续查其基类。
        while (visited.Add(parent.Definition))
        {
            var (target, h) = Definition(parent.Definition);
            var d = target.Md.GetTypeDefinition(h);
            var provider = new Provider(this, target);
            var matches = new List<int>();
            if (method)
                foreach (var m in d.GetMethods())
                {
                    var candidate = target.Md.GetMethodDefinition(m);
                    if (target.Md.GetString(candidate.Name) == name && Signature(candidate.DecodeSignature(provider, null)) == wanted)
                        matches.Add(Index(methods, target, m));
                }
            if (!method)
                foreach (var f in d.GetFields())
                {
                    var candidate = target.Md.GetFieldDefinition(f);
                    if (target.Md.GetString(candidate.Name) == name && candidate.DecodeSignature(provider, null).Identity == wanted)
                        matches.Add(Index(fields, target, f));
                }
            if (matches.Count == 1) return (matches[0], parent);
            if (matches.Count > 1) throw Unresolved($"成员 {name} 有多个匹配的定义");
            if (name is ".ctor" or ".cctor" || Facts.Model.Types[parent.Definition].Parent is not { } baseType ||
                EntityKeys.Inflate(baseType, parent) is not M.NamedType next) break;
            parent = next;
        }
        throw Unresolved($"没有匹配签名的成员 {name} {wanted}");
    }

    public ITokenResolver Tokens(Module module, EntityRef? caller = null) => new Resolver(this, module, Context(caller));
    private sealed class Resolver(SrmMetadata srm, Module module, Scope? scope) : ITokenResolver
    {
        public EntityRef Type(int token) => srm.Facts.TypeEntity(srm.ReadType(module, MetadataTokens.EntityHandle(token), scope).Concrete);
        public EntityRef Field(int token)
        {
            var h = MetadataTokens.EntityHandle(token);
            if (h.Kind == HandleKind.FieldDefinition)
            {
                int field = Index(srm.fields, module, h);
                var receiver = scope?.Type;
                return receiver != null && receiver.Definition == srm.Facts.Model.Fields[field].Owner
                    ? new(EntityKind.Field, srm.Facts.Keys.FieldKey(field, receiver) ?? throw Unresolved("字段的所属实例没有 Key"))
                    : new(EntityKind.Field, field);
            }
            if (h.Kind != HandleKind.MemberReference) throw Unresolved($"字段记号 {h.Kind}");
            var (i, owner) = srm.ResolveMember(module, (MemberReferenceHandle)h, false, scope);
            return new(EntityKind.Field, srm.Facts.Keys.FieldKey(i, owner) ?? throw Unresolved($"字段 {i} 的所属实例没有 Key"));
        }
        public EntityRef Method(int token)
        {
            var h = MetadataTokens.EntityHandle(token);
            IReadOnlyList<M.TypeReference> args = [];
            if (h.Kind == HandleKind.MethodSpecification)
            {
                var spec = module.Md.GetMethodSpecification((MethodSpecificationHandle)h);
                args = spec.DecodeSignature(new Provider(srm, module), scope).Select(a => a.Concrete).ToArray();
                h = spec.Method;
            }
            int i;
            IReadOnlyList<M.TypeReference> owner = [];
            if (h.Kind == HandleKind.MethodDefinition)
            {
                i = Index(srm.methods, module, h);
                if (scope?.Type.Definition == srm.Facts.Model.Methods[i].Owner) owner = scope.Type.Arguments;
            }
            else if (h.Kind == HandleKind.MemberReference)
            {
                var result = srm.ResolveMember(module, (MemberReferenceHandle)h, true, scope);
                i = result.Index;
                owner = result.Owner.Arguments;
            }
            else throw Unresolved($"方法记号 {h.Kind}");
            if (owner.Count == 0 && args.Count == 0) return new(EntityKind.Method, i);
            return new(EntityKind.Method, srm.Facts.Keys.MethodKey(new M.MethodInstance(i, owner, args)) ?? throw Unresolved($"方法 {i} 的实例未登记"));
        }
    }

    // 从托管映像取同一无参方法在两个不同所属实例上的引用。先用定义坐标选择反例，再交给记号解析器。
    public (Module Module, int First, int Second)? GenericMemberPair()
    {
        foreach (var image in Facts.Model.Images)
        {
            var module = LoadImage(image.Name);
            if (module == null) continue;
            var seen = new Dictionary<int, (long Owner, int Token)>();
            foreach (var h in module.Md.MemberReferences)
            {
                var r = module.Md.GetMemberReference(h);
                if (r.Parent.Kind != HandleKind.TypeSpecification || r.GetKind() != MemberReferenceKind.Method) continue;
                var sig = r.DecodeMethodSignature(new Provider(this, module), default(Scope));
                if (!sig.ParameterTypes.IsEmpty || sig.GenericParameterCount != 0) continue;
                if (ReadType(module, r.Parent, null).Value is not M.NamedType { Arguments.Count: > 0 } owner ||
                    Facts.Keys.TypeKey(owner) is not long ownerKey) continue;
                var (target, typeHandle) = Definition(owner.Definition);
                string name = module.Md.GetString(r.Name);
                var matches = target.Md.GetTypeDefinition(typeHandle).GetMethods().Where(candidate =>
                {
                    var m = target.Md.GetMethodDefinition(candidate);
                    return target.Md.GetString(m.Name) == name && Signature(m.DecodeSignature(new Provider(this, target), default(Scope))) == Signature(sig);
                }).ToArray();
                if (matches.Length != 1) continue;
                int definition = Index(methods, target, matches[0]);
                if (Facts.Keys.MethodKey(new M.MethodInstance(definition, owner.Arguments, [])) == null) continue;
                int token = MetadataTokens.GetToken(h);
                if (seen.TryGetValue(definition, out var previous) && previous.Owner != ownerKey) return (module, previous.Token, token);
                seen[definition] = (ownerKey, token);
            }
        }
        return null;
    }

    public MethodBody Body(Module module, int token)
    {
        var h = MetadataTokens.EntityHandle(token);
        if (h.Kind != HandleKind.MethodDefinition) throw Unresolved("方法体需要定义记号");
        var m = module.Md.GetMethodDefinition((MethodDefinitionHandle)h);
        var entity = Tokens(module).Method(token);
        return ReadBody(module, m, Facts.Method(entity), Context(entity));
    }

    public EntityRef SignatureFieldType(Module module, FieldDefinitionHandle h) => Facts.TypeEntity(module.Md.GetFieldDefinition(h)
        .DecodeSignature(new Provider(this, module), default(Scope)).Concrete);

    // InitLocals 的 CLR 夹具只有静态无参方法，签名与方法头均读取夹具本身。
    public MethodBody FixtureBody(Module module, MethodDefinitionHandle h)
    {
        var m = module.Md.GetMethodDefinition(h);
        var s = m.DecodeSignature(new Provider(this, module), default(Scope));
        if (s.Header.IsInstance || !s.ParameterTypes.IsEmpty) throw Unresolved("局部初始化夹具的签名");
        return ReadBody(module, m, new(default, false, [], Facts.Shape(s.ReturnType.Concrete), Cpp2CS.Spec.Catalog.VariantCondition.StaticMethod));
    }

    private MethodBody ReadBody(Module module, MethodDefinition m, MethodShape method, Scope? scope = null)
    {
        if (m.RelativeVirtualAddress == 0) throw new ExpansionException("方法没有方法体", "");
        var block = module.Pe.GetMethodBody(m.RelativeVirtualAddress);
        ImmutableArray<TypeShape> locals = block.LocalSignature.IsNil ? [] :
            [.. module.Md.GetStandaloneSignature(block.LocalSignature).DecodeLocalSignature(new Provider(this, module), scope).Select(t => Facts.Shape(t.Concrete))];
        return new(method, locals, block.GetILContent(), block.ExceptionRegions.Length, block.LocalVariablesInitialized)
            { InitializerOf = method.IsTypeInitializer ? method.DeclaringType : null };
    }
}
