using System.Collections.Immutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Model;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Facts;

/// <summary>代码地图与布局给出的全局事实。映像、符号与元数据槽由调用方解释。</summary>
public sealed class ModelNativeFacts
{
    private readonly ModelMetadata metadata;
    private readonly CodeMap code;
    private readonly Dictionary<ulong, HashSet<EntityRef>> entries = [];
    private readonly Dictionary<EntityRef, HashSet<ulong>> generic = [];

    public ModelNativeFacts(ModelMetadata metadata, CodeMap code)
    {
        this.metadata = metadata;
        this.code = code;
        void Register(ulong address, EntityRef method)
        {
            if (!entries.TryGetValue(address, out var group)) entries[address] = group = [];
            group.Add(method);
        }
        for (int i = 0; i < code.Methods.Count; i++)
            if (code.Methods[i].Entry is ulong address) Register(address, new(EntityKind.Method, i));
        for (int i = 0; i < code.MethodInstances.Count; i++)
        {
            if (code.MethodInstances[i].Entry is not ulong address) continue;
            var entity = new EntityRef(EntityKind.Method, metadata.Keys.MethodKey(metadata.Model.MethodInstances[i])!.Value);
            Register(address, entity);
            if (!generic.TryGetValue(entity, out var addresses)) generic[entity] = addresses = [];
            addresses.Add(address);
        }
        // vm/MetadataCache.cpp::GetGenericMethodPointers、GetSharedInst：先取精确登记，再把引用实参替换为 Object。
        // 值类型的共享还依赖代码生成选项；不能确定该选项时保留未知。
        var objectType = metadata.CoreType("Object");
        var enumType = metadata.CoreType("Enum");
        TypeReference? Shared(TypeReference t)
        {
            if (t is ArrayType) return objectType;
            if (t is not NamedType n) return null;
            var definition = metadata.Model.Types[n.Definition];
            if (!definition.ValueType) return objectType;
            if (definition.Parent is NamedType parent && parent.Definition == enumType.Definition) return null;
            if (n.Arguments.Count == 0) return n;
            var arguments = SharedArguments(n.Arguments);
            return arguments == null ? null : n with { Arguments = arguments };
        }
        TypeReference[]? SharedArguments(IReadOnlyList<TypeReference> arguments)
        {
            var shared = new TypeReference[arguments.Count];
            for (int i = 0; i < shared.Length; i++)
            {
                if (Shared(arguments[i]) is not { } argument) return null;
                shared[i] = argument;
            }
            return shared;
        }
        foreach (var spec in metadata.Model.MethodInstances)
        {
            var method = new EntityRef(EntityKind.Method, metadata.Keys.MethodKey(spec)!.Value);
            if (generic.ContainsKey(method) || SharedArguments(spec.TypeArguments) is not { } typeArgs ||
                SharedArguments(spec.MethodArguments) is not { } methodArgs) continue;
            var shared = new MethodInstance(spec.Definition, typeArgs, methodArgs);
            if (metadata.Keys.MethodKey(shared) is not long key ||
                !generic.TryGetValue(new(EntityKind.Method, key), out var targets) || targets.Count != 1) continue;
            generic.Add(method, targets);
            Register(targets.Single(), method);
        }
    }

    public bool IsEntry(ulong address) => entries.ContainsKey(address);
    public ulong? Entry(EntityRef method) => method.Kind == EntityKind.Method && method.Key >= 0 && method.Key < code.Methods.Count
        ? code.Methods[(int)method.Key].Entry : null;

    public GenericEntry? GenericEntry(EntityRef method)
    {
        if (!generic.TryGetValue(method, out var addresses) || addresses.Count != 1) return null;
        ulong address = addresses.Single();
        return new(address, method, entries[address].Count > 1);
    }

    public bool RequiresMethodArgument(ulong address) => entries.TryGetValue(address, out var group) && group.Count > 1;

    public ImmutableArray<MethodShape> Signatures(ulong address, out string reason)
    {
        reason = "代码地图没有这个入口";
        if (!entries.TryGetValue(address, out var group)) return [];
        var signatures = ImmutableArray.CreateBuilder<MethodShape>(group.Count);
        foreach (var entity in group)
        {
            try { signatures.Add(metadata.Method(entity)); }
            catch (ExpansionException e) { reason = e.Message; return []; }
        }
        reason = "";
        return signatures.MoveToImmutable();
    }

    public int? Offset(EntityRef entity, FieldStorage storage, out string reason)
    {
        reason = $"字段 {entity} 没有 {storage} 偏移";
        if (metadata.Keys.DescribeField(entity) is not { } f) return null;
        try
        {
            var offset = metadata.FieldOffset(f.Index, f.Owner, storage);
            if (offset.HasValue) reason = "";
            return offset;
        }
        catch (ExpansionException e) { reason = e.Message; return null; }
    }
}
