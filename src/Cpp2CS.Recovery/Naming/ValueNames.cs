using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Naming;

public enum ValueKind { Unnamed, ManagedReference, RuntimePointer, FrameAddress, ImageAddress, ManagedAddress, Integer, Floating, NativePointer }
public abstract record ValueName;
public sealed record EntityName(MetadataEntity Entity, ulong Slot) : ValueName;
public sealed record ParameterName(int Index, TypeRef? StaticType, bool MethodInformation) : ValueName;
public sealed record CallResultName(CallIdentity Call, TypeRef? StaticType, string? Operation) : ValueName;
public sealed record FieldName(ValueName Owner, string Record, string Field, long? Index = null) : ValueName;
public sealed record BitStorageName(ValueName Owner, string Record, string Fields) : ValueName;
public sealed record AddressName(Term Address) : ValueName;
public sealed record NamedValue(ValueKind Kind, ValueName? Name, string? Record = null, Reason? Why = null)
{
    public static NamedValue Unknown(string code, string message) => new(ValueKind.Unnamed, null, Why: new(code, message));
}

/// <summary>名字保存实体、定义或规格字段依据；不向项表写入替代项，不改写快照。</summary>
public sealed class ValueNamingQuery(StateQueries state, CallNamingQuery calls, NamingFacts facts, RuntimeSpec spec,
    MethodBinder binder, SignatureBinding? entry = null) : Query<Term, NamedValue>
{
    public QueryContext CreateContext(NativeFunction function) => new(function, null, state.Group,
        new FixedPointGroup(1_000_000, FixedPointMember.Create(this, _ => new NameLattice())));
    private static Outcome<NamedValue> Yes(NamedValue value) => Outcome<NamedValue>.Success(value);
    public override Outcome<NamedValue> Compute(QueryContext c, Term key)
    {
        // 先处理签名绑定出的完整值（窄参数可以是入口槽的切片）。
        if (entry is not null)
            for (int i = 0; i < entry.Signature.Parameters.Length; i++)
            {
                var bound = binder.Parameter(entry, i, c.Snapshot.Terms, c.Snapshot.Inputs, c.Snapshot.IncomingArgumentArea);
                if (bound.Value?.Source is TermSource source && source.Term == key)
                {
                    var method = entry.Entry?.Method;
                    TypeRef? type = null;
                    if (method is not null && entry.Managed is { } managed)
                    {
                        int index = managed.ParameterIndices.IndexOf(i);
                        if (index >= 0) type = method.Concrete(method.Method.Parameters[index].Type);
                        else if (managed.ThisIndex == i) type = method.Method.Owner.IsValueType
                            ? new ByRefRef(new DefinitionRef(method.Method.Owner, method.TypeArguments))
                            : new DefinitionRef(method.Method.Owner, method.TypeArguments);
                    }
                    bool info = entry.Managed?.MethodInformationIndex == i;
                    return Yes(info ? new(ValueKind.RuntimePointer, new ParameterName(i, null, true), "MethodInfo")
                        : Typed(entry.Signature.Parameters[i], type, new ParameterName(i, type, false)));
                }
            }
        var resolved = c.Get(state.Resolve, key);
        if (!resolved.IsSuccess) return Yes(new(ValueKind.Unnamed, null, Why: resolved.Why));
        if (resolved.Value != key) return c.Get(this, resolved.Value);
        if (key.Identity is MemoryAtom memory) return Read(c, memory.Location);
        if (key.Kind == TermKind.Slice && key.Operands[0].Identity is MemoryAtom bits)
            return Read(c, bits.Location with { Width = key.Width }, key.SliceLow!.Value);
        if (key.Identity is MemoryMerge || key.Identity is ResultAtom { Definition: MergeIdentity }) return Merge(c, key);
        var definition = key.Identity as ResultAtom;
        if (key.Kind == TermKind.Slice) definition = key.Operands[0].Identity as ResultAtom;
        if (definition?.Definition is CallIdentity id)
        {
            var classified = c.Get(calls, id); if (!classified.IsSuccess) return classified.Propagate<NamedValue>();
            var call = classified.Value;
            if (call.Function is { } function && call.Result?.Source is TermSource result && result.Term == key)
            {
                if (function.Operation.Result.ReturnInput is { } input && call.Inputs?.GetValueOrDefault(input)?.Source is TermSource same)
                    return c.Get(this, same.Term);
                var name = new CallResultName(id, null, function.Operation.Name);
                return Yes(function.Operation.Result.Kind switch
                {
                    RuntimeValueKind.Class => new(ValueKind.RuntimePointer, name, "Il2CppClass"),
                    RuntimeValueKind.Method => new(ValueKind.RuntimePointer, name, "MethodInfo"),
                    RuntimeValueKind.Metadata => new(ValueKind.RuntimePointer, name),
                    RuntimeValueKind.ManagedReference => new(ValueKind.ManagedReference, name, "Il2CppObject"),
                    RuntimeValueKind.Integer or RuntimeValueKind.Boolean => new(ValueKind.Integer, name),
                    RuntimeValueKind.ManagedAddress => new(ValueKind.ManagedAddress, name),
                    _ => new(ValueKind.NativePointer, name)
                });
            }
            if (call.Candidates is { } candidates)
            {
                var names = candidates.Candidates.Select(candidate => candidate.Binding.Value is { } bound &&
                    bound.Result.Source is TermSource source && source.Term == key && candidate.Entry.Method is { } method
                    ? Typed(bound.Result.Type, method.Concrete(method.Method.ReturnType), new CallResultName(id, method.Concrete(method.Method.ReturnType), null))
                    : NamedValue.Unknown("naming.result-binding", "候选结果未完整绑定。")).Distinct().ToArray();
                if (names.Length == 1) return Yes(names[0]);
                return Yes(NamedValue.Unknown("naming.result-ambiguity", "候选方法的结果名字不一致。"));
            }
        }
        if (key.Width == c.Snapshot.AddressWidth)
        {
            var location = c.Get(state.Locations, new(key, 8));
            if (location.IsSuccess && location.Value.Region is Region.Frame or Region.Image)
                return Yes(new(location.Value.Region == Region.Frame ? ValueKind.FrameAddress : ValueKind.ImageAddress, new AddressName(key)));
        }
        return Yes(NamedValue.Unknown("naming.definition", "定义没有可用的签名或运行时规格名字。"));
    }
    private static NamedValue Typed(CType ctype, TypeRef? type, ValueName name)
    {
        if (type is not null && ManagedTypes.IsReferenceType(type)) return new(ValueKind.ManagedReference, name, type is ArrayRef ? "Il2CppArray" : ManagedTypes.PrimitiveName(type) == "String" ? "Il2CppString" : "Il2CppObject");
        if (type is ByRefRef) return new(ValueKind.ManagedAddress, name);
        return ctype switch
        {
            CInteger => new(ValueKind.Integer, name), CFloat => new(ValueKind.Floating, name), CPointer => new(ValueKind.NativePointer, name),
            _ => NamedValue.Unknown("naming.aggregate", "聚合值没有标量种类。")
        };
    }
    private Outcome<NamedValue> Merge(QueryContext c, Term key)
    {
        var pending = new Stack<Term>(); var seen = new HashSet<Term>(); var names = new HashSet<NamedValue>(); pending.Push(key);
        while (pending.TryPop(out var term))
        {
            if (!seen.Add(term)) continue;
            if (c.Step() is { } why) return Outcome<NamedValue>.Failure(why);
            if (term.Identity is MemoryMerge memory)
            {
                var inputs = c.Get(state.MergeInputs, memory); if (!inputs.IsSuccess) return inputs.Propagate<NamedValue>();
                foreach (var input in inputs.Value) pending.Push(input.Value);
            }
            else if (term.Identity is ResultAtom { Definition: MergeIdentity id })
                foreach (var input in c.Snapshot.Blocks.SelectMany(b => b.Merges).Single(m => m.Identity == id).Inputs) pending.Push(input.Value);
            else
            {
                var value = c.Get(this, term); if (!value.IsSuccess) return value;
                if (value.Value != NameLattice.Pending) names.Add(value.Value);
            }
        }
        return Yes(names.Count == 0 ? NameLattice.Pending : names.Count == 1 ? names.Single() : NamedValue.Unknown("naming.merge", "合流输入没有一致名字。"));
    }
    private Outcome<NamedValue> Read(QueryContext c, Location location, int low = 0)
    {
        if (location.Region == Region.Image && location.Offset is { } offset && offset >= 0 && offset <= ulong.MaxValue &&
            low == 0 && location.Width == c.Snapshot.AddressWidth && facts.Slots.TryGetValue((ulong)offset, out var entity))
        {
            if (!entity.IsSuccess) return Yes(new(ValueKind.Unnamed, null, Why: entity.Why));
            var name = new EntityName(entity.Value, (ulong)offset);
            return Yes(entity.Value switch
            {
                ClassEntity => new(ValueKind.RuntimePointer, name, "Il2CppClass"),
                TypeEntity => new(ValueKind.RuntimePointer, name, "Il2CppType"),
                MethodEntity => new(ValueKind.RuntimePointer, name, "MethodInfo"),
                FieldEntity => new(ValueKind.RuntimePointer, name, "FieldInfo"),
                StringEntity => new(ValueKind.ManagedReference, name, "Il2CppString"),
                _ => NamedValue.Unknown("naming.entity", "未登记的实体种类。")
            });
        }
        if (location.Region != Region.Other || location.Offset is null)
            return Yes(NamedValue.Unknown("naming.read-region", "读取没有已命名的区域或定值偏移。"));
        var owner = c.Get(this, location.Root); if (!owner.IsSuccess) return owner;
        if (owner.Value == NameLattice.Pending) return owner;
        if (owner.Value.Name is not { } parent || owner.Value.Record is not { } record || !spec.Layout.Records.TryGetValue(record, out var layout))
            return Yes(NamedValue.Unknown("naming.read-base", "读取的基值没有运行时结构身份。"));
        var bitOffset = location.Offset.Value * 8 + low;
        var fields = layout.Fields.Values.Where(f => f.OffsetBits == bitOffset && (f.BitWidth ?? f.Size * 8) == location.Width).ToArray();
        // 对象头的联合以运行时对象的 klass 视图解释。
        if (record == "Il2CppObject" && fields.Any(f => f.Path == "Il2CppObject.klass"))
            return Yes(Field(parent, record, layout.Field("klass")));
        if (fields.Length == 1) return Yes(Field(parent, record, fields[0]));
        var bits = layout.Fields.Values.Where(f => f.BitWidth is not null && f.OffsetBits >= bitOffset && f.OffsetBits + f.BitWidth <= bitOffset + location.Width).OrderBy(f => f.OffsetBits).ToArray();
        if (bits.Length > 0 && bits.Sum(f => f.BitWidth!.Value) == location.Width)
            return Yes(new(ValueKind.Integer, new BitStorageName(parent, record, string.Join("|", bits.Select(f => f.Path)))));
        if (low == 0 && record == "Il2CppClass" && location.Offset >= spec.Layout.VtableStart)
        {
            long relative = checked((long)location.Offset.Value - spec.Layout.VtableStart);
            long index = relative / spec.Layout.VtableSlotSize;
            foreach (var field in spec.Layout.Record("VirtualInvokeData").Fields.Values)
                if (field.BitWidth is null && field.ByteOffset == relative % spec.Layout.VtableSlotSize && field.Size * 8 == location.Width)
                    return Yes(Field(new FieldName(parent, record, "vtable", index), "VirtualInvokeData", field));
        }
        return Yes(NamedValue.Unknown("naming.read-field", "访问范围不是唯一完整规格字段。"));
    }
    private NamedValue Field(ValueName owner, string record, RuntimeField field)
    {
        var name = new FieldName(owner, record, field.Path);
        var type = field.Type.Replace("const ", "", StringComparison.Ordinal).Replace("struct ", "", StringComparison.Ordinal).Trim();
        // il2cpp-api-types.h 与 il2cpp-class-internals.h 的函数指针别名。
        if (type is "Il2CppMethodPointer" or "InvokerMethod") return new(ValueKind.NativePointer, name);
        if (type.EndsWith('*'))
        {
            var pointee = type[..^1].Trim();
            var target = spec.Layout.Records.Values.SingleOrDefault(r => r.Type == pointee || r.Name == pointee);
            return new(ValueKind.RuntimePointer, name, target?.Name);
        }
        return new(ValueKind.Integer, name);
    }
}

/// <summary>未取得证据、小于唯一名字、小于冲突；高度为三，循环不会无限展开名字。</summary>
internal sealed class NameLattice : ILattice<NamedValue>
{
    internal static NamedValue Pending { get; } = NamedValue.Unknown("naming.pending", "循环尚无外部命名证据。");
    private static NamedValue Conflict { get; } = NamedValue.Unknown("naming.conflict", "循环或合流含不同名字。");
    public NamedValue Bottom => Pending;
    public NamedValue Join(NamedValue a, NamedValue b) => a == Pending ? b : b == Pending || a == b ? a : Conflict;
    public bool LessOrEqual(NamedValue a, NamedValue b) => a == Pending || a == b || (b.Kind == ValueKind.Unnamed && b != Pending);
}
