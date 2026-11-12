using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Naming;

public enum ValueKind { Unnamed, ManagedReference, RuntimePointer, FrameAddress, ImageAddress, ManagedAddress, Integer, Floating, NativePointer }
public abstract record ValueName;
public sealed record EntityName(MetadataEntity Entity, ulong? Slot) : ValueName;
public sealed record ParameterName(int Index, TypeRef? StaticType, bool MethodInformation) : ValueName;
public sealed record CallResultName(CallIdentity Call, TypeRef? StaticType, string? Operation) : ValueName;
/// <summary>身份沿用读取项；声明类型不证明不同读取同值。</summary>
public sealed record LoadedName(Term Read, TypeRef StaticType) : ValueName;
/// <summary>原生异常头、载荷与托管异常分别命名，不把头指针当作托管引用。</summary>
public sealed record ExceptionPointerName(BlockIdentity Handler) : ValueName;
public sealed record ExceptionPayloadName(BlockIdentity Handler) : ValueName;
public sealed record CaughtExceptionName(BlockIdentity Handler, TypeRef? StaticType) : ValueName;
public sealed record FieldName(ValueName Owner, string Record, string Field, long? Index = null) : ValueName;
/// <summary>规格数组字段的元素；下标保留为项，不改变读取位置。</summary>
public sealed record ArrayElementName(FieldName Array, Term Index) : ValueName;
public sealed record BitStorageName(ValueName Owner, string Record, string Fields) : ValueName;
public sealed record AddressName(Term Address) : ValueName;
public sealed record NamedValue(ValueKind Kind, ValueName? Name, string? Record = null, Reason? Why = null)
{
    public static NamedValue Unknown(string code, string message, Reason? cause = null) => new(ValueKind.Unnamed, null, Why: new(code, message, cause));
    public TypeRef? StaticType => Name switch
    { ParameterName p => p.StaticType, CallResultName r => r.StaticType, LoadedName r => r.StaticType, CaughtExceptionName e => e.StaticType, _ => null };
}

/// <summary>名字保存实体、定义或规格字段依据；不向项表写入替代项，不改写快照。</summary>
public sealed partial class ValueNamingQuery(StateQueries state, CallNamingQuery calls, NamingFacts facts, RuntimeSpec spec,
    MethodBinder binder, SignatureBinding? entry = null, IRgctxDecoder? rgctx = null, GenericWitness? witness = null,
    TypeRef? exceptionType = null, IReadOnlyDictionary<BlockIdentity, TypeRef>? caughtTypes = null) : Query<Term, NamedValue>
{
    /// <summary>区域查询已证明的 catch 类型作为查询视图；不改写异常对象身份。</summary>
    public ValueNamingQuery WithCaughtTypes(IReadOnlyDictionary<BlockIdentity, TypeRef> types) =>
        new(state, calls, facts, spec, binder, entry, rgctx, witness, exceptionType, types.ToImmutableDictionary());
    internal RuntimeSpec Spec => spec;
    internal MethodBinder Binder => binder;
    private readonly RuntimeInputKindsQuery inputKinds = new(state,calls);
    private ManagedLocationQuery? locations;
    internal SpecificationReadQuery SpecificationReads { get; } = new();
    internal void UseLocations(ManagedLocationQuery query)
    {
        if (locations is not null) throw new InvalidOperationException("命名查询已绑定托管位置查询。");
        locations = query;
    }
    internal FixedPointMember[] Members => [FixedPointMember.Create(this, _ => new NameLattice()),
        FixedPointMember.Create(SpecificationReads, _ => new NameLattice())];
    public QueryContext CreateContext(NativeFunction function) => locations is not null ? locations.CreateContext(function)
        : new(function, null, state.Group, new FixedPointGroup(1_000_000, Members));
    private static Outcome<NamedValue> Yes(NamedValue value) => Outcome<NamedValue>.Success(value);
    public override Outcome<NamedValue> Compute(QueryContext c, Term key)
    {
        var result=Definition(c,key);
        if (!result.IsSuccess || result.Value.Kind!=ValueKind.Unnamed) return result;
        var resolved=c.Get(state.Resolve,key); if (!resolved.IsSuccess) return result;
        var inputs=c.Get(inputKinds,0); if (!inputs.IsSuccess) return inputs.Propagate<NamedValue>();
        if (inputs.Value.TryGetValue(resolved.Value,out var kind))
            return Yes(RuntimeValue(kind,new RuntimeInputName(resolved.Value,kind)));
        // 托管读取只补充此前所有命名来源均未命名的值。
        var value=resolved.Value;
        if (value.Identity is MemoryAtom memory) return Read(c, value, memory.Location);
        if (value.Identity is EdgeReadAtom projected) return Read(c, value, projected.Location);
        if (value.Kind == TermKind.Slice && value.Operands[0].Identity is MemoryAtom bits)
            return Read(c, value, bits.Location with { Width=value.Width }, value.SliceLow!.Value);
        return result;
    }

    private Outcome<NamedValue> Definition(QueryContext c, Term key)
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
        if (key.Identity is ExceptionAtom exception)
            return Yes(new(ValueKind.NativePointer, new ExceptionPointerName(exception.Handler)));
        if (key.Identity is MemoryAtom memory) return c.Get(SpecificationReads, new(this, memory.Location));
        if (key.Identity is EdgeReadAtom projected) return c.Get(SpecificationReads, new(this, projected.Location));
        if (key.Kind == TermKind.Slice && key.Operands[0].Identity is MemoryAtom bits)
            return c.Get(SpecificationReads, new(this, bits.Location with { Width = key.Width }, key.SliceLow!.Value));
        if (key.Identity is MemoryMerge || key.Identity is ResultAtom { Definition: MergeIdentity }) return Merge(c, key);
        var definition = key.Identity as ResultAtom;
        if (key.Kind == TermKind.Slice) definition = key.Operands[0].Identity as ResultAtom;
        if (definition?.Definition is CallIdentity id)
        {
            var classified = c.Get(calls, id); if (!classified.IsSuccess) return classified.Propagate<NamedValue>();
            var call = classified.Value;
            if (call.Function is { } function && call.Result?.Source is TermSource result && result.Term == key)
            {
                if (function.Operation.Name is "BeginCatch" or "CxxGetExceptionPointer"
                    && call.Inputs?.GetValueOrDefault("exception")?.Source is TermSource native)
                {
                    var pointer = c.Get(this, native.Term);
                    if (!pointer.IsSuccess) return pointer;
                    if (pointer.Value.Name is ExceptionPointerName caught)
                        return Yes(new(ValueKind.RuntimePointer, new ExceptionPayloadName(caught.Handler), "Il2CppExceptionWrapper"));
                }
                if (function.Operation.Result.ReturnInput is { } input && call.Inputs?.GetValueOrDefault(input)?.Source is TermSource same)
                    return c.Get(this, same.Term);
                // 结果是某个类输入的实例时，静态类型取该类的实体；类还没有名字时结果照旧不带类型。
                TypeRef? instance = null;
                if (function.Operation.Result.Relation is { Kind: RuntimeResultRelationKind.InstanceOfInput, Input: { } classInput }
                    && call.Inputs?.GetValueOrDefault(classInput)?.Source is TermSource classTerm)
                {
                    var klass = c.Get(this, classTerm.Term); if (!klass.IsSuccess) return klass.Propagate<NamedValue>();
                    if (klass.Value == NameLattice.Pending) return Yes(NameLattice.Pending);
                    instance = klass.Value.Name is EntityName { Entity: ClassEntity { Type: var type } } ? type : null;
                }
                var name = new CallResultName(id, instance, function.Operation.Name);
                if (instance is not null) return Yes(Typed(null, instance, name));
                return Yes(RuntimeValue(function.Operation.Result.Kind,name));
            }
            if (call.Candidates is { } candidates)
            {
                if (witness is not null && candidates.Candidates.Any(x => x.Entry.Kind == BindingEntryKind.SharedGeneric))
                {
                    var target = c.Get(sharedResults ??= new(binder, calls, this, new(state)), id);
                    if (!target.IsSuccess) return Yes(new(ValueKind.Unnamed, null, Why: target.Why));
                    var bound = target.Value.Binding;
                    var method = target.Value.Method;
                    var type = method.Concrete(method.Method.ReturnType);
                    return Yes(bound.Result.Source is TermSource output && output.Term == key
                        ? Typed(bound.Result.Type, type, new CallResultName(id, type, null))
                        : NamedValue.Unknown("naming.result-binding", "共享调用结果未完整绑定。"));
                }
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
        // 消息里写明项的种类，报告才能按种类归并（原子取类型名，不带地址与编号）。
        var shape = key.Identity is { } atom ? atom.GetType().Name : key.Operator is { } op ? op.Name : key.Kind.ToString();
        return Yes(NamedValue.Unknown("naming.definition", "定义没有可用的签名或运行时规格名字：" + shape + "/" + key.Width));
    }
    private static NamedValue RuntimeValue(RuntimeValueKind kind, ValueName name) => kind switch
    {
        RuntimeValueKind.Class => new(ValueKind.RuntimePointer,name,"Il2CppClass"),
        RuntimeValueKind.Method => new(ValueKind.RuntimePointer,name,"MethodInfo"),
        RuntimeValueKind.Metadata => new(ValueKind.RuntimePointer,name),
        RuntimeValueKind.ManagedReference => new(ValueKind.ManagedReference,name,"Il2CppObject"),
        RuntimeValueKind.Integer or RuntimeValueKind.Boolean => new(ValueKind.Integer,name),
        RuntimeValueKind.ManagedAddress => new(ValueKind.ManagedAddress,name),
        _ => new(ValueKind.NativePointer,name)
    };
    private static NamedValue Typed(CType? ctype, TypeRef? type, ValueName name)
    {
        if (type is not null && ManagedTypes.IsReferenceType(type))
        {
            // 签名值保留既有结构身份，避免改变其规格字段名字；新增读取按声明类型选择字符串结构。
            bool text = ctype is null && type is DefinitionRef { Definition.Assembly: "mscorlib.dll", Definition.FullName: "System.String" };
            return new(ValueKind.ManagedReference, name, type is ArrayRef ? "Il2CppArray" : text ? "Il2CppString" : "Il2CppObject");
        }
        if (type is GenericParameterRef) return new(ValueKind.NativePointer, name);
        if (type is ByRefRef) return new(ValueKind.ManagedAddress, name);
        if (ctype is null && type is not null)
        {
            var scalar = ManagedTypes.Underlying(type);
            if (ManagedTypes.IsNativePointer(scalar)) return new(ValueKind.NativePointer, name);
            return ManagedTypes.PrimitiveName(scalar) switch
            {
                "Single" or "Double" => new(ValueKind.Floating, name),
                "Boolean" or "Char" or "SByte" or "Byte" or "Int16" or "UInt16" or "Int32" or "UInt32" or "Int64" or "UInt64" => new(ValueKind.Integer, name),
                _ => NamedValue.Unknown("naming.aggregate", "聚合值没有标量种类。")
            };
        }
        return ctype switch
        {
            CInteger => new(ValueKind.Integer, name), CFloat => new(ValueKind.Floating, name), CPointer => new(ValueKind.NativePointer, name),
            _ => NamedValue.Unknown("naming.aggregate", "聚合值没有标量种类。")
        };
    }
    private Outcome<NamedValue> Merge(QueryContext c, Term key)
    {
        var pending = new Stack<Term>(); var seen = new HashSet<Term>(); var names = new HashSet<NamedValue>(); var leaves = new HashSet<Term>(); pending.Push(key);
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
                if (value.Value != NameLattice.Pending)
                {
                    var resolved = c.Get(state.Resolve, term);
                    if (!resolved.IsSuccess) return resolved.Propagate<NamedValue>();
                    leaves.Add(resolved.Value);
                    var fixedName = FixedName(value.Value.Name);
                    names.Add(fixedName is null ? value.Value : value.Value with { Name = fixedName });
                }
            }
        }
        if (names.Count == 1 && leaves.Count > 1 && names.Single().Name is FieldName or ArrayElementName
            && FixedName(names.Single().Name) is null)
            return Yes(NamedValue.Unknown("naming.merge", "同名可变位置的不同读取版本没有同值凭据。"));
        return Yes(names.Count == 0 ? NameLattice.Pending : names.Count == 1 ? names.Single() : NamedValue.Unknown("naming.merge", "合流输入没有一致名字。"));
    }
    private Outcome<NamedValue> Read(QueryContext c, Term key, Location location, int low = 0)
    {
        var specification = c.Get(SpecificationReads, new(this, location, low));
        if (!specification.IsSuccess || specification.Value.Kind != ValueKind.Unnamed || specification.Value == NameLattice.Pending || locations is null || location.Region != Region.Other) return specification;
        if (low % 8 != 0) return specification;
        var request = ManagedReadTypeQuery.Address(c, location, low / 8);
        if (request is null) return specification;
        var located = c.Get(locations, request.Value);
        if (!located.IsSuccess) return located.Propagate<NamedValue>();
        if (located.Value.Kind is not (ManagedLocationKind.InstanceField or ManagedLocationKind.StaticField or ManagedLocationKind.ArrayElement or ManagedLocationKind.Unknown))
            return specification;
        var typed = c.Get(locations.ReadTypes, request.Value);
        if (!typed.IsSuccess) return Yes(NamedValue.Unknown("naming.read-location", "读取没有唯一完整托管位置类型。", typed.Why));
        if (typed.Value is null) return Yes(NameLattice.Pending);
        return Yes(Typed(null, typed.Value.Type, new LoadedName(key, typed.Value.Type)));
    }
    internal readonly record struct SpecificationRead(ValueNamingQuery Names, Location Location, int Low = 0);
    internal sealed class SpecificationReadQuery : Query<SpecificationRead, NamedValue>
    {
        public override Outcome<NamedValue> Compute(QueryContext c, SpecificationRead key) => key.Names.ReadSpecification(c, key.Location, key.Low);
    }
    private Outcome<NamedValue> ReadSpecification(QueryContext c, Location location, int low)
    {
        if (location.Region == Region.Image && location.Offset is { } offset && offset >= 0 && offset <= ulong.MaxValue &&
            low == 0 && location.Width == c.Snapshot.AddressWidth && facts.Slots.TryGetValue((ulong)offset, out var entity))
        {
            if (!entity.IsSuccess) return Yes(new(ValueKind.Unnamed, null, Why: entity.Why));
            return Yes(Entity(entity.Value, (ulong)offset));
        }
        if (low == 0 && location.Region == Region.Other && ReadSpecificationElement(c, location) is { } element) return element;
        if (location.Region != Region.Other || location.Offset is null)
            return Yes(NamedValue.Unknown("naming.read-region", "读取没有已命名的区域或定值偏移。"));
        var owner = c.Get(this, location.Root); if (!owner.IsSuccess) return owner;
        if (owner.Value == NameLattice.Pending) return owner;
        if (owner.Value.Name is not { } parent || owner.Value.Record is not { } record || !spec.Layout.Records.TryGetValue(record, out var layout))
            return Yes(NamedValue.Unknown("naming.read-base", "读取的基值没有运行时结构身份。", owner.Value.Why));
        if (ContextRead(location, low, parent, record) is { } generic) return generic;
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
        if (owner is ExceptionPayloadName payload && record == "Il2CppExceptionWrapper"
            && field.Path == spec.Layout.Field("Il2CppExceptionWrapper", "ex").Path)
            return new(ValueKind.ManagedReference, new CaughtExceptionName(payload.Handler, caughtTypes?.GetValueOrDefault(payload.Handler) ?? exceptionType), "Il2CppObject");
        return SpecificationValue(new FieldName(owner, record, field.Path), field.Type);
    }
    private NamedValue SpecificationValue(ValueName name, string spelling)
    {
        var type = spelling.Replace("const ", "", StringComparison.Ordinal).Replace("struct ", "", StringComparison.Ordinal).Trim();
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
