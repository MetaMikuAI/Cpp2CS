using Cpp2CS.Recovery.Binding;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Inlining;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private void CheckBody(ManagedBody body)
    {
        void Missing(string category, Reason? cause = null) => Fail<object>(LoweringFailureKind.UnsupportedType,
            "访问缺少权限或内联逆证明：" + category, cause, code: "lowering.Access." + category);
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            position = statement.Address;
            if (statement is ManagedCall call && !ManagedAccess.Method(types, method.Method.Owner,
                call.Invocation.Method, call.Invocation.Receiver?.Type)) { Missing("Method"); return; }
            foreach (var value in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk))
            {
                bool referenceBits = value switch
                {
                    ConversionValue conversion => ReferenceType(conversion.Operand.Type),
                    BinaryValue binary => ReferenceType(binary.Left.Type) || ReferenceType(binary.Right.Type),
                    UnaryValue unary => ReferenceType(unary.Operand.Type),
                    _ => false,
                };
                if (referenceBits)
                {
                    Fail<object>(LoweringFailureKind.UnsupportedType, "引用位型用于数值，缺少路径上的零值证明", code: "lowering.ReferenceBits");
                    return;
                }
                if (!ManagedAccess.Type(types, method.Method.Owner, value.Type)) { Missing("Type"); return; }
                if (value is FieldValue field && !ManagedAccess.Field(types, method, field.Field, field.Receiver.Type))
                { Missing("Field", new("access.field", "字段 " + field.Field.Field.Owner.FullName + "." + field.Field.Field.Name));
                    if (types.Kind(field.Field.DeclaringType) == TypeKind.Struct) failure = failure! with { StructType = field.Field.DeclaringType };
                    else if (types.Kind(field.Type) == TypeKind.Struct) failure = failure! with { StructType = field.Type };
                    return; }
                if (value is StaticFieldValue shared && !ManagedAccess.Field(types, method, shared.Field, null))
                { Missing("Field");
                    if (types.Kind(shared.Type) == TypeKind.Struct) failure = failure! with { StructType = shared.Type };
                    return; }
                if (value is NewObjectValue created && !ManagedAccess.Method(types, method.Method.Owner, created.Constructor, null))
                { Missing("Method"); return; }
            }
        }
    }

    private sealed class ReadDefinition(MemoryRead read)
    {
        public MemoryRead Read { get; set; } = read;
        public LocalValue? Local { get; set; }
        public ManagedValue? Value { get; set; }
        public ManagedValue? Constant { get; set; }
        public MethodRef? Accessor { get; set; }
    }
    private readonly Dictionary<Term, ReadDefinition> readValues = [];
    private readonly Dictionary<ReadIdentity, ReadDefinition> readDefinitions = [];
    private readonly Dictionary<ulong, List<(int Before, ReadIdentity Read, ulong Address)>> readInsertions = [];
    private static bool ReferenceType(TypeRef type) => ManagedTypes.IsReferenceType(type) || type is ByRefRef;
    private TypeRef? StaticType(Term term)
    {
        if (arguments.TryGetValue(term, out var argument)) return argument.Type;
        if (locations is null) return null;
        var result = context.Get(locations.Types, term);
        return result.IsSuccess ? result.Value?.Type : null;
    }
    private ManagedValue Coerce(ManagedValue value, TypeRef type)
    {
        if (ReferenceType(value.Type) && ManagedTypes.IsNativePointer(type)
            || ManagedTypes.IsNativePointer(value.Type) && ReferenceType(type))
        {
            Fail<object>(LoweringFailureKind.UnsupportedType, "托管引用与原生整数或非托管指针不能直接转换", code: "lowering.NativeInt.Reference");
            return value;
        }
        if (Opaque(value.Type) || Opaque(type))
        {
            if (Equals(value.Type, type)) return value;
            if (Opaque(type) && value is ConstantValue { Bits: 0 }) return new ComposedValue(type, []);
            if (Opaque(value.Type) && (type.Equals(types.Object) || type is DefinitionRef { Definition.IsInterface: true })
                && witness is not null && GenericWitness.IsCanonical(witness))
                return new BoxValue(value, value.Type, type, types.PointerSize * 8);
            if (!Equals(value.Type, type)) GenericFailure<object>("Conversion", "类型参数值只能原样流向同一类型参数的位置");
            return value;
        }
        if (ManagedTypes.IsNativePointer(type)) return NativeBits(value, type);
        if (value is ConstantValue { Bits: 0 } && ManagedTypes.IsReferenceType(type))
            return new ConstantValue(0, type, types.PointerSize * 8);
        if (Equals(value.Type, type) || ManagedTypes.IsReferenceType(value.Type) && types.IsAssignable(value.Type, type)) return value;
        if (ManagedTypes.IsReferenceType(value.Type) && ManagedTypes.IsReferenceType(type)
            && value is LocalValue local && merges.Values.Any(m => m.Id == local.Id))
            Fail<object>(LoweringFailureKind.UnsupportedType, "使用位置需要类型 " + type + "，引用合流的静态类型为 " + value.Type, code: "lowering.Merge.StaticType");
        else Fail<object>(LoweringFailureKind.UnsupportedType, $"值的托管类型与使用位置不兼容：{types.Kind(value.Type)} → {types.Kind(type)}，{value.GetType().Name}");
        return value;
    }
    private int registeredAccessorReads;
    private int? accessorReadCount;
    private bool accessorProgramPrepared;
    private bool accessorProgramMaterialized;
    private readonly Dictionary<AccessorReplacement, LocalValue?> accessorResults = [];
    private AccessorProgram? accessorProgram;
    private Reason? accessorProgramFailure;
    private readonly Dictionary<ReadIdentity, List<ManagedCall>> accessorReadCalls = [];
    private readonly HashSet<ReadIdentity> accessorConsumedReads = [];
    private readonly Dictionary<CallIdentity, ManagedCall> accessorCallCalls = [];
    private readonly Dictionary<BlockIdentity, AccessorRegion> accessorRegions = [];
    private readonly HashSet<BlockIdentity> accessorRemovedBlocks = [];
    private readonly Dictionary<ulong, List<ManagedCall>> accessorEndCalls = [];
    private readonly Dictionary<WriteIdentity, ManagedCall?> accessorWriteCalls = [];

    private void RegisterRead(MemoryRead read)
    {
        RegisterReadDefinition(read);
        accessorReadCount ??= function.Blocks.Sum(b => b.Statements.OfType<MemoryRead>().Count());
        if (++registeredAccessorReads == accessorReadCount) PrepareAccessorProgram();
    }
    private void RegisterReadDefinition(MemoryRead read)
    {
        if (readDefinitions.ContainsKey(read.Identity)) return;
        // 只登记可用身份；未使用读取的失败不阻断下降，实际使用处负责传播失败。
        var address = context.Get(state.Resolve, read.Address);
        if (!address.IsSuccess) return;
        var location = context.Get(state.Locations, new(address.Value, read.Width));
        if (!location.IsSuccess) return;
        if (location.Value.Region == Region.Frame && !FrameContains(location.Value)) return;
        var resolved = context.Get(state.Read, read.Identity);
        if (!resolved.IsSuccess) return;
        // 内存合流描述来源；读取仍在原读取点物化，不在入边补造读取。
        if (resolved.Value.Identity is not (MemoryAtom or MemoryMerge)) return;
        if (!readValues.TryGetValue(resolved.Value, out var definition))
            readValues.Add(resolved.Value, definition = new(read));
        readDefinitions.Add(read.Identity, definition);
    }
    private void PrepareAccessorProgram()
    {
        if (accessorProgramPrepared || accessors is null || locations is null) return;
        accessorProgramPrepared = true;
        foreach (var group in readDefinitions.GroupBy(p => p.Value).Where(g => g.Count() > 1))
        {
            var occurrences = group.Select(p => p.Key).ToArray();
            if (context.Get(accessors.ReadPlacement, new(group.Key.Read.Identity, occurrences)) is { IsSuccess: true, Value: true }) continue;
            foreach (var identity in occurrences.Where(id => id != group.Key.Read.Identity))
                if (context.Get(accessors.ReadPlacement, new(identity, occurrences)) is { IsSuccess: true, Value: true }
                    && context.Get(state.Index, 0) is { IsSuccess: true } index)
                { group.Key.Read = index.Value.Reads[identity].Read; break; }
        }
        var answer = accessors.Match(context, method, state, locations, arguments, callDefinitions.ToDictionary(p => p.Key,
            p => new AccessorCallSite(p.Value.Method, p.Value.Binding, p.Value.Virtual, p.Value.Receiver)));
        if (!answer.IsSuccess) { accessorProgramFailure = new("inline.Accessor.None", "模板项匹配查询未完成", answer.Why); return; }
        accessorProgram = answer.Value;
        foreach (var replacement in accessorProgram.Replacements)
        {
            if (replacement.Region is { } region)
            { accessorRegions.Add(region.Entry, region); accessorRemovedBlocks.UnionWith(region.Blocks); }
            LocalValue? local = null;
            if (replacement.Result is { } result)
            {
                var type = replacement.Method.Concrete(replacement.Method.Method.ReturnType);
                local = new(new(nextLocal++), type, ValueWidth(type));
                values[result] = replacement.Negated ? new NegatedValue(local, types.Boolean) : local;
                // 完整读取与它的位片共用调用结果，保留原读取身份供范围视图取用。
                if (readValues.TryGetValue(result, out var definition))
                {
                    definition.Local = local;
                    foreach (var occurrence in readDefinitions.Where(p => ReferenceEquals(p.Value, definition)))
                        accessorConsumedReads.Add(occurrence.Key);
                    var range = Range(definition.Read.Address, definition.Read.Width);
                    if (range is { Pieces: [{ View: { } view, AccessBit: 0, LocationBit: 0 } piece] }
                        && piece.Width == definition.Read.Width)
                        rangeReads[(definition, view)] = definition;
                }
            }
            accessorResults.Add(replacement, local);
            accessorConsumedReads.UnionWith(replacement.Reads);
        }
    }
    private void MaterializeAccessorProgram()
    {
        PrepareAccessorProgram();
        if (accessorProgramMaterialized || accessorProgram is null) return;
        accessorProgramMaterialized = true;
        foreach (var replacement in accessorProgram.Replacements)
        {
            ManagedValue? receiver = replacement.Receiver is { } self ? Value(self) : null;
            if (replacement.Receiver is not null && receiver is null) return;
            var args = new List<ManagedValue>();
            for (int i = 0; i < replacement.Arguments.Count; i++)
            {
                var value = Value(replacement.Arguments[i]); if (value is null) return;
                var type = replacement.Method.Concrete(replacement.Method.Method.Parameters[i].Type);
                value = ReferenceType(type) || Opaque(type) ? Coerce(value, type)
                    : new ConversionValue(ManagedTypes.IsSigned(type) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                        IntegerBits(value), type, ValueWidth(type));
                args.Add(value);
            }
            var block = function.Blocks.Single(b => b.Identity == replacement.Point.Block);
            var address = replacement.Point.Before == block.Statements.Length ? block.Trace?.NativeAddress ?? 0
                : block.Statements[replacement.Point.Before].Trace?.NativeAddress ?? 0;
            var call = new ManagedCall(address, new(replacement.Method, receiver, args,
                receiver is not null && !replacement.Method.Method.Owner.IsValueType && receiver is not ArgumentValue { Index: -1 }), accessorResults[replacement]) { Inlined = true };
            if (replacement.Region is not null)
            {
                if (!accessorEndCalls.TryGetValue(labels[replacement.Point.Block], out var callsAtEnd)) accessorEndCalls.Add(labels[replacement.Point.Block], callsAtEnd = []);
                callsAtEnd.Add(call);
            }
            else if (replacement.Call is { } consumedCall) accessorCallCalls.Add(consumedCall, call);
            else if (replacement.Writes.Count != 0)
            {
                foreach (var write in replacement.Writes) accessorWriteCalls.Add(write, null);
                var first = ((MemoryWrite)block.Statements[replacement.Point.Before]).Identity;
                accessorWriteCalls[first] = call;
            }
            else
            {
                var first = ((MemoryRead)block.Statements[replacement.Point.Before]).Identity;
                if (!accessorReadCalls.TryGetValue(first, out var list)) accessorReadCalls.Add(first, list = []);
                list.Add(call);
            }
        }
    }
    private ManagedValue? NamedConstant(NamedValue named) => (named.EquivalentName ?? named.Name) is EntityName { Entity: StringEntity literal }
        ? new StringValue(literal.Value, types.String, types.PointerSize * 8) : null;
    private ManagedValue? ReadValue(ReadDefinition definition)
    {
        if (definition.Local is not null) return definition.Local;
        if (definition.Constant is not null) return definition.Constant;
        var read = definition.Read;
        // 字符串字面量的槽位在元数据初始化之后就是那个驻留的字符串对象，与 ldstr 相同；它是常量，不需要落进局部。
        if (valueNames is not null && context.Get(valueNames, read.Result) is { IsSuccess: true } named
            && NamedConstant(named.Value) is { } constant) return definition.Constant = constant;
        var usePosition = position; position = read.Trace?.NativeAddress ?? position;
        var range = Range(read.Address, read.Width);
        if (range?.Why is { Code: "location.padding" or "location.overlap" or "location.range" } rangeFailure)
            return Fail<ManagedValue>(LoweringFailureKind.NonFrameRead, rangeFailure.Message, rangeFailure, rangeFailure.Code);
        if (range is { Pieces.IsEmpty: false } && !(range.Pieces is [{ View: { } whole, LocationBit: 0 } piece]
            && piece.Width == types.Size(whole.Type) * 8))
        {
            var split = RangeRead(definition, 0, read.Width); position = usePosition; return split;
        }
        var value = Access(read.Address, read.Width);
        if (value is null) return null;
        if (types.Kind(value.Type) == TypeKind.Struct)
            return frameObjects?.Accesses.ContainsKey(read.Identity) == true
                ? Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "结构体帧读取不能作为跨字段标量使用：" + value.Type, code: "lowering.Frame.Struct")
                : StructScalarFailure(value.Type);
        definition.Accessor = FieldAccessor(value, false, definition);
        if (failure is not null) return null;
        position = usePosition;
        definition.Value = value;
        definition.Local = new(new(nextLocal++), value.Type, value.Width);
        return definition.Local;
    }
    private ManagedBlock InsertReads(ManagedBlock block)
    {
        MaterializeAccessorProgram();
        var reads = readInsertions.GetValueOrDefault(block.Address) ?? [];
        var statements = new List<ManagedStatement>(); int cursor = 0;
        for (int i = 0; i <= block.Statements.Count; i++)
        {
            while (cursor < reads.Count && reads[cursor].Before == i)
            {
                var read = reads[cursor++];
                if (accessorReadCalls.TryGetValue(read.Read, out var recovered)) statements.AddRange(recovered);
                if (!accessorConsumedReads.Contains(read.Read) && readDefinitions.TryGetValue(read.Read, out var definition) && definition.Local is { } local)
                {
                    if (definition.Accessor is { } accessor)
                    {
                        // 同值读取共用原定义；调用只在该定义处发生一次。
                        if (read.Read == definition.Read.Identity)
                            statements.Add(new ManagedCall(read.Address, AccessorInvocation(accessor, definition.Value!, []), local) { Inlined = true });
                    }
                    else statements.Add(new ManagedAssignment(read.Address, local, definition.Value!));
                }
                if (structReads.TryGetValue(read.Read, out var aggregates))
                    foreach (var aggregate in aggregates)
                        statements.Add(aggregate.Accessor is { } getter
                            ? new ManagedCall(read.Address, AccessorInvocation(getter, aggregate.Value!, []), aggregate.Local!) { Inlined = true }
                            : new ManagedAssignment(read.Address, aggregate.Local!, aggregate.Value!));
            }
            if (i < block.Statements.Count) statements.Add(block.Statements[i]);
        }
        if (accessorEndCalls.TryGetValue(block.Address, out var atEnd)) statements.InsertRange(statements.Count - 1, atEnd);
        return block with { Statements = statements };
    }
    private ManagedStatement? LowerStore(MemoryWrite write, Point point)
    {
        // 入口地址的普通溢出由状态模型转发；对外存储仍按逃逸检查。
        if (hasIndirectParameters && valueNames is not null
            && context.Get(state.Resolve, write.Value) is { IsSuccess: true } stored
            && context.Get(valueNames, stored.Value) is { IsSuccess: true, Value.Name: IndirectParameterName }
            && context.Get(state.Resolve, write.Address) is { IsSuccess: true } spill
            && context.Get(state.Locations, new(spill.Value, write.Width)) is { IsSuccess: true, Value.Region: Region.Frame }) return null;
        MaterializeAccessorProgram();
        if (accessorWriteCalls.TryGetValue(write.Identity, out var recovered)) return recovered;
        if (RejectAddressUse([write.Value], "写入内存")) return null;
        if (structReturnStores is not null)
        {
            var output = context.Get(structReturnStores, write.Identity);
            if (!output.IsSuccess) return Fail<ManagedStatement>(LoweringFailureKind.State, "结构体结果区写入查询失败", output.Why, "lowering.Struct.ResultStore");
            if (output.Value) return null;
        }
        var resolved = context.Get(state.Resolve, write.Address);
        if (!resolved.IsSuccess) return Fail<ManagedStatement>(LoweringFailureKind.State, "写入地址查询失败", resolved.Why);
        var location = context.Get(state.Locations, new(resolved.Value, write.Width));
        if (!location.IsSuccess) return Fail<ManagedStatement>(LoweringFailureKind.State, "写入位置查询失败", location.Why);
        if (location.Value.Region == Region.Frame) return null;
        TypeRef? copiedType = null;
        if (locations is not null && context.Get(locations, new(write.Address, write.Width)) is { IsSuccess: true } located)
            foreach (var view in located.Value.Views.Where(v => v.Offset == 0 && types.Kind(v.Type) == TypeKind.Struct
                && types.StorageBits(v.Type) == write.Width).OrderBy(v => v.Path.Length))
            {
                var copy = context.Get(structs, new(view.Type, new TermSource(write.Value), point));
                if (copy.IsSuccess)
                { copiedType = view.Type; break; }
            }
        var target = Access(write.Address, write.Width, true, copiedType);
        if (target is null) return null;
        var accessor = FieldAccessor(target, true, writeIdentity: write.Identity);
        if (failure is not null) return null;
        if (target is ArrayLengthValue) return Fail<ManagedStatement>(LoweringFailureKind.NonFrameWrite, "数组长度不可写");
        var value = types.Kind(target.Type) == TypeKind.Struct
            ? StructValue(new TermSource(write.Value), target.Type, point)
            : Value(write.Value, IsFloat(target.Type));
        if (value is null) return null;
        value = types.Kind(target.Type) == TypeKind.Struct ? value : Opaque(target.Type) || Opaque(value.Type) || ReferenceType(target.Type) || ManagedTypes.IsNativePointer(target.Type) ? Coerce(value, target.Type) : IsFloat(target.Type) ? FloatBits(value, write.Width)
            : new ConversionValue(ManagedTypes.IsSigned(target.Type) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                IntegerBits(value), target.Type, write.Width);
        return accessor is null ? new ManagedStore(position, target, value)
            : new ManagedCall(position, AccessorInvocation(accessor, target, [value]), null) { Inlined = true };
    }

    private MethodRef? FieldAccessor(ManagedValue storage, bool write, ReadDefinition? read = null, WriteIdentity? writeIdentity = null)
    {
        if (accessors is null) return null;
        foreach (var value in ManagedValues.Walk(storage))
        {
            var (field, receiver) = value switch
            {
                FieldValue f => (f.Field, f.Receiver.Type),
                StaticFieldValue f => (f.Field, (TypeRef?)null),
                _ => ((FieldRef?)null, (TypeRef?)null),
            };
            if (field is null || ManagedAccess.Field(types, method, field, receiver)) continue;
            StableIdentity? identity = read is not null ? read.Read.Identity : writeIdentity;
            var programFailure = accessorProgramFailure ?? (identity is not null ? accessorProgram?.Failures.GetValueOrDefault(identity) : null);
            if (programFailure is not null)
            {
                var rejected = accessors.Reject(new(method, position, field, receiver, write ? AccessorKind.Setter : AccessorKind.Getter, false), programFailure);
                Fail<object>(LoweringFailureKind.UnsupportedType, programFailure.Message, programFailure.Cause, programFailure.Code);
                return rejected.Method;
            }
            Reason? placementFailure = !ReferenceEquals(value, storage)
                ? new("inline.Accessor.Placement.NestedAccess", "不可访问字段只是复合访问的内部位置")
                : ManagedValues.Children(storage).Any(v => !AccessorReceiver(v))
                    ? new("inline.Accessor.Placement.Receiver", "接收者仍含字段访问或复合位置的取地址，不能保持单次访问的位置") : null;
            if (placementFailure is null && read is not null)
            {
                var placement = context.Get(accessors.ReadPlacement, new(read.Read.Identity,
                    readDefinitions.Where(p => ReferenceEquals(p.Value, read)).Select(p => p.Key).ToArray()));
                if (!placement.IsSuccess || !placement.Value)
                    placementFailure = new("inline.Accessor.Placement.ReadDominance", "原读取未能证明支配全部同值读取", placement.Why);
            }
            var answer = accessors.Resolve(new(method, position, field, receiver, write ? AccessorKind.Setter : AccessorKind.Getter,
                placementFailure is null, placementFailure));
            if (answer.Failure is { } why) Fail<object>(LoweringFailureKind.UnsupportedType, why.Message, why.Cause, why.Code);
            return answer.Method;
        }
        return null;
    }

    private bool AccessorReceiver(ManagedValue value) => value is LocalValue or ArgumentValue
        || value is AddressValue address && AccessorReceiver(address.Target)
        || value is FieldValue field && types.Kind(field.Type) == TypeKind.Struct && AccessorReceiver(field.Receiver);

    private ManagedInvocation AccessorInvocation(MethodRef accessor, ManagedValue storage, IReadOnlyList<ManagedValue> arguments)
    {
        var receiver = (storage as FieldValue)?.Receiver;
        if (receiver is not null && accessor.Method.Owner.IsValueType && receiver.Type is not ByRefRef)
            receiver = new AddressValue(receiver, types.PointerSize * 8);
        // 值类型接收者已是托管地址，直接调用保持该存储；引用接收者在原读取处判空。
        return new(accessor, receiver, arguments, receiver is not null && !accessor.Method.Owner.IsValueType
            && receiver is not ArgumentValue { Index: -1 });
    }
    private ManagedValue? Access(Term address, int width, bool write = false, TypeRef? expectedType = null)
    {
        var kind = write ? LoweringFailureKind.NonFrameWrite : LoweringFailureKind.NonFrameRead;
        if (locations is null) return Fail<ManagedValue>(kind, "未装配托管位置查询");
        var result = context.Get(locations, new(address, width));
        if (!result.IsSuccess) return Fail<ManagedValue>(kind, "定位查询失败", result.Why, result.Why?.Code);
        var location = result.Value;
        if (location.Kind is ManagedLocationKind.NotManaged or ManagedLocationKind.Unknown)
            return Fail<ManagedValue>(kind, "使用未定位的内存：" + location.Kind,
                location.Why, location.Why?.Code ?? "lowering.Location." + location.Kind);
        if (location.Views.Any(v => GenericStruct(v.Type)))
            return GenericFailure<ManagedValue>("Struct", "含类型参数的值类型访问尚未下降");
        var exact = location.Views.Where(v => (expectedType is null || v.Type.Equals(expectedType)) && v.Offset == 0 && (v.Kind == ManagedLocationKind.ArrayLength
            || types.Size(v.Type) * 8 == width)).ToArray();
        var views = exact.Where(v => v.Kind == ManagedLocationKind.ArrayLength || Scalar(v.Type)
            || v.Kind == ManagedLocationKind.FrameLocal && ManagedTypes.IsNativePointer(v.Type)).ToArray();
        if (views.Length == 0)
        {
            views = exact.Where(v => types.Kind(v.Type) == TypeKind.Struct).OrderBy(v => v.Path.Length).ToArray();
            if (views.Length > 1 && views.Skip(1).All(v => v.Path.Take(views[0].Path.Length).SequenceEqual(views[0].Path)))
                views = [views[0]];
        }
        if (views.Length != 1) return Fail<ManagedValue>(kind,
            views.Length == 0 ? "访问只覆盖位置的一部分" : "访问有多个完整托管视图", code: views.Length == 0 ? "lowering.Location.Partial" : "lowering.Location.Ambiguous");
        var view = views[0];
        if (write && !Writable(view)) return null;
        return AccessView(view, write);
    }
    private ManagedValue? AccessView(LocationView view, bool write = false, bool address = false)
    {
        if (view.Kind == ManagedLocationKind.StaticField)
        {
            // 根是类的静态字段块，不是托管值；路径的第一项就是静态字段本身。
            var head = view.Path[0];
            var headType = head.Field.Type.Substitute((head.DeclaringType as DefinitionRef)?.Arguments ?? [], []);
            ManagedValue storage = new StaticFieldValue(head, headType, ValueWidth(headType));
            foreach (var field in view.Path.Skip(1))
            {
                if (write && types.Kind(storage.Type) == TypeKind.Struct) storage = new AddressValue(storage, types.PointerSize * 8);
                var type = field.Field.Type.Substitute((field.DeclaringType as DefinitionRef)?.Arguments ?? [], []);
                storage = new FieldValue(storage, field, type, ValueWidth(type));
            }
            if (!address && !Scalar(storage.Type) && types.Kind(storage.Type) != TypeKind.Struct)
                return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "访问的值类型尚未下降");
            return storage;
        }
        var root = view.Kind == ManagedLocationKind.FrameLocal ? FrameLocal(frameObjects!.Objects.Single(o => o.Address == view.Root)) : Value(view.Root);
        if (root is null) return null;
        if (Opaque(root.Type)) return GenericFailure<ManagedValue>("Receiver", "类型参数值不能作为字段或数组接收者");
        if (view.Kind == ManagedLocationKind.Indirect) return new IndirectValue(root, view.Type, ValueWidth(view.Type));
        if (root.Type is ByRefRef { Element: not DefinitionRef { Definition.IsValueType: true } })
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "字段接收者的托管地址必须指向值类型");
        if (view.Kind == ManagedLocationKind.ArrayLength) return Mask(new ArrayLengthValue(root, types.UInt32, 32), view.Width);
        ManagedValue value = root;
        if (view.Kind == ManagedLocationKind.ArrayElement)
        {
            var index = Value(view.Index!);
            if (index is null) return null;
            if (Opaque(index.Type)) return GenericFailure<ManagedValue>("Arithmetic", "类型参数值不能作为数组下标");
            var element = view.ElementType ?? view.Type;
            value = new ArrayElementValue(root, index, element, ValueWidth(element));
        }
        foreach (var field in view.Path)
        {
            if ((write || view.Kind == ManagedLocationKind.FrameLocal) && types.Kind(value.Type) == TypeKind.Struct) value = new AddressValue(value, types.PointerSize * 8);
            var type = field.Field.Type.Substitute((field.DeclaringType as DefinitionRef)?.Arguments ?? [], []);
            if (ManagedTypes.IsReferenceType(value.Type)) value = Coerce(value, field.DeclaringType);
            if (failure is not null) return null;
            value = new FieldValue(value, field, type, ValueWidth(type));
        }
        if (!address && !Scalar(value.Type) && types.Kind(value.Type) != TypeKind.Struct
            && !(view.Kind == ManagedLocationKind.FrameLocal && ManagedTypes.IsNativePointer(value.Type)))
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "访问的值类型尚未下降");
        return value;
    }
}
