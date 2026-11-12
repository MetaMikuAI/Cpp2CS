using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Recovery.Inlining;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    /// <summary>一次对象分配；与紧随其后的构造函数调用合成 newobj，对象的值是构造完成后的局部。</summary>
    private sealed class ObjectDefinition(TypeRef type, Term result)
    {
        public TypeRef Type { get; } = type;
        public Term Result { get; } = result;
        public LocalValue? Local { get; set; }
        public MethodRef? InlinedConstructor { get; set; }
        public IReadOnlyList<ManagedValue> Arguments { get; set; } = [];
    }
    private readonly Dictionary<CallIdentity, ObjectDefinition> allocations = [];
    private readonly Dictionary<Term, ObjectDefinition> objects = [];
    private readonly Dictionary<CallIdentity, ObjectDefinition> constructions = [];
    private ObjectDefinition? constructing;
    private ValueNamingQuery? valueNames;

    /// <summary>分配的类取自已命名的元数据实体；说不出类的分配是洞。</summary>
    private void PrepareAllocation(Call call, ClassifiedCall c)
    {
        var input = c.Operation!.Inputs.FirstOrDefault(i => i.Kind == RuntimeValueKind.Class);
        if (valueNames is null || input is null || c.Inputs?.GetValueOrDefault(input.Name)?.Source is not TermSource klass
            || c.Result?.Source is not TermSource result)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "对象分配的类或结果没有绑定", code: "lowering.Allocation.Binding"); return; }
        var named = context.Get(valueNames, klass.Term);
        if (!named.IsSuccess || named.Value.Name is not EntityName { Entity: ClassEntity { Type: var type } } || !ManagedTypes.IsReferenceType(type))
        {
            Fail<object>(LoweringFailureKind.RuntimeCall, "对象分配的类没有实体凭据", named.IsSuccess ? named.Value.Why : named.Why, "lowering.Allocation.Class");
            return;
        }
        var definition = new ObjectDefinition(type, result.Term);
        allocations.Add(call.Identity, definition);
        objects[result.Term] = definition;
    }

    private readonly HashSet<WriteIdentity> constructorWrites = [];
    private ConstructorAnswer? constructorInitialization;

    /// <summary>位置查询提供初始写入，模板查询绑定值；只有匹配成功的写入并入构造调用。</summary>
    private void PairConstructions()
    {
        if (calls is null) return;
        var query = new AllocationConstructorQuery(state, locations, calls,
            callDefinitions.ToDictionary(p => p.Key, p => new ConstructorCall(p.Value.Method, p.Value.Binding, p.Value.Virtual, p.Value.Receiver)), constructors);
        foreach (var definition in allocations.Values)
            definition.Local = new(new(nextLocal++), definition.Type, types.PointerSize * 8);
        foreach (var b in function.Blocks)
            for (int i = 0; i < b.Statements.Length; i++)
            {
                if (b.Statements[i] is not Call call || !allocations.TryGetValue(call.Identity, out var definition)) continue;
                position = call.Trace?.NativeAddress ?? b.Trace?.NativeAddress ?? 0;
                var result = context.Get(query, new(new(b.Identity, i), definition.Type, definition.Result,
                    new(method, position, definition.Type, ConstructorAnchor.Allocation)));
                if (!result.IsSuccess || result.Value.Failure is not null)
                {
                    var why = result.IsSuccess ? result.Value.Failure! : result.Why!;
                    Fail<object>(LoweringFailureKind.RuntimeCall, why.Message, why.Cause, why.Code);
                    continue;
                }
                if (result.Value.Call is { } paired) constructions.Add(paired, definition);
                else if (constructors is not null)
                {
                    var writes = ConstructorInputs(result.Value.Writes);
                    if (writes is null) return;
                    var answer = constructors.Resolve(new(method, position, definition.Type, ConstructorAnchor.Allocation), writes);
                    if (answer.Failure is { } why)
                    { Fail<object>(LoweringFailureKind.RuntimeCall, why.Message, why.Cause, why.Code); return; }
                    definition.InlinedConstructor = answer.Method;
                    definition.Arguments = answer.Arguments;
                    foreach (int index in answer.Writes) constructorWrites.Add(result.Value.Writes[index].Write.Identity);
                }
            }
        if (constructors is null || method.Method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }) return;
        // 任何可能初始化 this 的已有祖先构造调用都交给原见证检查，不能重复补入。
        if (callDefinitions.Values.Any(d => d.Method.Method is { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
            && types.IsAssignable(method.DeclaringType, d.Method.DeclaringType))) return;
        var self = arguments.FirstOrDefault(p => p.Value is ArgumentValue { Index: -1 }).Key;
        if (self is null) return;
        var initial = query.InitialWrites(context, new(function.Entry, 0), self);
        var inputs = ConstructorInputs(initial);
        if (inputs is null) return;
        constructorInitialization = constructors.MatchInitialization(method, inputs);
        if (constructorInitialization.Failure is { } reason)
        { Fail<object>(LoweringFailureKind.ConstructorInitialization, reason.Message, reason.Cause, reason.Code); return; }
        foreach (int index in constructorInitialization.Writes) constructorWrites.Add(initial[index].Write.Identity);
    }

    private IReadOnlyList<ConstructorWrite>? ConstructorInputs(IReadOnlyList<ConstructorInitialWrite> writes)
    {
        var result = new List<ConstructorWrite>();
        foreach (var write in writes)
        {
            var type = write.Field.Field.Type.Substitute((write.Field.DeclaringType as DefinitionRef)?.Arguments ?? [], []);
            var value = types.Kind(type) == TypeKind.Struct ? StructValue(new TermSource(write.Write.Value), type, write.Point)
                : Value(write.Write.Value, IsFloat(type));
            if (value is null) return null;
            value = types.Kind(type) == TypeKind.Struct ? value : Opaque(type) || Opaque(value.Type) || ReferenceType(type) || ManagedTypes.IsNativePointer(type) ? Coerce(value, type)
                : IsFloat(type) ? FloatBits(value, write.Write.Width)
                : new ConversionValue(ManagedTypes.IsSigned(type) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                    IntegerBits(value), type, write.Write.Width);
            var resolved = context.Get(state.Resolve, write.Write.Value);
            if (!resolved.IsSuccess) return Fail<IReadOnlyList<ConstructorWrite>>(LoweringFailureKind.State, "初始写入值查询失败", resolved.Why);
            result.Add(new(write.Field, value, resolved.Value));
        }
        return result;
    }

    /// <summary>一维数组的分配：就在调用处写成 newarr，结果是一个局部。</summary>
    private sealed class VectorDefinition(ArrayRef type, BoundValue length, LocalValue local)
    {
        public ArrayRef Type { get; } = type;
        public BoundValue Length { get; } = length;
        public LocalValue Local { get; } = local;
    }
    private readonly Dictionary<CallIdentity, VectorDefinition> vectors = [];
    private readonly Dictionary<Term, VectorDefinition> vectorResults = [];
    private readonly Dictionary<CallIdentity, BoundValue> thrown = [];

    private void PrepareVector(Call call, ClassifiedCall c)
    {
        var klassInput = c.Operation!.Inputs.FirstOrDefault(i => i.Kind == RuntimeValueKind.Class);
        var lengthInput = c.Operation.Inputs.FirstOrDefault(i => i.Kind == RuntimeValueKind.Integer);
        if (valueNames is null || klassInput is null || lengthInput is null
            || c.Inputs?.GetValueOrDefault(klassInput.Name)?.Source is not TermSource klass
            || c.Inputs.GetValueOrDefault(lengthInput.Name) is not { } length || c.Result?.Source is not TermSource result)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "数组分配的类、长度或结果没有绑定", code: "lowering.Allocation.Binding"); return; }
        var named = context.Get(valueNames, klass.Term);
        if (!named.IsSuccess || named.Value.Name is not EntityName { Entity: ClassEntity { Type: ArrayRef { IsVector: true } type } })
        {
            Fail<object>(LoweringFailureKind.RuntimeCall, "数组分配的类没有一维向量的实体凭据", named.IsSuccess ? named.Value.Why : named.Why, "lowering.Allocation.Class");
            return;
        }
        var definition = new VectorDefinition(type, length, new(new(nextLocal++), type, types.PointerSize * 8));
        vectors.Add(call.Identity, definition);
        vectorResults[result.Term] = definition;
    }

    /// <summary>抛出一个已有的异常对象：操作登记为不返回、以抛出终止、没有固定的异常类型。</summary>
    private void PrepareThrow(Call call, ClassifiedCall c)
    {
        var input = c.Operation!.Inputs.FirstOrDefault(i => i.Kind == RuntimeValueKind.ManagedReference);
        if (input is null || c.Inputs?.GetValueOrDefault(input.Name) is not { } exception)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "抛出的异常对象没有绑定", code: "lowering.Throw.Binding"); return; }
        thrown.Add(call.Identity, exception);
    }

    private ManagedStatement? LowerRuntimeStatement(Call call, Point point)
    {
        if (vectors.TryGetValue(call.Identity, out var vector))
        {
            var length = CallArgument(vector.Length, types.Integer(32, true), point);
            return length is null ? null : new ManagedAssignment(position, vector.Local, new NewArrayValue(vector.Type, length, types.PointerSize * 8));
        }
        var exception = thrown[call.Identity];
        var term = BoundTerm(exception.Source, point);
        if (term is null) return null;
        var resolved = context.Get(state.Resolve, term);
        if (!resolved.IsSuccess) return Fail<ManagedStatement>(LoweringFailureKind.State, "异常对象状态查询失败", resolved.Why);
        var value = Value(resolved.Value);
        if (value is null) return null;
        if (!ManagedTypes.IsReferenceType(value.Type)) return Fail<ManagedStatement>(LoweringFailureKind.UnsupportedType, "抛出的值不是对象引用");
        return new ManagedThrow(position, value);
    }

    private bool PrivateAccess(Statement statement) => AllocationConstructorQuery.PrivateAccess(context, state, locations, statement);

    private ManagedValue? ObjectValue(ObjectDefinition definition) =>
        definition == constructing ? Fail<ManagedValue>(LoweringFailureKind.RuntimeCall, "对象在自己的构造函数实参里被使用", code: "lowering.Allocation.Escape")
        : definition.Local ?? Fail<ManagedValue>(LoweringFailureKind.RuntimeCall, "对象分配没有配对的构造函数调用", code: "lowering.Allocation.Constructor");
}
