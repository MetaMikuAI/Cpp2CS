using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private sealed record TypeCheckDefinition(BoundValue Object, TypeRef Target, LocalValue Local, bool Cast, TypeRef? Boxed);
    private readonly Dictionary<CallIdentity, TypeCheckDefinition> typeChecks = [];
    private readonly Dictionary<Term, LocalValue> runtimeValues = [];
    private sealed record BoxDefinition(BoundValue Data, TypeRef Target, TypeRef Storage, LocalValue Local);
    private readonly Dictionary<CallIdentity, BoxDefinition> boxes = [];
    private sealed record UnboxDefinition(BoundValue Object, TypeRef Target, Term Result, LocalValue Local);
    private readonly Dictionary<CallIdentity, UnboxDefinition> unboxes = [];

    private TypeRef? RuntimeClass(ClassifiedCall call, string code)
    {
        if (valueNames is not null && call.Inputs?.GetValueOrDefault("class")?.Source is TermSource klass)
        {
            var named = context.Get(valueNames, klass.Term);
            if (named.IsSuccess && named.Value.Name is EntityName { Entity: ClassEntity { Type: var type } }) return type;
            return Fail<TypeRef>(LoweringFailureKind.RuntimeCall, "运行时操作的类没有实体凭据", named.IsSuccess ? named.Value.Why : named.Why, code);
        }
        return Fail<TypeRef>(LoweringFailureKind.RuntimeCall, "运行时操作的类没有绑定", code: code);
    }

    private void PrepareTypeCheck(Call call, ClassifiedCall c)
    {
        var type = RuntimeClass(c, "lowering.TypeCheck.Class");
        if (type is null) return;
        if (c.Inputs?.GetValueOrDefault("object") is not { } obj || c.Result?.Source is not TermSource result)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "类型检查的对象或结果没有绑定", code: "lowering.TypeCheck.Binding"); return; }
        bool cast = c.Operation!.Il.Name == "CastClass";
        // isinst 对值类型目标的结果是装箱对象的引用；castclass 的目标只能是引用类型。
        TypeRef? boxed = ManagedTypes.IsReferenceType(type) ? null : types.Object;
        if (cast && boxed is not null)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "强制转换的目标不是引用类型", code: "lowering.TypeCheck.Target"); return; }
        var local = new LocalValue(new(nextLocal++), boxed ?? type, types.PointerSize * 8);
        typeChecks.Add(call.Identity, new(obj, type, local, cast, boxed));
        runtimeValues.Add(result.Term, local);
    }

    private ManagedStatement? LowerTypeCheck(Call call, Point point)
    {
        var definition = typeChecks[call.Identity];
        var obj = CallArgument(definition.Object, types.Object, point);
        if (obj is null) return null;
        if (!ManagedTypes.IsReferenceType(obj.Type))
            return Fail<ManagedStatement>(LoweringFailureKind.RuntimeCall, "类型检查的对象不是引用", code: "lowering.TypeCheck.Object");
        ManagedValue value = definition.Cast ? new CheckedCastValue(obj, definition.Target, types.PointerSize * 8)
            : new IsInstValue(obj, definition.Target, types.PointerSize * 8, definition.Boxed);
        return new ManagedAssignment(position, definition.Local, value);
    }

    private TypeRef? BoxedScalar(TypeRef type, string operation)
    {
        if (type is DefinitionRef { Definition: { Namespace: "System", Name: "Nullable`1" } })
            return Fail<TypeRef>(LoweringFailureKind.RuntimeCall, "可空类型的装拆箱尚未下降", code: "lowering." + operation + ".Nullable");
        var storage = ManagedTypes.Underlying(type);
        if ((!IntegerType(storage) && !IsFloat(storage)) || types.Size(type) is < 1 or > 8)
            return Fail<TypeRef>(LoweringFailureKind.RuntimeCall, "装拆箱类型不是受支持的基元或枚举", code: "lowering." + operation + ".Struct");
        return storage;
    }

    private void PrepareBox(Call call, ClassifiedCall c)
    {
        var type = RuntimeClass(c, "lowering.Box.Class");
        if (type is null || BoxedScalar(type, "Box") is not { } storage) return;
        if (c.Inputs?.GetValueOrDefault("data") is not { } data || c.Result?.Source is not TermSource result)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "装箱的数据地址或结果没有绑定", code: "lowering.Box.Binding"); return; }
        var local = new LocalValue(new(nextLocal++), types.Object, types.PointerSize * 8);
        boxes.Add(call.Identity, new(data, type, storage, local));
        runtimeValues.Add(result.Term, local);
    }

    private ManagedStatement? LowerBox(Call call, Point point)
    {
        var definition = boxes[call.Identity];
        var data = BoundTerm(definition.Data.Source, point);
        if (data is null) return null;
        var address = context.Get(state.Resolve, data);
        if (!address.IsSuccess)
            return Fail<ManagedStatement>(LoweringFailureKind.RuntimeCall, "装箱数据地址查询失败", address.Why, "lowering.Box.Address");
        int width = types.Size(definition.Target) * 8;
        var location = context.Get(state.Locations, new(address.Value, width));
        if (!location.IsSuccess || location.Value.Region != Region.Frame || location.Value.Offset is null)
            return Fail<ManagedStatement>(LoweringFailureKind.RuntimeCall, "装箱数据没有确定的帧位置", location.Why, "lowering.Box.Address");
        var contents = context.Get(state.ValueAt, new(point, location.Value));
        if (!contents.IsSuccess) return Fail<ManagedStatement>(LoweringFailureKind.State, "装箱数据在调用点不可用", contents.Why);
        var value = Value(contents.Value, IsFloat(definition.Storage));
        if (value is null) return null;
        value = IsFloat(definition.Storage) ? FloatBits(value, width)
            : new ConversionValue(ManagedTypes.IsSigned(definition.Storage) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                value, definition.Storage, width);
        return new ManagedAssignment(position, definition.Local, new BoxValue(value, definition.Target, types.Object, types.PointerSize * 8));
    }

    private void PrepareUnbox(Call call, ClassifiedCall c)
    {
        var type = RuntimeClass(c, "lowering.Unbox.Class");
        if (type is null || BoxedScalar(type, "Unbox") is null) return;
        if (c.Inputs?.GetValueOrDefault("object") is not { } obj || c.Result?.Source is not TermSource result)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "拆箱的对象或结果没有绑定", code: "lowering.Unbox.Binding"); return; }
        unboxes.Add(call.Identity, new(obj, type, result.Term, new(new(nextLocal++), type, types.Size(type) * 8)));
    }

    /// <summary>拆箱地址只由同块内、下一次调用或非帧写入之前的唯一完整读取使用；检查所有语句、终结和合流的用途。</summary>
    private void PairUnboxes()
    {
        foreach (var block in function.Blocks)
        for (int i = 0; i < block.Statements.Length; i++)
        {
            if (block.Statements[i] is not Call call || !unboxes.TryGetValue(call.Identity, out var definition)) continue;
            position = call.Trace?.NativeAddress ?? block.Trace?.NativeAddress ?? 0;
            var result = context.Get(state.Resolve, definition.Result);
            if (!result.IsSuccess)
            { Fail<object>(LoweringFailureKind.RuntimeCall, "拆箱地址查询失败", result.Why, "lowering.Unbox.Use"); return; }
            MemoryRead? paired = null;
            for (int j = i + 1; j < block.Statements.Length; j++)
            {
                var statement = block.Statements[j];
                if (statement is Call || statement is MemoryWrite && !PrivateAccess(statement)) break;
                if (statement is not MemoryRead read || read.Width != definition.Local.Width) continue;
                var address = context.Get(state.Resolve, read.Address);
                if (!address.IsSuccess || address.Value != result.Value) continue;
                if (paired is not null)
                { Fail<object>(LoweringFailureKind.RuntimeCall, "拆箱地址有多次读取", code: "lowering.Unbox.Use"); return; }
                paired = read;
            }
            if (paired is null)
            { Fail<object>(LoweringFailureKind.RuntimeCall, "拆箱地址没有同块内且未跨调用或非帧写入的完整读取", code: "lowering.Unbox.Use"); return; }

            bool UsesAddress(IEnumerable<Term> roots)
            {
                foreach (var root in roots)
                {
                    if (SnapshotRewrite.Dependencies([root]).Contains(definition.Result)) return true;
                    var resolved = context.Get(state.Resolve, root);
                    if (!resolved.IsSuccess)
                    { Fail<object>(LoweringFailureKind.RuntimeCall, "拆箱地址的使用无法解析", resolved.Why, "lowering.Unbox.Use"); return true; }
                    if (SnapshotRewrite.Dependencies([resolved.Value]).Contains(result.Value)) return true;
                }
                return false;
            }
            foreach (var other in function.Blocks)
            {
                if (UsesAddress(other.Merges.SelectMany(m => m.Inputs.Select(v => v.Value)).Concat(SnapshotRewrite.Uses(other.End)))
                    || other.Statements.Where(s => !ReferenceEquals(s, paired)).Any(s => UsesAddress(SnapshotRewrite.Uses(s))))
                { Fail<object>(LoweringFailureKind.RuntimeCall, "拆箱地址还有未配对的使用", code: "lowering.Unbox.Use"); return; }
            }
            var contents = context.Get(state.Read, paired.Identity);
            if (!contents.IsSuccess)
            { Fail<object>(LoweringFailureKind.RuntimeCall, "配对读取没有状态身份", contents.Why, "lowering.Unbox.Use"); return; }
            if (contents.Value.Identity is not MemoryAtom { Location.Region: not Region.Frame } || readValues.ContainsKey(contents.Value))
            { Fail<object>(LoweringFailureKind.RuntimeCall, "配对读取没有独立的非帧读取身份", code: "lowering.Unbox.Use"); return; }
            var readDefinition = new ReadDefinition(paired)
            {
                Constant = IsFloat(definition.Target) ? definition.Local : Mask(definition.Local, definition.Local.Width)
            };
            readValues.Add(contents.Value, readDefinition);
            readDefinitions.Add(paired.Identity, readDefinition);
        }
    }

    private ManagedStatement? LowerUnbox(Call call, Point point)
    {
        var definition = unboxes[call.Identity];
        var obj = CallArgument(definition.Object, types.Object, point);
        if (obj is null) return null;
        if (!ManagedTypes.IsReferenceType(obj.Type))
            return Fail<ManagedStatement>(LoweringFailureKind.RuntimeCall, "拆箱的对象不是引用", code: "lowering.Unbox.Object");
        return new ManagedAssignment(position, definition.Local, new UnboxValue(obj, definition.Target, definition.Local.Width));
    }
}
