using System.Numerics;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private ManagedRangeQuery? ranges;
    private readonly Dictionary<(ReadDefinition Read, LocationView View), ReadDefinition> rangeReads = [];

    private LocationResult? Range(Term address, int width)
    {
        if (locations is null) return null;
        ranges ??= new(locations, types);
        var answer = context.Get(ranges, new(address, width));
        if (!answer.IsSuccess) return Fail<LocationResult>(LoweringFailureKind.State, "访问范围查询失败", answer.Why);
        return answer.Value;
    }

    private bool Writable(LocationView view)
    {
        if (view.Kind == ManagedLocationKind.ArrayLength)
        { Fail<object>(LoweringFailureKind.NonFrameWrite, "数组长度不可写", code: "lowering.Location.Readonly"); return false; }
        // 只读字段只允许在所属类型对应的实例或静态构造函数中写入。
        foreach (var field in view.Path)
            if ((field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
                && !(method.Method.Name == (field.Field.IsStatic ? ".cctor" : ".ctor") && method.Method.Owner == field.Field.Owner))
            { Fail<object>(LoweringFailureKind.NonFrameWrite, "只读字段的写入缺少构造函数上下文", code: "lowering.Location.Readonly"); return false; }
        return true;
    }

    private ManagedValue? RangeRead(ReadDefinition read, int low, int width)
    {
        var usePosition = position;
        position = read.Read.Trace?.NativeAddress ?? position;
        var value = RangeReadAt(read, low, width);
        position = usePosition;
        return value;
    }
    private ManagedValue? RangeReadAt(ReadDefinition read, int low, int width)
    {
        var range = Range(read.Read.Address, read.Read.Width);
        if (range?.Why is { Code: "location.padding" or "location.overlap" or "location.range" } why)
            return Fail<ManagedValue>(LoweringFailureKind.NonFrameRead, why.Message, why, why.Code);
        if (range is null || range.Pieces.IsEmpty) return null;
        var selected = range.Pieces.Where(p => p.AccessBit < low + width && p.AccessBit + p.Width > low).ToArray();
        if (selected.Any(p => p.View is null))
            return Fail<ManagedValue>(LoweringFailureKind.NonFrameRead, "使用访问范围中的填充位", code: "location.padding");
        if (width > 64) return Fail<ManagedValue>(LoweringFailureKind.NonFrameRead, "跨位置的值超过整数栈宽度", code: "lowering.Location.Width");
        ManagedValue result = Constant(0, width);
        foreach (var piece in selected)
        {
            var view = piece.View!;
            int begin = Math.Max(low, piece.AccessBit), end = Math.Min(low + width, piece.AccessBit + piece.Width);
            int bit = piece.LocationBit + begin - piece.AccessBit, bits = end - begin;
            if (ReferenceType(view.Type) && (bit != 0 || bits != types.Size(view.Type) * 8))
                return Fail<ManagedValue>(LoweringFailureKind.NonFrameRead, "引用字段的部分位片不可读取", code: "location.reference-slice");
            var key = (read, view);
            if (!rangeReads.TryGetValue(key, out var snapshot))
            {
                var storage = AccessView(view); if (storage is null) return null;
                var accessor = FieldAccessor(storage, false, read); if (failure is not null) return null;
                snapshot = new(read.Read) { Value = storage, Accessor = accessor, Local = new(new(nextLocal++), storage.Type, storage.Width) };
                rangeReads.Add(key, snapshot);
                if (!structReads.TryGetValue(read.Read.Identity, out var definitions)) structReads.Add(read.Read.Identity, definitions = []);
                definitions.Add(snapshot);
            }
            var value = snapshot.Local!;
            if (selected.Length == 1 && bit == 0 && bits == types.Size(view.Type) * 8) return value;
            var part = Slice(value, bit, bits);
            if (ReferenceType(part.Type)) return Fail<ManagedValue>(LoweringFailureKind.NonFrameRead,
                "引用字段不能拼接成整数", code: "location.reference-bits");
            part = Convert(part, width);
            if (begin != low) part = Binary(BinaryOperator.ShiftLeft, part, Constant((ulong)(begin - low), 32), width);
            result = Binary(BinaryOperator.Or, result, part, width);
        }
        return Mask(result, width);
    }

    // null 表示仍使用完整位置的既有写入；空列表表示失败或没有可观察的字段。
    private IReadOnlyList<ManagedStatement>? RangeStores(MemoryWrite write, Point point)
    {
        if (locations is not null && context.Get(locations, new(write.Address, write.Width)) is { IsSuccess: true } located)
            foreach (var view in located.Value.Views.Where(v => v.Offset == 0 && types.Kind(v.Type) == TypeKind.Struct
                && types.StorageBits(v.Type) == write.Width))
                if (context.Get(structs, new(view.Type, new TermSource(write.Value), point)).IsSuccess) return null;
        var range = Range(write.Address, write.Width);
        if (range?.Why is { Code: "location.padding" or "location.overlap" or "location.range" } why)
        { Fail<object>(LoweringFailureKind.NonFrameWrite, why.Message, why, why.Code); return []; }
        if (range is null || range.Pieces.IsEmpty) return null;
        if (range.Pieces is [{ View: { } only, AccessBit: 0, LocationBit: 0 } wholePiece]
            && wholePiece.Width == types.Size(only.Type) * 8) return null;
        if (RejectAddressUse([write.Value], "写入内存")) return [];
        var statements = new List<ManagedStatement>();
        foreach (var piece in range.Pieces)
        {
            if (piece.View is not { } view) continue;
            if (!Writable(view)) return [];
            int storageBits = types.Size(view.Type) * 8;
            bool partial = piece.LocationBit != 0 || piece.Width != storageBits;
            if (partial && !IntegerType(view.Type))
            { Fail<object>(LoweringFailureKind.NonFrameWrite, "部分写入只支持整数与枚举字段", code: "location.partial-write-type"); return []; }
            var target = AccessView(view, true); if (target is null) return [];
            var setter = FieldAccessor(target, true); if (failure is not null) return [];
            var value = Part(write.Value, piece.AccessBit, piece.Width, IsFloat(view.Type)); if (value is null) return [];
            if (partial)
            {
                var old = AccessView(view); if (old is null) return [];
                var getter = FieldAccessor(old, false); if (failure is not null) return [];
                if (getter is not null)
                {
                    var local = new LocalValue(new(nextLocal++), old.Type, old.Width);
                    statements.Add(new ManagedCall(position, AccessorInvocation(getter, old, []), local) { Inlined = true }); old = local;
                }
                ulong mask = (ulong)(((BigInteger.One << piece.Width) - 1) << piece.LocationBit);
                var kept = Binary(BinaryOperator.And, old, Constant(~mask, storageBits), storageBits);
                value = Convert(Mask(value, piece.Width), storageBits);
                if (piece.LocationBit != 0) value = Binary(BinaryOperator.ShiftLeft, value, Constant((ulong)piece.LocationBit, 32), storageBits);
                value = Binary(BinaryOperator.Or, kept, value, storageBits);
            }
            value = ReferenceType(view.Type) || ManagedTypes.IsNativePointer(view.Type) ? Coerce(value, view.Type)
                : IsFloat(view.Type) ? FloatBits(value, storageBits)
                : new ConversionValue(ManagedTypes.IsSigned(view.Type) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                    IntegerBits(value), view.Type, storageBits);
            statements.Add(setter is null ? new ManagedStore(position, target, value)
                : new ManagedCall(position, AccessorInvocation(setter, target, [value]), null) { Inlined = true });
        }
        return statements;
    }
}
