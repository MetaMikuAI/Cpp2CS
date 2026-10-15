using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Runtime;

namespace Cpp2CS.Managed;

public sealed partial class ValueRecovery
{
    private ArrayRef? HelperResultType(Call call) => session.Resolver.Resolve(call) is HelperCallee { Helper.Kind: HelperKind.NewArray }
        && HelperArgument(call, 0) is { } type && Metadata.Usage(type) is { Kind: UsageKind.TypeInfo, Value: ArrayRef { Rank: 1, IsVector: true } array }
        ? array : null;

    private static Expr? HelperArgument(Call call, int index)
    {
        var source = Array.IndexOf(call.Sources, Storage.Gpr(index));
        return source >= 0 && source < call.Arguments.Length ? call.Arguments[source] : null;
    }

    public ManagedValue? HelperValue(Call call, out string? problem)
    {
        problem = null;
        if (HelperResultType(call) is not { } array) return Fail("运行时调用的类型或操作尚未恢复", out problem);
        if (HelperArgument(call, 1) is not { } native) return Fail("数组分配缺少长度来源", out problem);
        if (Recover(native, out problem) is not { } length) return null;
        if (types.Kind(length.Type) != ValueKind.Int || length.Width is not (32 or 64)) return Fail("数组长度不是整数", out problem);
        return new NewArrayValue(array, length);
    }

    // 当前管线为 64 位 IL2CPP：对象头后依次为 bounds 指针、max_length 和元素。
    private ArrayLengthValue? ArrayLength(Load load)
    {
        if (load.Width is not (32 or 64) || load.Address is not Binary { Op: BinOp.Add, Right: Const offset } add
            || offset.Value != (ulong)(types.HeaderSize + 8)) return null;
        return Recover(add.Left, out _) is { Type: ArrayRef { Rank: 1, IsVector: true } } array
            ? new(array, types.Integer(load.Width, false), load.Width) : null;
    }

    private ArrayElementValue? ArrayElement(Expr address, int width)
    {
        var terms = new List<Expr>();
        void Add(Expr value)
        {
            if (value is Binary { Op: BinOp.Add, Width: 64 } sum) { Add(sum.Left); Add(sum.Right); }
            else terms.Add(value);
        }
        Add(address);
        if (terms.Count < 2) return null;
        ManagedValue? array = null;
        Expr? scaled = null;
        ulong offset = 0;
        foreach (var term in terms)
        {
            if (term is Const constant) { offset = unchecked(offset + constant.Value); continue; }
            if (Recover(term, out _) is { Type: ArrayRef { Rank: 1, IsVector: true } } candidate)
            {
                if (array is not null) return null;
                array = candidate;
            }
            else
            {
                if (scaled is not null) return null;
                scaled = term;
            }
        }
        if (array?.Type is not ArrayRef arrayType) return null;
        var size = types.Size(arrayType.Element);
        if (size <= 0 || width != size * 8) return null;
        var header = (ulong)(types.HeaderSize + 16);
        if (offset < header || (offset - header) % (ulong)size != 0) return null;
        var bias = (offset - header) / (ulong)size;
        ManagedValue index = new ConstantValue(bias, types.UInt64, 64);
        if (scaled is not null)
        {
            Expr? native = scaled switch
            {
                Binary { Op: BinOp.Shl, Width: 64, Right: Const shift } b when shift.Value < 63 && (1UL << (int)shift.Value) == (ulong)size => b.Left,
                Binary { Op: BinOp.Mul, Width: 64, Right: Const factor } b when factor.Value == (ulong)size => b.Left,
                _ when size == 1 => scaled,
                _ => null,
            };
            if (native is null || Recover(native, out _) is not { Width: 64 } variable || types.Kind(variable.Type) != ValueKind.Int) return null;
            index = bias == 0 ? variable : new BinaryValue(BinOp.Add, variable, index, types.UInt64, 64);
        }
        return new(array, index, arrayType.Element, width);
    }
}
