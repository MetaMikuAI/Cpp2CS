using System.Collections.Immutable;
using Cpp2CS.SemanticCore;

namespace Cpp2CS.Nir;

public sealed record NirVectorExpansion(ImmutableArray<NirOperation> Operations, NirValue Result, NirValue? Exceptions);

// Lane 0 位于最低位；固定向量展开为普通 SSA 位段和标量运算，不保留机器容器。
public static class NirVectorMath
{
    public static NirVectorExpansion Integer(NirPureCode code, int count, int laneWidth,
        ImmutableArray<NirValue> inputs, Func<int, NirValue> allocate)
    {
        if (code is not (NirPureCode.Add or NirPureCode.Sub or NirPureCode.Mul or NirPureCode.And or NirPureCode.Or or
            NirPureCode.Xor or NirPureCode.Not or NirPureCode.Shl or NirPureCode.Shr or NirPureCode.Sar or NirPureCode.UDiv or
            NirPureCode.SDiv or NirPureCode.Eq or NirPureCode.Ult or NirPureCode.Slt))
            throw new ArgumentException("向量映射要求独立的标量整数运算", nameof(code));
        CheckInputs(count, laneWidth, inputs, code == NirPureCode.Not ? 1 : 2);
        var operations = ImmutableArray.CreateBuilder<NirOperation>();
        var lanes = ImmutableArray.CreateBuilder<NirValue>();
        for (var lane = 0; lane < count; lane++)
        {
            var arguments = Extract(operations, inputs, lane, laneWidth, allocate);
            var result = allocate(code is NirPureCode.Eq or NirPureCode.Ult or NirPureCode.Slt ? 1 : laneWidth);
            operations.Add(new NirPure(result, code, arguments));
            lanes.Add(result);
        }
        var packed = Pack(operations, lanes.ToImmutable(), allocate);
        return new(operations.ToImmutable(), packed, null);
    }

    public static NirVectorExpansion Floating(BinaryFloatSpec spec, int count,
        ImmutableArray<NirValue> inputs, Func<int, NirValue> allocate, NirFloatControls? controls = null)
    {
        if (spec.Validate() is { } error) throw new ArgumentException(error, nameof(spec));
        CheckInputs(count, spec.OperandWidth, inputs, spec.InputCount);
        if ((long)count * spec.ResultWidth > 4096) throw new ArgumentException("向量输出超过位串上限", nameof(count));
        var operations = ImmutableArray.CreateBuilder<NirOperation>();
        var lanes = ImmutableArray.CreateBuilder<NirValue>();
        NirValue? combined = null;
        for (var lane = 0; lane < count; lane++)
        {
            var arguments = Extract(operations, inputs, lane, spec.OperandWidth, allocate);
            var result = allocate(spec.ResultWidth);
            var flags = allocate(6);
            operations.Add(new NirFloat(result, flags, spec, arguments, controls));
            lanes.Add(result);
            if (combined is { } prior)
            {
                var next = allocate(6);
                operations.Add(new NirPure(next, NirPureCode.Or, [prior, flags]));
                combined = next;
            }
            else combined = flags;
        }
        var packed = Pack(operations, lanes.ToImmutable(), allocate);
        return new(operations.ToImmutable(), packed, combined);
    }

    private static void CheckInputs(int count, int width, ImmutableArray<NirValue> inputs, int arity)
    {
        if (count < 1 || width < 1 || (long)count * width > 4096 || inputs.IsDefault || inputs.Length != arity ||
            inputs.Any(v => v.Type is not NirBitsType bits || bits.Width != count * width))
            throw new ArgumentException("向量输入要求明确 lane 数、宽度及匹配位串");
    }
    private static ImmutableArray<NirValue> Extract(ImmutableArray<NirOperation>.Builder operations,
        ImmutableArray<NirValue> inputs, int lane, int width, Func<int, NirValue> allocate)
    {
        var arguments = ImmutableArray.CreateBuilder<NirValue>();
        foreach (var input in inputs)
        {
            var element = allocate(width);
            operations.Add(new NirPure(element, NirPureCode.Extract, [input], lane * width));
            arguments.Add(element);
        }
        return arguments.ToImmutable();
    }
    private static NirValue Pack(ImmutableArray<NirOperation>.Builder operations, ImmutableArray<NirValue> lanes,
        Func<int, NirValue> allocate)
    {
        var packed = lanes[0];
        for (var lane = 1; lane < lanes.Length; lane++)
        {
            var next = allocate(((NirBitsType)packed.Type).Width + ((NirBitsType)lanes[lane].Type).Width);
            operations.Add(new NirPure(next, NirPureCode.Concat, [lanes[lane], packed]));
            packed = next;
        }
        return packed;
    }
}
