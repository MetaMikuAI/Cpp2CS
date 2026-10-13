using System.Collections.Immutable;
using Cpp2CS.SemanticCore;

namespace Cpp2CS.Nir;

// 输入和输出是格式明确的位值；异常是本次计算的六位结果，不读取或修改隐含环境。
public sealed record NirFloat(NirValue Result, NirValue Exceptions, BinaryFloatSpec Spec,
    ImmutableArray<NirValue> Inputs, NirFloatControls? Controls = null) : NirOperation;

public sealed record NirFloatControls(NirValue RoundingMode, NirValue FlushSubnormalInput,
    NirValue FlushSubnormalOutput, NirValue CanonicalNaN, NirValue? ExactTinyUnderflow = null)
{
    public ImmutableArray<NirValue> Values => ExactTinyUnderflow is { } exact
        ? [RoundingMode, FlushSubnormalInput, FlushSubnormalOutput, CanonicalNaN, exact]
        : [RoundingMode, FlushSubnormalInput, FlushSubnormalOutput, CanonicalNaN];
}
