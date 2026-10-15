using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Ssa;

/// <summary>寄存器层的 SSA 降级：填写调用约定 → 构建 SSA → 校验 → 传播与清理 → 再校验。</summary>
public static class Lowering
{
    /// <summary>返回 SSA 不变量错误（构建阶段的错误带“构建: ”前缀）；空表示成功。</summary>
    public static List<string> Registers(MachineFunction function, CallingConvention convention, ICallModel calls, Expr? returnValue)
    {
        var dominators = Dominators.Compute(function);
        SsaBuilder.PrepareCalls(function, calls, returnValue);
        SsaBuilder.Build(function, dominators, s => s.Bank is Bank.Gpr or Bank.Vec or Bank.Flags or Bank.Temp, calls, convention.StackPointer);
        var errors = SsaCheck.Verify(function, dominators);
        if (errors.Count > 0) return errors.Select(e => "构建: " + e).ToList();
        Propagate.Run(function, dominators);
        return SsaCheck.Verify(function, dominators);
    }
}
