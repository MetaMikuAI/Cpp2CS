using Cpp2CS.Ir;

namespace Cpp2CS.Lifting;

/// <summary>未化简 SSA 的入口读取；未知指令或不完整控制流不能证明参数未用。</summary>
internal static class NativeInputs
{
    public static HashSet<Storage>? Reads(LiftedFunction lifted)
    {
        var statements = lifted.Function.Blocks.SelectMany(b => b.Statements).ToArray();
        if (!lifted.Succeeded || lifted.Function.Problems.Count != 0 || lifted.Function.UnresolvedIndirectJumps != 0
            || statements.Any(s => s is Opaque or IndirectJump { Targets.Length: 0 })) return null;
        return statements.SelectMany(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable)
                .Concat(s is Phi phi ? phi.Sources : []))
            .Where(v => v.Version == 0).Select(v => v.Storage).ToHashSet();
    }
}
