using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Idioms;

/// <summary>
/// IL2CPP 的 catch 先判断异常的类是否匹配，不匹配时再次抛出。托管异常都是 System.Exception，
/// catch (Exception) 的这次判断恒成立，折叠之后再次抛出的路径和它的清理都不可达。
/// </summary>
internal static class CaughtExceptionChecks
{
    public static bool Run(MachineFunction function, Func<Expr, Expr> expand)
    {
        var caught = function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
            .Where(c => c.Op?.Kind == OpKind.BeginCatch).SelectMany(c => c.Defines.OfType<Variable>()).ToHashSet();
        if (caught.Count == 0) return false;
        var changed = false;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Call { Op.Kind: OpKind.IsAssignableFrom, Arguments: [var klass, var objectClass], Defines: [{ } result] } check
                    && expand(klass) is Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.FullName: "System.Exception" } }
                    && expand(objectClass) is Load { Address: Load { Address: Use { Variable: var exception } } } && caught.Contains(exception))
                {
                    block.Statements[i] = new Define(check.Address, result, Expr.C(1, 64));
                    changed = true;
                }
        return changed;
    }
}
