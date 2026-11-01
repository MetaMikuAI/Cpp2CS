using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ThreadStaticBlocksPass
{
    internal static bool ThreadStaticBlocks(this IdiomState state)
    {
        var changed = false;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: null, Target: Const target, Arguments: [Symbol { Kind: SymbolKind.Class, Value: DefinitionRef type }, ..] } call || call.Defines.FirstOrDefault() is not { } result || state.facts.Layouts.Of(type)?.ThreadStatics.Count is not > 0 || state.facts.Code.Word(target.Value) != 0xb9411400 || state.facts.Code.Word(target.Value + 4) is not { } branch || !A64.IsB(branch))
                    continue;
                var lookup = A64.Imm26Target(branch, target.Value + 4);
                // thread_static_fields_offset 的高低 16 位索引经 pthread_getspecific 取得的两级线程表。
                if (state.facts.Code.Word(lookup + 16) != 0x53107c13 || state.facts.Code.Word(lookup + 20) != 0x12003c14 || state.facts.Code.Word(lookup + 32) is not { } get || !A64.IsBl(get) || state.facts.Code.At(A64.Imm26Target(get, lookup + 32))?.Import != "pthread_getspecific" || state.facts.Code.Word(lookup + 36) != 0xf8735808 || state.facts.Code.Word(lookup + 40) != 0xf8745900)
                    continue;
                block.Statements[i] = new Define(call.Address, result, new Symbol(SymbolKind.ThreadStaticFields, type));
                var clobbered = call.Defines.Where(v => v is not null && v != result).ToHashSet();
                foreach (var affected in state.function.Blocks)
                    for (var j = 0; j < affected.Statements.Count; j++)
                        affected.Statements[j] = affected.Statements[j] is Phi phi ? phi with
                        {
                            Sources = phi.Sources.Select(v => clobbered.Contains(v) ? new Variable(v.Storage, -1) : v).ToArray()
                        }

                        : ExprMap.MapOperands(affected.Statements[j], e => ExprMap.Map(e, p => p is Use use && clobbered.Contains(use.Variable) ? new Unknown($"{use.Variable.Storage} 被调用破坏", use.Width) : null));
                changed = true;
            }

        return changed;
    }
}
