using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.IL.Transforms;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>只被分支读取的布尔合流值可在前驱直接判断，保留求值次数与异常区域。</summary>
    private sealed class BranchResults : IILTransform
    {
        public void Run(ILFunction function, ILTransformContext context)
        {
            foreach (var container in function.Descendants.OfType<BlockContainer>().ToArray())
            {
                var changed = false;
                foreach (var target in container.Blocks.ToArray())
                {
                    if (target.Instructions.Count != 2 || target.Instructions[0] is not IfInstruction branch
                        || target.Instructions[1] is not (Branch or Leave)) continue;
                    var condition = branch.Condition;
                    while (condition.MatchLogicNot(out var operand)) condition = operand;
                    if (condition is not LdLoc read || !read.Variable.Type.IsKnownType(KnownTypeCode.Boolean)
                        || read.Variable.Function != function || read.Variable.LoadInstructions.Count != 1
                        || read.Variable.AddressInstructions.Count != 0 || read.Variable.UsesInitialValue) continue;
                    foreach (var block in container.Blocks.ToArray())
                    {
                        if (block == target || block.Instructions.Count < 2 || block.Instructions[^1] is not Branch jump || jump.TargetBlock != target
                            || block.Instructions[^2] is not StLoc store || store.Variable != read.Variable) continue;
                        var replacement = (IfInstruction)branch.Clone();
                        replacement.Condition.Descendants.OfType<LdLoc>().Single(l => l.Variable == read.Variable).ReplaceWith(store.Value.Clone());
                        replacement.AddILRange(store);
                        block.Instructions[^2] = replacement;
                        block.Instructions[^1] = target.Instructions[1].Clone();
                        changed = true;
                    }
                }
                if (changed) container.SortBlocks(deleteUnreachableBlocks: true);
            }
        }
    }
}
