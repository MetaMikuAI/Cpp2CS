using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.IL.Transforms;

namespace Cpp2CS.Extensions.Decompile;

public sealed partial class ReadabilityTransforms
{
    /// <summary>同一异常区域内，共享最终局部赋值相同的纯复制出口。</summary>
    private sealed class CopyBlocks : IILTransform
    {
        public void Run(ILFunction function, ILTransformContext context)
        {
            foreach (var container in function.Descendants.OfType<BlockContainer>().ToArray())
            {
                var canonical = new List<(Block Block, Block Target, Dictionary<ILVariable, ILVariable> Values)>();
                var replacements = new Dictionary<Block, Block>();
                foreach (var block in container.Blocks)
                {
                    if (block == container.EntryPoint || block.Instructions.Count < 2
                        || block.Instructions[^1] is not Branch jump || jump.TargetBlock.Parent != container) continue;
                    var values = new Dictionary<ILVariable, ILVariable>();
                    var valid = true;
                    foreach (var instruction in block.Instructions.SkipLast(1))
                    {
                        if (instruction is not StLoc { Value: LdLoc read } store
                            || store.Variable.Function != function || read.Variable.Function != function
                            || store.Variable.AddressInstructions.Count != 0 || read.Variable.AddressInstructions.Count != 0
                            || !store.Variable.Type.Equals(read.Variable.Type)) { valid = false; break; }
                        values[store.Variable] = values.GetValueOrDefault(read.Variable, read.Variable);
                    }
                    if (!valid) continue;
                    foreach (var variable in values.Keys.ToArray())
                    {
                        // 块内临时量只承载复制快照；其余局部必须保留最终值，交换不能按顺序赋值比较。
                        if (values[variable] == variable || variable.IsSingleDefinition && !variable.UsesInitialValue
                            && variable.LoadInstructions.All(l => l.Parent is StLoc s && s.Parent == block)) values.Remove(variable);
                    }
                    var equivalent = canonical.FirstOrDefault(c => c.Target == jump.TargetBlock && c.Values.Count == values.Count
                        && values.All(p => c.Values.TryGetValue(p.Key, out var source) && source == p.Value));
                    if (equivalent.Block is null) canonical.Add((block, jump.TargetBlock, values));
                    else replacements.Add(block, equivalent.Block);
                }
                if (replacements.Count == 0) continue;
                foreach (var branch in function.Descendants.OfType<Branch>())
                    if (replacements.TryGetValue(branch.TargetBlock, out var target)) branch.TargetBlock = target;
                container.SortBlocks(deleteUnreachableBlocks: true);
            }
        }
    }
}
