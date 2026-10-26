using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.IL.Transforms;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>成功分配的托管引用非空，消除阻碍闭包展开的原生判空。</summary>
    private sealed class AllocatedNullChecks : IILTransform
    {
        public void Run(ILFunction function, ILTransformContext context)
        {
            var allocated = function.Variables.Where(v => v.IsSingleDefinition && !v.UsesInitialValue && v.AddressInstructions.Count == 0
                && v.Type.IsReferenceType == true && v.StoreInstructions.OfType<StLoc>().ToArray() is [StLoc { Value: NewObj or NewArr }]).ToHashSet();
            foreach (var instruction in function.Descendants.Reverse().ToArray())
            {
                if (instruction.MatchCompEqualsNull(out var equal) && equal is LdLoc first && allocated.Contains(first.Variable))
                    instruction.ReplaceWith(new LdcI4(0));
                else if (instruction.MatchCompNotEqualsNull(out var unequal) && unequal is LdLoc second && allocated.Contains(second.Variable))
                    instruction.ReplaceWith(new LdcI4(1));
            }
            foreach (var instruction in function.Descendants.OfType<IfInstruction>().Reverse().ToArray())
                if (instruction.Condition.MatchLdcI4(out var condition))
                {
                    var selected = (condition != 0 ? instruction.TrueInst : instruction.FalseInst).Clone();
                    selected.AddILRange(instruction);
                    if (selected is Nop && instruction.Parent is Block block && block.Instructions.Contains(instruction)) block.Instructions.Remove(instruction);
                    else instruction.ReplaceWith(selected);
                }
        }
    }
}
