using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.IL.Transforms;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>合并单次赋值的闭包引用副本，避免闭包展开将同一对象拆成不同捕获。</summary>
    private sealed class IteratorCopies : IILTransform
    {
        public void Run(ILFunction function, ILTransformContext context)
        {
            bool changed;
            do
            {
                changed = false;
                foreach (var copy in function.Descendants.OfType<StLoc>().ToArray())
                {
                    if (copy.Parent is not Block block || !block.Instructions.Contains(copy) || copy.Value is not LdLoc from || copy.Variable == from.Variable
                        || copy.Variable.Function != function || from.Variable.Function != function
                        || !copy.Variable.IsSingleDefinition || !from.Variable.IsSingleDefinition
                        || copy.Variable.UsesInitialValue || from.Variable.UsesInitialValue
                        || copy.Variable.AddressInstructions.Count != 0 || from.Variable.AddressInstructions.Count != 0
                        || !copy.Variable.Type.Equals(from.Variable.Type)
                        || from.Variable.Type.GetDefinition() is not { } type
                        || type.IsReferenceType != true
                        || !type.Name.Contains("DisplayClass", StringComparison.Ordinal)
                        || !type.GetAttributes().Any(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.CompilerGeneratedAttribute")) continue;
                    foreach (var read in copy.Variable.LoadInstructions.ToArray())
                    {
                        var replacement = new LdLoc(from.Variable);
                        replacement.AddILRange(read);
                        read.ReplaceWith(replacement);
                    }
                    block.Instructions.Remove(copy);
                    changed = true;
                }
            } while (changed);
        }
    }
}
