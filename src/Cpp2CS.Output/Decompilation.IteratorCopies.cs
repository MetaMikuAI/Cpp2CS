using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.IL.Transforms;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>合并来源相同的闭包引用副本，避免闭包展开将同一对象拆成不同捕获。</summary>
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
                        || !from.Variable.IsSingleDefinition
                        || copy.Variable.UsesInitialValue || from.Variable.UsesInitialValue
                        || copy.Variable.AddressInstructions.Count != 0 || from.Variable.AddressInstructions.Count != 0
                        || !copy.Variable.Type.Equals(from.Variable.Type)
                        || from.Variable.Type.GetDefinition() is not { } type
                        || type.IsReferenceType != true
                        || !type.Name.Contains("DisplayClass", StringComparison.Ordinal)
                        || !type.GetAttributes().Any(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.CompilerGeneratedAttribute")) continue;
                    var copies = copy.Variable.StoreInstructions.OfType<StLoc>().ToArray();
                    if (copies.Length != copy.Variable.StoreInstructions.Count || copies.Any(c => c.Parent is not Block b || !b.Instructions.Contains(c)
                        || c.Value is not LdLoc value || value.Variable != from.Variable)) continue;
                    // 多个入边必须引用入口处创建的同一对象；循环内反复创建的实例不能合并。
                    if (!copy.Variable.IsSingleDefinition && (from.Variable.StoreInstructions.OfType<StLoc>().ToArray() is not [StLoc { Value: NewObj, Parent: Block allocation }]
                        || function.Body is not BlockContainer body || allocation != body.EntryPoint)) continue;
                    foreach (var read in copy.Variable.LoadInstructions.ToArray())
                    {
                        var replacement = new LdLoc(from.Variable);
                        replacement.AddILRange(read);
                        read.ReplaceWith(replacement);
                    }
                    foreach (var store in copies) ((Block)store.Parent!).Instructions.Remove(store);
                    changed = true;
                }
            } while (changed);
        }
    }
}
