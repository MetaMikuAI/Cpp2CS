using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Transforms;

namespace Cpp2CS.Extensions.Decompile;

public sealed partial class ReadabilityTransforms : IDecompileTransformProvider
{
    public static ReadabilityTransforms Instance { get; } = new();
    public void Register(CSharpDecompiler decompiler, DecompilePosition position)
    {
        if (position == DecompilePosition.BeforeLegality)
        {
            decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ICSharpCode.Decompiler.IL.ControlFlow.SwitchDetection), new BranchResults());
            decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ICSharpCode.Decompiler.IL.ControlFlow.SwitchDetection), new ICSharpCode.Decompiler.IL.Transforms.ILInlining());
            decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ICSharpCode.Decompiler.IL.ControlFlow.SwitchDetection), new CopyBlocks());
            decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ICSharpCode.Decompiler.IL.Transforms.DelegateConstruction), new AllocatedNullChecks());
            decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ICSharpCode.Decompiler.IL.Transforms.DelegateConstruction), new IteratorCopies());
            decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ICSharpCode.Decompiler.IL.Transforms.TransformDisplayClassUsage), new ClosureLinks());
            decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ICSharpCode.Decompiler.IL.Transforms.TransformDisplayClassUsage), new IteratorCopies());
            decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ICSharpCode.Decompiler.IL.Transforms.TransformDisplayClassUsage), new AllocatedNullChecks());
            decompiler.AstTransforms.Insert(decompiler.AstTransforms.ToList().FindIndex(t => t is IntroduceQueryExpressions), new PreserveLambdaOrigins());
            decompiler.AstTransforms.Add(new EnumeratorCopies());
        }
        if (position == DecompilePosition.AfterLegality)
        {
            decompiler.AstTransforms.Add(new AsyncMarkers());
            decompiler.AstTransforms.Add(new RecoveredForeach());
        }
        if (position == DecompilePosition.AfterEvents)
        {
            decompiler.AstTransforms.Add(new ConstructorFields());
            decompiler.AstTransforms.Add(new CompilerScaffolding());
        }
    }
}
