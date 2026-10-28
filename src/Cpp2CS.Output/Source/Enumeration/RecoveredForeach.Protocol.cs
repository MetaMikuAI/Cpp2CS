using Cpp2CS.Structure;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

internal sealed partial class RecoveredForeach
{
    private static EnumeratorShape Enumerator(Expression expression) => Enumerator(expression.Annotation<ResolveResult>()?.Type);
    private static EnumeratorShape Enumerator(IType? type) => EnumerationProtocol.Describe(type?.FullName ?? "",
        type?.GetAllBaseTypes().Select(t => t.FullName) ?? [], type?.IsReferenceType);
    private static bool CurrentByReference(MemberReferenceExpression read) => read.GetSymbol() is IProperty { ReturnType: ByReferenceType };
}
