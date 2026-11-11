using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>ILSpy 的 new (T1,T2) { Item1=... } 不是合法 C#；只还原初始化器的底层类型名，保留元组名特性。</summary>
    private sealed class TupleInitializers : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var creation in rootNode.Descendants.OfType<ObjectCreateExpression>().ToArray())
                if (creation.Type is TupleAstType tuple && creation.Arguments.Count == 0 && creation.Initializer is { Elements.Count: > 0 })
                    creation.Type = Underlying(tuple.Elements.Select(e => e.Type).ToArray());
        }

        private static AstType Underlying(IReadOnlyList<AstType> elements)
        {
            var system = new MemberType(new SimpleType("global"), "System") { IsDoubleColon = true };
            var result = new MemberType(system, "ValueTuple");
            foreach (var element in elements.Take(elements.Count > 7 ? 7 : elements.Count)) result.TypeArguments.Add(element.Clone());
            if (elements.Count > 7) result.TypeArguments.Add(Underlying(elements.Skip(7).ToArray()));
            return result;
        }
    }
}
