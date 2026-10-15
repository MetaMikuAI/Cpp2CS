using System.Collections.Concurrent;
using System.Reflection.Metadata;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.OutputVisitor;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Metadata;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

/// <summary>一个顶层类型（含其嵌套类型）的 C# 源码；程序集级特性单独作为一份，TypeName 为空。</summary>
public sealed record SourceFile(string? TypeName, string Namespace, string Source);

/// <summary>用 ICSharpCode.Decompiler 把写出的程序集还原成 C#，按顶层类型分文件。</summary>
public static class Decompilation
{
    public static DecompilerSettings Settings(bool recoveringBodies = false) => new()
    {
        ThrowOnAssemblyResolveErrors = true,
        // 恢复中的方法与骨架混合存在，自动属性变换可能隐藏仍被方法体引用的字段。
        AutomaticProperties = !recoveringBodies,
        GetterOnlyAutomaticProperties = !recoveringBodies,
        FieldKeyword = !recoveringBodies,
        StructDefaultConstructorsAndFieldInitializers = !recoveringBodies,
    };

    /// <summary>与 ILSpy 导出工程（WholeProjectDecompiler）相同的附加变换：转义非法标识符（编译器生成的名字）、去掉 CLSCompliant。</summary>
    private static CSharpDecompiler CreateDecompiler(DecompilerTypeSystem typeSystem, DecompilerSettings settings)
    {
        var decompiler = new CSharpDecompiler(typeSystem, settings);
        decompiler.AstTransforms.Add(new EscapeInvalidIdentifiers());
        decompiler.AstTransforms.Add(new RemoveCLSCompliantAttribute());
        decompiler.AstTransforms.Add(new StrippedMathConstants());
        return decompiler;
    }

    /// <summary>
    /// ILSpy 把等于 π、e 的浮点常量写成 Math.PI / Math.E，但不检查 Math 是否还有该常量（float 的 MathF 会检查）。
    /// 裁剪后的 mscorlib 可能没有这两个字段：此时改回字面值。
    /// </summary>
    private sealed class StrippedMathConstants : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            var math = context.TypeSystem.FindType(typeof(Math)).GetDefinition();
            var present = math?.Fields.Where(f => f.IsConst).Select(f => f.Name).ToHashSet() ?? [];
            foreach (var reference in rootNode.Descendants.OfType<MemberReferenceExpression>().ToArray())
            {
                if (reference.MemberName is not ("PI" or "E") || present.Contains(reference.MemberName)) continue;
                if (reference.Target is not TypeReferenceExpression { Type: SimpleType { Identifier: "Math" } }) continue;
                reference.ReplaceWith(new PrimitiveExpression(reference.MemberName == "PI" ? Math.PI : Math.E));
            }
        }
    }

    /// <summary>
    /// 反编译 <paramref name="assemblyPath"/> 中满足 <paramref name="include"/> 的顶层类型，
    /// 依赖从 <paramref name="searchDirectory"/> 解析。共享一个类型系统，并行反编译各类型。
    /// </summary>
    public static IReadOnlyList<SourceFile> Decompile(string assemblyPath, string searchDirectory, Func<ITypeDefinition, bool> include, bool assemblyAttributes,
        bool recoveringBodies = false)
    {
        var file = new PEFile(assemblyPath);
        var resolver = new UniversalAssemblyResolver(assemblyPath, true, file.DetectTargetFrameworkId());
        resolver.AddSearchDirectory(searchDirectory);
        var settings = Settings(recoveringBodies);
        var typeSystem = new DecompilerTypeSystem(file, resolver, settings);
        var types = typeSystem.MainModule.TopLevelTypeDefinitions
            .Where(t => t.Name != "<Module>" && include(t))
            .Select(t => ((TypeDefinitionHandle)t.MetadataToken, t.Namespace, t.ReflectionName))
            .ToArray();
        var results = new ConcurrentBag<(int Index, SourceFile File)>();
        Parallel.For(0, types.Length, i =>
        {
            var (handle, ns, name) = types[i];
            var tree = CreateDecompiler(typeSystem, settings).DecompileTypes([handle]);
            results.Add((i, new SourceFile(name, ns, Print(tree, settings))));
        });
        var files = results.OrderBy(r => r.Index).Select(r => r.File).ToList();
        if (assemblyAttributes)
        {
            var decompiler = CreateDecompiler(typeSystem, settings);
            decompiler.AstTransforms.Add(new RemoveCompilerGeneratedAssemblyAttributes());
            var tree = decompiler.DecompileModuleAndAssemblyAttributes();
            // ILSpy 按程序集版本合成 [assembly: AssemblyVersion]；0.0.0.0 是不写该特性时的默认值，去掉（AssemblyVersionAttribute 可能已被裁剪）
            foreach (var attribute in tree.Descendants.OfType<ICSharpCode.Decompiler.CSharp.Syntax.Attribute>().ToArray())
                if (attribute.Type.ToString() == "AssemblyVersion" && attribute.Arguments.SingleOrDefault() is PrimitiveExpression { Value: "0.0.0.0" })
                    attribute.Remove();
            foreach (var section in tree.Descendants.OfType<AttributeSection>().Where(s => s.Attributes.Count == 0).ToArray()) section.Remove();
            files.Add(new SourceFile(null, "", Print(tree, settings)));
        }
        return files;
    }

    private static string Print(SyntaxTree tree, DecompilerSettings settings)
    {
        var writer = new StringWriter();
        tree.AcceptVisitor(new CSharpOutputVisitor(writer, settings.CSharpFormattingOptions));
        return writer.ToString();
    }
}
