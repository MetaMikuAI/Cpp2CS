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
public static partial class Decompilation
{
    public static DecompilerSettings Settings(bool recoveringBodies = false) => new()
    {
        ThrowOnAssemblyResolveErrors = true,
        AutomaticProperties = true,
        GetterOnlyAutomaticProperties = true,
        AggressiveInlining = true,
        FieldKeyword = !recoveringBodies,
        StructDefaultConstructorsAndFieldInitializers = !recoveringBodies,
    };

    /// <summary>与 ILSpy 导出工程（WholeProjectDecompiler）相同的附加变换：转义非法标识符（编译器生成的名字）、去掉 CLSCompliant。</summary>
    private static CSharpDecompiler CreateDecompiler(DecompilerTypeSystem typeSystem, DecompilerSettings settings, IDecompileTransformProvider? transforms)
    {
        var decompiler = new CSharpDecompiler(typeSystem, settings);
        decompiler.AstTransforms.Insert(decompiler.AstTransforms.ToList().FindIndex(t => t is DeclareVariables), new DistinctLocalNames());
        transforms?.Register(decompiler, DecompilePosition.BeforeLegality);
        decompiler.AstTransforms.Add(new EscapeInvalidIdentifiers());
        decompiler.AstTransforms.Add(new RemoveCLSCompliantAttribute());
        decompiler.AstTransforms.Add(new StrippedMathConstants());
        decompiler.AstTransforms.Add(new WritableUnboxing());
        decompiler.AstTransforms.Add(new TupleInitializers());
        transforms?.Register(decompiler, DecompilePosition.AfterLegality);
        decompiler.AstTransforms.Add(new EventFieldNames());
        transforms?.Register(decompiler, DecompilePosition.AfterEvents);
        return decompiler;
    }

    /// <summary>unbox 得到的可写引用不能用 C# 强制转换作左值；目标库有对应接口时输出 Unsafe.Unbox。</summary>
    private sealed class WritableUnboxing : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            var available = context.TypeSystem.Modules.SelectMany(m => m.TopLevelTypeDefinitions)
                .Where(t => t.FullName == "System.Runtime.CompilerServices.Unsafe")
                .SelectMany(t => t.Methods).Any(m => m.Name == "Unbox" && m.IsStatic && m.Accessibility == Accessibility.Public && m.TypeParameters.Count == 1
                    && m.Parameters.Count == 1 && m.Parameters[0].Type.FullName == "System.Object" && m.ReturnType is ByReferenceType);
            if (!available) return;
            foreach (var assignment in rootNode.Descendants.OfType<AssignmentExpression>().ToArray())
            {
                if (assignment.Operator != AssignmentOperatorType.Assign || assignment.Left is not CastExpression cast
                    || !cast.Annotations.OfType<ICSharpCode.Decompiler.IL.Unbox>().Any()) continue;
                AstType type = new MemberType(new SimpleType("global"), "System") { IsDoubleColon = true };
                type = new MemberType(new MemberType(new MemberType(type, "Runtime"), "CompilerServices"), "Unsafe");
                var method = new MemberReferenceExpression(new TypeReferenceExpression(type), "Unbox");
                method.TypeArguments.Add(cast.Type.Clone());
                cast.ReplaceWith(new InvocationExpression(method, cast.Expression.Clone()));
            }
        }
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
        bool recoveringBodies = false, bool groupByName = false, IDecompileTransformProvider? transforms = null)
    {
        var file = new PEFile(assemblyPath);
        var resolver = new UniversalAssemblyResolver(assemblyPath, true, file.DetectTargetFrameworkId());
        resolver.AddSearchDirectory(searchDirectory);
        var settings = Settings(recoveringBodies);
        var typeSystem = new DecompilerTypeSystem(file, resolver, settings);
        var types = typeSystem.MainModule.TopLevelTypeDefinitions
            .Where(t => t.Name != "<Module>" && include(t))
            .GroupBy(t => (t.Namespace, Name: groupByName ? t.Name.Split('`')[0] : t.ReflectionName))
            .Select(g => (Handles: g.Select(t => (TypeDefinitionHandle)t.MetadataToken).ToArray(), g.Key.Namespace,
                Name: groupByName && g.Key.Namespace.Length > 0 ? g.Key.Namespace + "." + g.Key.Name : g.Key.Name))
            .ToArray();
        var results = new ConcurrentBag<(int Index, SourceFile File)>();
        Parallel.For(0, types.Length, i =>
        {
            var (handles, ns, name) = types[i];
            var tree = CreateDecompiler(typeSystem, settings, transforms).DecompileTypes(handles);
            results.Add((i, new SourceFile(name, ns, Print(tree, settings))));
        });
        var files = results.OrderBy(r => r.Index).Select(r => r.File).ToList();
        if (assemblyAttributes)
        {
            var decompiler = CreateDecompiler(typeSystem, settings, transforms);
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
