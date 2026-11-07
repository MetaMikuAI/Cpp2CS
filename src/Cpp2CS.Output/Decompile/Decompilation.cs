using System.Collections.Concurrent;
using System.Reflection.Metadata;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.OutputVisitor;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.IL.ControlFlow;
using ICSharpCode.Decompiler.IL.Transforms;
using ICSharpCode.Decompiler.Metadata;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

/// <summary>一个顶层类型（含其嵌套类型）的 C# 源码；程序集级特性单独作为一份，TypeName 为空。</summary>
public sealed record SourceFile(string? TypeName, string Namespace, string Source);

/// <summary>用 ICSharpCode.Decompiler 把写出的程序集还原成 C#，按顶层类型分文件。</summary>
public static partial class Decompilation
{
    /// <summary>目标语言版本：Unity 2022.3 的编译器支持到 C# 9.0。</summary>
    public const string TargetLanguageVersion = "9.0";

    public static DecompilerSettings Settings() => new(LanguageVersion.CSharp9_0)
    {
        ThrowOnAssemblyResolveErrors = true,
        AutomaticProperties = true,
        GetterOnlyAutomaticProperties = true,
        AggressiveInlining = true,
    };

    /// <summary>与 ILSpy 导出工程（WholeProjectDecompiler）相同的附加变换：转义非法标识符（编译器生成的名字）、去掉 CLSCompliant。</summary>
    private static CSharpDecompiler CreateDecompiler(DecompilerTypeSystem typeSystem, DecompilerSettings settings, IDecompileTransformProvider? transforms)
    {
        var decompiler = new CSharpDecompiler(typeSystem, settings);
        decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ILInlining) + 1, new MergedArrayInitializers());
        decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is MergedArrayInitializers) + 1, new ClosureValues());
        decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is ClosureValues) + 1, new ImplicitChecks());
        decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is AsyncAwaitDecompiler) + 1, new ClosureValues());
        decompiler.ILTransforms.Insert(decompiler.ILTransforms.ToList().FindIndex(t => t is AsyncAwaitDecompiler) + 2, new ImplicitChecks());
        decompiler.AstTransforms.Insert(decompiler.AstTransforms.ToList().FindIndex(t => t is DeclareVariables), new GotoCleanup());
        decompiler.AstTransforms.Insert(decompiler.AstTransforms.ToList().FindIndex(t => t is DeclareVariables), new DistinctLocalNames());
        transforms?.Register(decompiler, DecompilePosition.BeforeLegality);
        decompiler.AstTransforms.Add(new InitializerOrder());
        decompiler.AstTransforms.Add(new ConstructorCalls());
        decompiler.AstTransforms.Add(new StructConstructors());
        decompiler.AstTransforms.Add(new LibraryInternals());
        decompiler.AstTransforms.Add(new ExpressionForms());
        decompiler.AstTransforms.Add(new BooleanIntegers());
        decompiler.AstTransforms.Add(new CachedLambdas());
        decompiler.AstTransforms.Add(new ShadowedLocals());
        decompiler.AstTransforms.Add(new DefiniteAssignment());
        decompiler.AstTransforms.Add(new MemberTokens());
        decompiler.AstTransforms.Add(new NullConditionalReceivers());
        decompiler.AstTransforms.Add(new ReferenceNullTests());
        decompiler.AstTransforms.Add(new EscapeInvalidIdentifiers());
        decompiler.AstTransforms.Add(new RemoveCLSCompliantAttribute());
        decompiler.AstTransforms.Add(new StrippedMathConstants());
        decompiler.AstTransforms.Add(new WritableUnboxing());
        decompiler.AstTransforms.Add(new TupleInitializers());
        decompiler.AstTransforms.Add(new InaccessibleAttributes());
        decompiler.AstTransforms.Add(new InterfaceTupleNames());
        decompiler.AstTransforms.Add(new ForwardingImplementations());
        transforms?.Register(decompiler, DecompilePosition.AfterLegality);
        decompiler.AstTransforms.Add(new FieldLikeEvents());
        decompiler.AstTransforms.Add(new EventFieldNames());
        transforms?.Register(decompiler, DecompilePosition.AfterEvents);
        return decompiler;
    }

    /// <summary>unbox 得到的可写引用不能用 C# 强制转换作左值；目标库有对应接口时输出 Unsafe.Unbox。</summary>
    private sealed class WritableUnboxing : IAstTransform
    {
        /// <summary>每个类型都运行这个变换，全模块查找的结果按类型系统缓存。</summary>
        private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<IDecompilerTypeSystem, object> Availability = new();

        private static object Available(IDecompilerTypeSystem typeSystem) => typeSystem.Modules.SelectMany(m => m.TopLevelTypeDefinitions)
            .Where(t => t.FullName == "System.Runtime.CompilerServices.Unsafe")
            .SelectMany(t => t.Methods).Any(m => m.Name == "Unbox" && m.IsStatic && m.Accessibility == Accessibility.Public && m.TypeParameters.Count == 1
                && m.Parameters.Count == 1 && m.Parameters[0].Type.FullName == "System.Object" && m.ReturnType is ByReferenceType);

        public void Run(AstNode rootNode, TransformContext context)
        {
            if (!(bool)Availability.GetValue(context.TypeSystem, Available)) return;
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
        bool groupByName = false, IDecompileTransformProvider? transforms = null, Func<string>? stubs = null)
    {
        var file = new PEFile(assemblyPath);
        var resolver = new UniversalAssemblyResolver(assemblyPath, true, file.DetectTargetFrameworkId());
        resolver.AddSearchDirectory(searchDirectory);
        var settings = Settings();
        var typeSystem = new DecompilerTypeSystem(file, resolver, settings);
        (string Namespace, string Name) Key(ITypeDefinition t) => (t.Namespace, groupByName ? t.Name.Split('`')[0] : t.ReflectionName);
        (string Namespace, string Name) Named(ITypeDefinition t) => Key(t) is var (ns, name) ? (ns, groupByName && ns.Length > 0 ? ns + "." + name : name) : default;
        var types = typeSystem.MainModule.TopLevelTypeDefinitions
            .Where(t => t.Name != "<Module>" && include(t))
            .GroupBy(t => Key(t))
            .Select(g => (Handles: g.Select(t => (TypeDefinitionHandle)t.MetadataToken).ToArray(), g.Key.Namespace,
                Name: groupByName && g.Key.Namespace.Length > 0 ? g.Key.Namespace + "." + g.Key.Name : g.Key.Name))
            .ToArray();
        var results = new ConcurrentBag<(int Index, SourceFile File)>();
        var failed = new ConcurrentBag<(string Namespace, string Name, string Reason)>();
        // 逐个分发：默认分块会把相邻的大类型留在同一线程上串行。
        Parallel.ForEach(Partitioner.Create(Enumerable.Range(0, types.Length), EnumerablePartitionerOptions.NoBuffering), i =>
        {
            var (handles, ns, name) = types[i];
            try
            {
                var tree = CreateDecompiler(typeSystem, settings, transforms).DecompileTypes(handles);
                results.Add((i, new SourceFile(name, ns, Print(tree, settings))));
            }
            // 只有调用方提供了占位程序集才继续（--keep-going）；否则照常中断。
            catch (Exception e) when (stubs is not null)
            {
                failed.Add((ns, name, e.GetType().Name));
            }
        });
        var files = results.OrderBy(r => r.Index).Select(r => r.File).ToList();
        ReferencedHiddenTypes(files, types, typeSystem, settings, transforms);
        if (!failed.IsEmpty)
        {
            // 反编译失败的类型退回成占位体，工程的结构仍然完整。
            var directory = stubs!();
            var wanted = failed.ToDictionary(f => (f.Namespace, f.Name), f => f.Reason);
            foreach (var source in Decompile(Path.Combine(directory, Path.GetFileName(assemblyPath)), directory, t => wanted.ContainsKey(Named(t)), false, groupByName, transforms))
                files.Add(source with { Source = $"// 反编译失败（{wanted[(source.Namespace, source.TypeName!)]}），这个类型只有占位体。\n{source.Source}" });
        }
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

    /// <summary>
    /// 反编译器默认隐藏匿名类型、闭包和 PrivateImplementationDetails，用处还原成 new { }、lambda、数组初始化器和字符串 switch。
    /// 没还原的地方仍按名字引用它们：这时单独写出被引用的声明；引用闭包的成员不折叠闭包，否则 lambda 和闭包类型对不上。
    /// </summary>
    private static void ReferencedHiddenTypes(List<SourceFile> files, (TypeDefinitionHandle[] Handles, string Namespace, string Name)[] types,
        DecompilerTypeSystem typeSystem, DecompilerSettings settings, IDecompileTransformProvider? transforms)
    {
        void Redo((TypeDefinitionHandle[] Handles, string Namespace, string Name) type, Action<DecompilerSettings> configure)
        {
            var visible = settings.Clone();
            configure(visible);
            var index = files.FindIndex(f => f.TypeName == type.Name && f.Namespace == type.Namespace);
            var source = new SourceFile(type.Name, type.Namespace, Print(CreateDecompiler(typeSystem, visible, transforms).DecompileTypes(type.Handles), visible));
            if (index >= 0) files[index] = source; else files.Add(source);
        }
        // 反编译器有时折叠不了某个方法的闭包，留下对隐藏类型的引用。只把这些成员换成不折叠的写法，再补上它们用到的闭包，其余成员保持折叠。
        // 不折叠后匿名类型也会按名字出现；局部函数同样是闭包折叠的结果，要一起关掉。
        // 迭代器同理：带 try 的 MoveNext 没有还原成 Roslyn 的形态，提升出来的 yield 丢了语义，这些成员保留状态机。
        void Expose((TypeDefinitionHandle[] Handles, string Namespace, string Name) type, bool closures, bool iterators)
        {
            var folded = CreateDecompiler(typeSystem, settings, transforms).DecompileTypes(type.Handles);
            if (closures)
            {
                var visible = settings.Clone();
                visible.AnonymousMethods = false;
                visible.AnonymousTypes = false;
                visible.LocalFunctions = false;
                MergeHidden(folded, CreateDecompiler(typeSystem, visible, transforms).DecompileTypes(type.Handles),
                    text => ClosureReference.IsMatch(text) || ClosureThis.IsMatch(text) || LambdaMethod.IsMatch(text));
            }
            if (iterators)
            {
                var visible = settings.Clone();
                visible.YieldReturn = false;
                MergeHidden(folded, CreateDecompiler(typeSystem, visible, transforms).DecompileTypes(type.Handles), BrokenIterator.IsMatch);
            }
            files[files.FindIndex(f => f.TypeName == type.Name && f.Namespace == type.Namespace)] = new SourceFile(type.Name, type.Namespace, Print(folded, settings));
        }
        var visibleClosures = new HashSet<TypeDefinitionHandle>();
        foreach (var type in types)
        {
            var file = files.Find(f => f.TypeName == type.Name && f.Namespace == type.Namespace);
            if (file is null) continue;
            var closures = ClosureReference.Matches(file.Source).Select(m => m.Value).Distinct();
            var declared = DeclaredLambdaMethod.Matches(file.Source).Select(m => m.Groups[1].Value).ToHashSet();
            var hiddenClosures = closures.Any(c => !file.Source.Contains("class " + c, StringComparison.Ordinal)) || ClosureThis.IsMatch(file.Source)
                || !LambdaMethod.Matches(file.Source).All(m => declared.Contains(m.Value));
            var brokenIterators = BrokenIterator.IsMatch(file.Source);
            if (!hiddenClosures && !brokenIterators) continue;
            Expose(type, hiddenClosures, brokenIterators);
            if (hiddenClosures) visibleClosures.Add(type.Handles[0]);
        }
        // 按名字引用匿名类型的文件里，new { } 也要写成同一个类型。
        foreach (var type in types)
        {
            if (type.Name.StartsWith("<>f__AnonymousType", StringComparison.Ordinal) || type.Name == "<PrivateImplementationDetails>" || visibleClosures.Contains(type.Handles[0])) continue;
            var file = files.Find(f => f.TypeName == type.Name && f.Namespace == type.Namespace);
            if (file is not null && file.Source.Contains("_003C_003Ef__AnonymousType", StringComparison.Ordinal)) Redo(type, s => s.AnonymousTypes = false);
        }
        var used = new HashSet<string>(files.SelectMany(f => HiddenReference.Matches(f.Source).Select(m => m.Value)));
        foreach (var type in types)
        {
            var escaped = type.Name.Replace("<", "_003C").Replace(">", "_003E");
            if (type.Name.StartsWith("<>f__AnonymousType", StringComparison.Ordinal) && used.Contains(escaped)) Redo(type, s => s.AnonymousTypes = false);
            else if (type.Name == "<PrivateImplementationDetails>" && used.Contains(escaped)) Redo(type, s => s.ArrayInitializers = false);
        }
    }

    /// <summary>
    /// folded 里 <paramref name="broken"/> 匹配的成员换成 expanded 里对应的写法，再把用到的闭包类、状态机、lambda 方法和字段按需加进来。
    /// 没提升的状态机是嵌套类型，它的成员用到的闭包声明在外层，所以名字要沿外层类型查找。
    /// </summary>
    private static void MergeHidden(SyntaxTree folded, SyntaxTree expanded, Func<string, bool> broken)
    {
        const string Shared = "_003C_003Ec";
        static int Token(AstNode node) => node.GetSymbol() is IEntity entity ? System.Reflection.Metadata.Ecma335.MetadataTokens.GetToken(entity.MetadataToken) : 0;
        static string? Declared(EntityDeclaration member) => member is FieldDeclaration field ? field.Variables.FirstOrDefault()?.Name : member.Name;
        // 换进来的成员按 expanded 的 using 写短名。
        var imports = folded.Members.OfType<UsingDeclaration>().Select(u => u.ToString()).ToHashSet();
        foreach (var import in expanded.Members.OfType<UsingDeclaration>())
            if (imports.Add(import.ToString())) folded.Members.InsertBefore(folded.Members.First(), (UsingDeclaration)import.Clone());
        var twins = expanded.Descendants.OfType<TypeDeclaration>().Where(t => Token(t) != 0).GroupBy(Token).ToDictionary(g => g.Key, g => g.First());
        var targets = folded.Descendants.OfType<TypeDeclaration>().Where(t => Token(t) != 0).GroupBy(Token).ToDictionary(g => g.Key, g => g.First());
        var pending = new Queue<(string Name, TypeDeclaration Scope)>();
        void Scan(AstNode node, TypeDeclaration scope)
        {
            foreach (System.Text.RegularExpressions.Match token in HiddenName.Matches(node.ToString())) pending.Enqueue((token.Value, scope));
        }
        foreach (var type in targets.Values.ToArray())
        {
            if (!twins.TryGetValue(Token(type), out var twin)) continue;
            var candidates = twin.Members.OfType<EntityDeclaration>().Where(m => Token(m) != 0).GroupBy(Token).ToDictionary(g => g.Key, g => g.First());
            foreach (var member in type.Members.ToArray())
            {
                if (member is TypeDeclaration) continue;
                if (!broken(member.ToString()) || !candidates.TryGetValue(Token(member), out var replacement)) continue;
                Scan(replacement, twin);
                member.ReplaceWith(replacement.Clone());
            }
        }
        // <>c 里每个 lambda 是独立的方法，只留用到的；闭包类属于单个方法，整个写出。
        var sharedLive = new Dictionary<TypeDeclaration, HashSet<EntityDeclaration>>();
        var seen = new HashSet<(string, TypeDeclaration)>();
        var added = new HashSet<EntityDeclaration>();
        while (pending.TryDequeue(out var next))
        {
            if (!seen.Add(next)) continue;
            foreach (var scope in next.Scope.AncestorsAndSelf.OfType<TypeDeclaration>())
            {
                var members = scope.Members.OfType<EntityDeclaration>().ToArray();
                var shared = members.OfType<TypeDeclaration>().FirstOrDefault(t => t.Name == Shared);
                if (shared?.Members.OfType<EntityDeclaration>().FirstOrDefault(m => Declared(m) == next.Name) is { } inner)
                {
                    if (!sharedLive.TryGetValue(shared, out var live)) sharedLive[shared] = live = [];
                    if (live.Add(inner)) Scan(inner, shared);
                    break;
                }
                if (next.Name == Shared && shared is not null)
                {
                    if (!sharedLive.ContainsKey(shared)) sharedLive[shared] = [];
                    break;
                }
                if (members.FirstOrDefault(m => Declared(m) == next.Name) is not { } declaration) continue;
                if (added.Add(declaration) && targets.TryGetValue(Token(scope), out var target))
                {
                    var existing = target.Members.OfType<EntityDeclaration>().FirstOrDefault(m => Declared(m) == next.Name);
                    // 折叠时闭包类也可能写出来，但里面的局部函数是隐藏的，要换成不折叠的写法。
                    if (existing is TypeDeclaration && next.Name.StartsWith("_003C_003Ec__DisplayClass", StringComparison.Ordinal))
                        existing.ReplaceWith(declaration.Clone());
                    else if (existing is null) target.Members.Add((EntityDeclaration)declaration.Clone());
                    if (declaration is TypeDeclaration nested) Scan(nested, nested);
                    else if (existing is null) Scan(declaration, scope);
                }
                break;
            }
        }
        foreach (var (shared, live) in sharedLive)
        {
            if (shared.Parent is not TypeDeclaration scope || !targets.TryGetValue(Token(scope), out var target)) continue;
            if (target.Members.OfType<TypeDeclaration>().Any(t => t.Name == Shared)) continue;
            var partial = (TypeDeclaration)shared.Clone();
            foreach (var (original, copy) in shared.Members.OfType<EntityDeclaration>().Zip(partial.Members.OfType<EntityDeclaration>()).ToArray())
                if (!live.Contains(original) && original is MethodDeclaration or FieldDeclaration && Declared(original) != "_003C_003E9") copy.Remove();
            target.Members.Add(partial);
        }
    }

    private static readonly System.Text.RegularExpressions.Regex BrokenIterator = new(@"/\*Error near IL_[0-9a-f]+: (stateMachine|Unexpected return in MoveNext\(\))\*/", System.Text.RegularExpressions.RegexOptions.Compiled);
    private static readonly System.Text.RegularExpressions.Regex HiddenName = new(@"\b_003C\w+", System.Text.RegularExpressions.RegexOptions.Compiled);
    private static readonly System.Text.RegularExpressions.Regex HiddenReference = new(@"\b_003CPrivateImplementationDetails_003E\b|\b_003C_003Ef__AnonymousType\d+\b", System.Text.RegularExpressions.RegexOptions.Compiled);
    private static readonly System.Text.RegularExpressions.Regex ClosureThis = new(@"\(_003C_003Ec__DisplayClass\d+_\d+\)(\(object\))?this\b", System.Text.RegularExpressions.RegexOptions.Compiled);
    private static readonly System.Text.RegularExpressions.Regex LambdaMethod = new(@"\b_003C\w+?_003Eb__\d+(_\d+)?\b", System.Text.RegularExpressions.RegexOptions.Compiled);
    private static readonly System.Text.RegularExpressions.Regex DeclaredLambdaMethod = new(@"(?m)^\s*(?:public|internal|private|protected)\b[^=\r\n;]*?\b(_003C\w+?_003Eb__\d+(?:_\d+)?)(?:<[^>\r\n]*>)?\(", System.Text.RegularExpressions.RegexOptions.Compiled);
    private static readonly System.Text.RegularExpressions.Regex ClosureReference = new(@"\b_003C_003Ec__DisplayClass\d+_\d+\b", System.Text.RegularExpressions.RegexOptions.Compiled);

    private static string Print(SyntaxTree tree, DecompilerSettings settings)
    {
        var writer = new StringWriter();
        tree.AcceptVisitor(new CSharpOutputVisitor(writer, settings.CSharpFormattingOptions));
        return writer.ToString();
    }
}
