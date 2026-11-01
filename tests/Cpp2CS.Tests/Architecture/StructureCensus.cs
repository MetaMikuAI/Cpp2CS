using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace Cpp2CS.Tests.Architecture;

/// <summary>一处受约束的访问：约束标签、被访问的成员、所在文件与行。白名单与豁免清单按（标签、成员、文件）放行。</summary>
internal sealed record Access(string Tag, string Member, string File, int Line);

/// <summary>
/// 语义计数（主文 3.3、附录 C.3）：用符号与 IOperation 判定，不用文本正则；换行、调换属性顺序或改写成 == 都不改变计数。
/// 计数键为“计数项/范围”，范围见 <see cref="SourceModel.Scope"/>。同时收集受白名单或豁免清单约束的访问。
/// </summary>
internal sealed class StructureCensus
{
    public SortedDictionary<string, int> Counts { get; } = new(StringComparer.Ordinal);
    public List<Access> Accesses { get; } = [];
    /// <summary>洞编码字面量：（rule、文件、所在方法）。</summary>
    public List<(string Rule, string File, string Method)> HoleCodes { get; } = [];
    /// <summary>PassList.Run 的步骤名：（名称、范围、文件、行）。</summary>
    public List<(string Name, string Scope, string File, int Line)> PassNames { get; } = [];
    /// <summary>方法声明（声明类型.方法名）→ 所在范围；核对跨族转移清单用。</summary>
    public Dictionary<string, HashSet<string>> MethodScopes { get; } = new(StringComparer.Ordinal);

    private readonly SourceModel model;

    /// <summary>维护原语：声明类型名.方法名 → 计数项。</summary>
    private static readonly Dictionary<string, string> Maintenance = new(StringComparer.Ordinal)
    {
        ["TypingRules.InferTypes"] = "infer-types",
        ["RuntimeRules.IndexDefinitions"] = "index-definitions",
        ["Propagate.Run"] = "propagate-run",
        ["Propagate.RemoveDead"] = "propagate-remove-dead",
        ["Lowering.Cleanup"] = "lowering-cleanup",
        ["ControlFlow.Simplify"] = "control-flow-simplify",
        ["Dominators.Compute"] = "dominators",
        ["SsaBuilder.Build"] = "ssa-build",
    };

    /// <summary>证据表类型 → 归属族（计数跨族写入用；字段迁移按附录 A.4 在 O1、O2 进行）。</summary>
    private static readonly Dictionary<string, string> StateOwners = new(StringComparer.Ordinal)
    {
        ["SignatureState"] = "Signature", ["TypesState"] = "Typing", ["RuntimeState"] = "Runtime",
        ["ConstructionState"] = "Construction", ["FramesState"] = "Frames", ["StructsState"] = "Structs",
        ["ExceptionsState"] = "Exceptions", ["CallsState"] = "Calls", ["ArraysState"] = "Memory", ["LoweringState"] = "Lowering",
    };

    /// <summary>以证据字段为实例时不改变内容的方法；其他实例方法调用一律视为写入。</summary>
    private static readonly HashSet<string> ReadOnlyMethods = new(StringComparer.Ordinal)
    {
        "TryGetValue", "ContainsKey", "ContainsValue", "Contains", "GetValueOrDefault", "IndexOf", "LastIndexOf", "Find", "FindIndex",
        "FindLast", "FindLastIndex", "FindAll", "Exists", "TrueForAll", "ToArray", "ToList", "GetEnumerator", "Equals", "GetHashCode",
        "ToString", "CopyTo", "GetRange", "ConvertAll", "Overlaps", "IsSubsetOf", "IsSupersetOf", "IsProperSubsetOf",
        "IsProperSupersetOf", "SetEquals", "AsReadOnly", "BinarySearch", "Peek", "TryPeek",
    };

    /// <summary>以证据字段为第一个实参时会改变内容的扩展方法。</summary>
    private static readonly HashSet<string> MutatingExtensions = new(StringComparer.Ordinal) { "TryAdd", "Remove", "AddRange" };

    private static readonly HashSet<string> ListMutators = new(StringComparer.Ordinal)
    {
        "Add", "AddRange", "Insert", "InsertRange", "Remove", "RemoveAt", "RemoveAll", "RemoveRange", "Clear", "Reverse", "Sort",
    };

    /// <summary>方法会话与交给规则的作用域：以它们为接收者的扩展方法、经它们访问证据表与方法恢复器的成员一并计数。</summary>
    private static readonly HashSet<string> Scopes = new(StringComparer.Ordinal) { "RecoveryScope", "AnalysisScope", "RewriteScope", "BindingScope", "ProofScope" };

    private static readonly HashSet<string> RuleAttributes = new(StringComparer.Ordinal)
    {
        "StepAttribute", "RuleAttribute",
    };

    /// <summary>只做转调的注册方法 → 被转调的方法（视同注册方法，I3）。</summary>
    private readonly Dictionary<IMethodSymbol, IMethodSymbol> forwarded = new(SymbolEqualityComparer.Default);

    public StructureCensus(SourceModel model)
    {
        this.model = model;
        var core = model["Core"];
        foreach (var tree in core.Trees) Forwarders(core.Compilation.GetSemanticModel(tree), tree);
        foreach (var project in model.Projects.Where(p => p.Name != "Tests"))
            foreach (var tree in project.Trees)
                Source(project.Compilation.GetSemanticModel(tree), tree);
        foreach (var tree in core.Trees)
        {
            var file = model.Relative(tree);
            Members(core.Compilation.GetSemanticModel(tree), tree, file, SourceModel.Scope(file));
        }
        var tests = model["Tests"];
        foreach (var tree in tests.Trees) TestSource(tests.Compilation.GetSemanticModel(tree), tree);
        foreach (var project in model.Projects)
            foreach (var tree in project.Trees)
                Unbound(project, project.Compilation.GetSemanticModel(tree), tree);
    }

    private void Count(string item, string scope, int n = 1) => Counts[$"{item}/{scope}"] = Counts.GetValueOrDefault($"{item}/{scope}") + n;

    private void Track(string tag, string member, string file, SyntaxNode node) => Accesses.Add(new(tag, member, file, SourceModel.Line(node)));

    private static string Name(ISymbol symbol) => $"{symbol.ContainingType?.Name}.{symbol.Name}";

    private static bool Declared(ISymbol? symbol, string type, string member) => symbol is not null && symbol.Name == member && symbol.ContainingType?.Name == type
        && symbol.ContainingNamespace.ToDisplayString().StartsWith("Cpp2CS", StringComparison.Ordinal);

    private static IOperation? Unwrap(IOperation? operation)
    {
        while (operation is IConversionOperation conversion) operation = conversion.Operand;
        while (operation is IParenthesizedOperation parenthesized) operation = parenthesized.Operand;
        return operation;
    }

    private void Source(SemanticModel semantic, SyntaxTree tree)
    {
        var file = model.Relative(tree);
        var scope = SourceModel.Scope(file);
        var recovery = scope == "Recovery" || scope.StartsWith("Recovery/", StringComparison.Ordinal);
        var root = tree.GetRoot();
        foreach (var node in root.DescendantNodes())
        {
            switch (node)
            {
                case MethodDeclarationSyntax method when method.ParameterList.Parameters.FirstOrDefault() is { } first
                    && first.Modifiers.Any(SyntaxKind.ThisKeyword) && Scopes.Contains(semantic.GetDeclaredSymbol(first)?.Type.Name ?? ""):
                    Count("scope-extension-methods", scope);
                    break;
                case MemberAccessExpressionSyntax access when semantic.GetSymbolInfo(access.Expression).Symbol is { } inner
                    && (Scopes.Any(s => Declared(inner, s, "State")) || Declared(inner, "LoweringScope", "State")):
                    Count("state-access", scope);
                    break;
                case InvocationExpressionSyntax invocation:
                    Invocation(semantic, invocation, file, scope, recovery);
                    break;
                case AssignmentExpressionSyntax assignment:
                    Assignment(semantic, assignment, file, scope, recovery);
                    break;
                case PostfixUnaryExpressionSyntax or PrefixUnaryExpressionSyntax when node.Kind() is SyntaxKind.PostIncrementExpression
                    or SyntaxKind.PostDecrementExpression or SyntaxKind.PreIncrementExpression or SyntaxKind.PreDecrementExpression:
                    StateWrite(semantic.GetOperation(node) is IIncrementOrDecrementOperation step ? step.Target : null, node, file, scope);
                    break;
                case ArgumentSyntax argument when argument.RefKindKeyword.Kind() is SyntaxKind.RefKeyword or SyntaxKind.OutKeyword:
                    StateWrite(semantic.GetOperation(argument.Expression), node, file, scope);
                    break;
                case ObjectCreationExpressionSyntax or ImplicitObjectCreationExpressionSyntax
                    when semantic.GetTypeInfo(node).Type is { Name: "Block" } created && created.ContainingNamespace.ToDisplayString() == "Cpp2CS.Machine.Flow":
                    Count("new-block", scope);
                    break;
                case SubpatternSyntax subpattern when semantic.GetOperation(subpattern) is IPropertySubpatternOperation property
                    && Unwrap(property.Member) is IPropertyReferenceOperation { Property: var op } && Declared(op, "Binary", "Op") && MentionsAdd(property.Pattern):
                    Count("address-add-match", scope);
                    break;
                case BinaryExpressionSyntax binary when binary.Kind() is SyntaxKind.EqualsExpression or SyntaxKind.NotEqualsExpression
                    && semantic.GetOperation(binary) is IBinaryOperation comparison && IsAddComparison(comparison):
                    Count("address-add-match", scope);
                    break;
                case IsPatternExpressionSyntax list when list.Pattern.DescendantNodesAndSelf().OfType<ListPatternSyntax>().Any()
                    && semantic.GetOperation(list.Expression) is IInvocationOperation { TargetMethod.Name: "ToArray" } toArray
                    && toArray.Arguments.FirstOrDefault()?.Value is { } source && Unwrap(source) is IPropertyReferenceOperation { Property.Name: "NormalSuccessors" }:
                    Count("single-successor-pattern", scope);
                    break;
                case ForStatementSyntax loop when recovery && RoundLoop(semantic, loop):
                    Count("round-loops", scope);
                    break;
                case WhileStatementSyntax or DoStatementSyntax when recovery && MaintenanceLoop(semantic, node):
                    Count("maintenance-loops-unbudgeted", scope);
                    break;
                case ArgumentSyntax { NameColon.Name.Identifier.Text: "rule", Expression: LiteralExpressionSyntax literal } argument
                    when literal.IsKind(SyntaxKind.StringLiteralExpression):
                    HoleCodes.Add((literal.Token.ValueText, file, argument.Ancestors().OfType<MethodDeclarationSyntax>().FirstOrDefault()?.Identifier.Text ?? "?"));
                    break;
            }
        }
        foreach (var method in root.DescendantNodes().OfType<MethodDeclarationSyntax>())
        {
            // Analyze 的改写步骤：Step(id, StepPhase.Analyze, StepKind.Rewrite)。Prepare 的步骤都改写 IR，没有只读检查，不计入
            if (semantic.GetDeclaredSymbol(method)?.GetAttributes().Any(a => a.AttributeClass?.Name == "StepAttribute"
                    && a.ConstructorArguments is [_, { Type.Name: "StepPhase", Value: 1 }, { Type.Name: "StepKind", Value: 1 }]) == true)
                Count("machine-pass-steps", scope);
            var declared = $"{method.Ancestors().OfType<BaseTypeDeclarationSyntax>().FirstOrDefault()?.Identifier.Text}.{method.Identifier.Text}";
            if (!MethodScopes.TryGetValue(declared, out var scopes)) MethodScopes[declared] = scopes = [];
            scopes.Add(scope);
        }
    }

    private static bool MentionsAdd(IOperation pattern) => pattern.DescendantsAndSelf().OfType<IFieldReferenceOperation>().Any(f => Declared(f.Field, "BinOp", "Add"));

    private static bool IsAddComparison(IBinaryOperation comparison)
    {
        var (left, right) = (Unwrap(comparison.LeftOperand), Unwrap(comparison.RightOperand));
        static bool Op(IOperation? o) => o is IPropertyReferenceOperation { Property: var p } && Declared(p, "Binary", "Op");
        static bool Add(IOperation? o) => o is IFieldReferenceOperation { Field: var f } && Declared(f, "BinOp", "Add");
        return Op(left) && Add(right) || Add(left) && Op(right);
    }

    /// <summary>
    /// 循环体内改写 IR 或执行维护动作的循环（主文 4.3.4）：维护原语调用、重置块视图或定义索引、
    /// 经语句改写器或语句列表修改语句。
    /// </summary>
    private static bool MaintenanceLoop(SemanticModel semantic, SyntaxNode loop) => loop.DescendantNodes().Any(n => n switch
    {
        InvocationExpressionSyntax call => semantic.GetSymbolInfo(call).Symbol is IMethodSymbol m
            && (Maintenance.ContainsKey(Name((m.ReducedFrom ?? m).OriginalDefinition))
                || m.ContainingType.Name is "StatementRewriter" or "StatementList" && m.Name is "Replace" or "Insert" or "Remove" or "RemoveAt" or "RemoveAll" or "Add" or "Clear"),
        AssignmentExpressionSyntax assignment => semantic.GetSymbolInfo(assignment.Left).Symbol is { } field
            && (Declared(field, "RecoveryScope", "blocks") || Declared(field, "RecoveryScope", "definitions")),
        _ => false,
    });

    /// <summary>
    /// 轮次循环：for 循环的计数器与常量比较、在循环体内不被引用（只计轮数）。包括不动点的轮次预算（主文 4.3.4 的 3 个 round &lt; 8），
    /// 也包括搜索深度一类的预算；新增的同类循环会使计数上升。
    /// </summary>
    private static bool RoundLoop(SemanticModel semantic, ForStatementSyntax loop)
    {
        if (loop.Condition is not BinaryExpressionSyntax { RawKind: (int)SyntaxKind.LessThanExpression } compare
            || semantic.GetConstantValue(compare.Right) is not { HasValue: true, Value: int }
            || semantic.GetSymbolInfo(compare.Left).Symbol is not ILocalSymbol counter) return false;
        return !loop.Statement.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
            .Any(name => SymbolEqualityComparer.Default.Equals(semantic.GetSymbolInfo(name).Symbol, counter));
    }

    private void Invocation(SemanticModel semantic, InvocationExpressionSyntax syntax, string file, string scope, bool recovery)
    {
        if (semantic.GetOperation(syntax) is not IInvocationOperation invocation) return;
        var method = invocation.TargetMethod.ReducedFrom ?? invocation.TargetMethod;
        var target = Name(method.OriginalDefinition);
        // 维护原语在内核中的调用是内核接口自身的实现，不计数
        if (Maintenance.TryGetValue(target, out var item) && scope != "Recovery/Kernel")
        {
            Count(item, scope);
            if (recovery) Track(MaintenanceTag(semantic, syntax), target, file, syntax);
            else if (scope == "Idioms" && item == "dominators") Track("I2b", target, file, syntax);
        }
        if (Declared(method, "CallBindingState", "Commit")) Count("call-binding-commit", scope);
        if (method.Name == "OfType" && method.ContainingType.Name == "Enumerable" && invocation.TargetMethod.TypeArguments is [{ Name: "Use" } use]
            && use.ContainingNamespace.ToDisplayString() == "Cpp2CS.Ir" && SequenceScan(semantic, syntax))
        {
            Count("use-scan", scope);
            if (recovery || scope == "Idioms") Track("I2b", "Enumerable.OfType<Use>", file, syntax);
        }
        // φ 头部：TakeWhile(s => s is Phi)（is 类型测试或类型模式）
        if (method.Name == "TakeWhile" && syntax.ArgumentList.Arguments is [{ Expression: LambdaExpressionSyntax lambda }]
            && semantic.GetOperation(lambda.Body) is IIsTypeOperation { TypeOperand.Name: "Phi" } or IIsPatternOperation { Pattern: ITypePatternOperation { MatchedType.Name: "Phi" } })
            Count("phi-head", scope);
        if (method.Name == "Run" && method.ContainingType.Name == "PassList" && syntax.ArgumentList.Arguments.FirstOrDefault()?.Expression is LiteralExpressionSyntax name)
            PassNames.Add((name.Token.ValueText, scope, file, SourceModel.Line(syntax)));
        if (Registered(method) || forwarded.Values.Contains(method.OriginalDefinition, SymbolEqualityComparer.Default)
            && !forwarded.Any(p => SymbolEqualityComparer.Default.Equals(p.Value, method.OriginalDefinition) && Caller(semantic, syntax) is { } caller && SymbolEqualityComparer.Default.Equals(caller, p.Key)))
            Track("I3", target, file, syntax);
        // CFG：Successors、Predecessors、Blocks 的修改方法（含同一方法内的局部别名）
        if (ListMutators.Contains(method.Name) && CfgList(semantic, invocation.Instance) is { } list && !file.StartsWith("src/Cpp2CS.Core/Machine/Flow/", StringComparison.Ordinal))
        {
            Count("cfg-mutation", scope);
            Track("I1b", $"{list}.{method.Name}", file, syntax);
        }
        // 以证据字段为实例的可变方法调用；扩展方法看第一个实参
        if (invocation.Instance is { } instance && !ReadOnlyMethods.Contains(method.Name))
            StateWrite(instance, syntax, file, scope);
        else if (invocation.Instance is null && method.IsExtensionMethod && MutatingExtensions.Contains(method.Name) && invocation.Arguments.FirstOrDefault() is { } receiver)
            StateWrite(receiver.Value, syntax, file, scope);
        // 对 MethodRecovery 实例成员的访问（I10）在成员访问处统计
    }

    private static bool Registered(IMethodSymbol method) => method.GetAttributes().Any(a => RuleAttributes.Contains(a.AttributeClass?.Name ?? ""));

    private static IMethodSymbol? Caller(SemanticModel semantic, SyntaxNode node) =>
        node.Ancestors().OfType<BaseMethodDeclarationSyntax>().FirstOrDefault() is { } declaration ? semantic.GetDeclaredSymbol(declaration) as IMethodSymbol : null;

    /// <summary>注册方法的方法体只有一个调用（表达式体或单条语句）时，记下被转调的方法。</summary>
    private void Forwarders(SemanticModel semantic, SyntaxTree tree)
    {
        foreach (var declaration in tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>())
        {
            if (semantic.GetDeclaredSymbol(declaration) is not { } method || !Registered(method)) continue;
            var body = declaration.ExpressionBody?.Expression
                ?? (declaration.Body?.Statements is [var only] ? only switch
                {
                    ExpressionStatementSyntax e => e.Expression,
                    ReturnStatementSyntax r => r.Expression,
                    _ => null,
                } : null);
            // 内核的维护接口（Maintenance、Editing）不是步骤体，转调它不使它成为注册方法
            if (body is InvocationExpressionSyntax call && semantic.GetSymbolInfo(call).Symbol is IMethodSymbol callee && callee.ContainingType.Name is not ("Maintenance" or "Editing"))
                forwarded[method] = (callee.ReducedFrom ?? callee).OriginalDefinition;
        }
    }

    private string MaintenanceTag(SemanticModel semantic, SyntaxNode node)
    {
        // 不以作用域为参数的独立算法类内部的维护调用属于 I2c，其余（规则、Prepare 流程、以作用域为参数的辅助函数）属于 I2a
        var method = node.Ancestors().OfType<BaseMethodDeclarationSyntax>().FirstOrDefault();
        var symbol = method is null ? null : semantic.GetDeclaredSymbol(method) as IMethodSymbol;
        var scoped = symbol is null || symbol.Parameters.Any(p => Scopes.Contains(p.Type.Name) || p.Type.Name == "LoweringScope")
            || symbol.ContainingType.GetMembers().OfType<IFieldSymbol>().Any(f => Scopes.Contains(f.Type.Name) || f.Type.Name == "LoweringScope")
            || Scopes.Contains(symbol.ContainingType.Name) || symbol.ContainingType.Name == "LoweringScope";
        return scoped ? "I2a" : "I2c";
    }

    /// <summary>
    /// 语句序列上的用途扫描：接收者链中出现函数、块或语句序列，或者调用位于遍历语句序列的 foreach、
    /// 以语句序列为接收者的调用的 lambda 实参之中。只遍历单个表达式或单条语句的不算。
    /// </summary>
    private static bool SequenceScan(SemanticModel semantic, InvocationExpressionSyntax syntax)
    {
        var receiver = syntax.Expression is MemberAccessExpressionSyntax access ? access.Expression : syntax.ArgumentList.Arguments.FirstOrDefault()?.Expression;
        if (receiver is not null && receiver.DescendantNodesAndSelf().OfType<ExpressionSyntax>().Any(e => IsSequence(semantic.GetTypeInfo(e).Type))) return true;
        foreach (var ancestor in syntax.Ancestors().TakeWhile(a => a is not MemberDeclarationSyntax))
        {
            if (ancestor is ForEachStatementSyntax loop && IsSequence(semantic.GetTypeInfo(loop.Expression).Type)) return true;
            if (ancestor is LambdaExpressionSyntax && ancestor.Parent is ArgumentSyntax { Parent.Parent: InvocationExpressionSyntax outer }
                && outer.Expression is MemberAccessExpressionSyntax { Expression: var outerReceiver }
                && outerReceiver.DescendantNodesAndSelf().OfType<ExpressionSyntax>().Any(e => IsSequence(semantic.GetTypeInfo(e).Type)))
                return true;
        }
        return false;
    }

    private static bool IsSequence(ITypeSymbol? type)
    {
        if (type is null) return false;
        if (type.Name is "MachineFunction" or "Block" or "StatementList" && type.ContainingNamespace.ToDisplayString().StartsWith("Cpp2CS", StringComparison.Ordinal)) return true;
        var element = type is IArrayTypeSymbol array ? array.ElementType
            : type.AllInterfaces.Append(type as INamedTypeSymbol).OfType<INamedTypeSymbol>()
                .FirstOrDefault(i => i.OriginalDefinition.SpecialType == SpecialType.System_Collections_Generic_IEnumerable_T)?.TypeArguments[0];
        return element is not null && (element.Name == "Block" || IsStatement(element));
    }

    private static bool IsStatement(ITypeSymbol type)
    {
        for (var current = type; current is not null; current = current.BaseType)
            if (current.Name == "Stmt" && current.ContainingNamespace.ToDisplayString() == "Cpp2CS.Ir") return true;
        return false;
    }

    /// <summary>实例是 CFG 列表（Block.Successors/Predecessors、MachineFunction.Blocks），或同一方法内以它初始化的局部变量时，返回列表名。</summary>
    private static string? CfgList(SemanticModel semantic, IOperation? instance)
    {
        switch (Unwrap(instance))
        {
            case IPropertyReferenceOperation { Property: var p } when Declared(p, "Block", "Successors") || Declared(p, "Block", "Predecessors") || Declared(p, "MachineFunction", "Blocks"):
                return Name(p);
            case ILocalReferenceOperation { Local: var local }:
                foreach (var reference in local.DeclaringSyntaxReferences)
                    if (reference.GetSyntax() is VariableDeclaratorSyntax { Initializer.Value: var value } && reference.SyntaxTree == semantic.SyntaxTree)
                        return CfgList(semantic, semantic.GetOperation(value));
                return null;
            default:
                return null;
        }
    }

    private void Assignment(SemanticModel semantic, AssignmentExpressionSyntax syntax, string file, string scope, bool recovery)
    {
        if (semantic.GetOperation(syntax) is not IAssignmentOperation assignment) return;
        var target = Unwrap(assignment.Target);
        if (target is IFieldReferenceOperation { Field: var field } && scope != "Recovery/Kernel")
        {
            if (Declared(field, "RecoveryScope", "blocks")) Count("blocks-reset", scope);
            if (Declared(field, "RecoveryScope", "definitions")) Count("definitions-reset", scope);
            if (recovery && (Declared(field, "RecoveryScope", "blocks") || Declared(field, "RecoveryScope", "definitions"))
                && !file.EndsWith("/Rules/RecoveryScope.cs", StringComparison.Ordinal))
                Track(MaintenanceTag(semantic, syntax), Name(field), file, syntax);
        }
        if (!file.StartsWith("src/Cpp2CS.Core/Machine/Flow/", StringComparison.Ordinal))
        {
            // 对象初始化器（new MachineFunction { Blocks = … }）是构造，不是对已有 CFG 的修改
            if (target is IPropertyReferenceOperation { Property: var property, Instance: not IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ImplicitReceiver } }
                && (Declared(property, "Block", "Handler") || Declared(property, "MachineFunction", "Blocks")))
            {
                Count("cfg-mutation", scope);
                Track("I1b", $"{Name(property)}=", file, syntax);
            }
            if (target is IPropertyReferenceOperation { Property.IsIndexer: true, Instance: var indexed } && CfgList(semantic, indexed) is { } list)
            {
                Count("cfg-mutation", scope);
                Track("I1b", $"{list}[]=", file, syntax);
            }
        }
        StateWrite(assignment.Target, syntax, file, scope);
    }

    /// <summary>写入目标（经索引器、数组元素与成员访问链）的根是证据表字段时，计一次写入；写入方与表的归属族不同则为跨族写入（I4）。</summary>
    private void StateWrite(IOperation? target, SyntaxNode node, string file, string scope)
    {
        var field = StateField(target);
        if (field is null || !StateOwners.TryGetValue(field.ContainingType.Name, out var owner)) return;
        if (node.Ancestors().OfType<BaseTypeDeclarationSyntax>().Any(t => t.Identifier.Text == field.ContainingType.Name)) return;
        Count("state-write", scope);
        var writer = SourceModel.Family(file) ?? scope;
        if (writer == owner) return;
        Count("cross-family-write", scope);
        Track("I4", $"{field.ContainingType.Name[..^"State".Length]}.{field.Name}", file, node);
    }

    private static IFieldSymbol? StateField(IOperation? operation)
    {
        for (var current = Unwrap(operation); current is not null; )
        {
            switch (current)
            {
                case IFieldReferenceOperation { Field: var field } when StateOwners.ContainsKey(field.ContainingType.Name):
                    return field;
                case IPropertyReferenceOperation { Property.IsIndexer: true } indexer:
                    current = Unwrap(indexer.Instance);
                    break;
                case IArrayElementReferenceOperation element:
                    current = Unwrap(element.ArrayReference);
                    break;
                case IInvocationOperation { TargetMethod.Name: "GetValueOrDefault" or "First" or "Single" or "Last" } call when call.Instance is null && call.Arguments.Length > 0:
                    current = Unwrap(call.Arguments[0].Value);
                    break;
                default:
                    return null;
            }
        }
        return null;
    }

    /// <summary>对 MethodRecovery 实例成员的引用（I10）与 RecoveryScope.owner 的访问次数。终态允许 Recovery/Kernel 与 Recovery/Services 访问，不计。</summary>
    private void Members(SemanticModel semantic, SyntaxTree tree, string file, string scope)
    {
        if (scope is "Recovery/Kernel" or "Recovery/Services") return;
        foreach (var name in tree.GetRoot().DescendantNodes().OfType<SimpleNameSyntax>())
        {
            var symbol = semantic.GetSymbolInfo(name).Symbol;
            if (symbol is null) continue;
            if (Scopes.Any(s => Declared(symbol, s, "owner"))) Count("owner-access", scope);
            if (!symbol.IsStatic && symbol.ContainingType?.Name == "MethodRecovery" && symbol.Kind is SymbolKind.Field or SymbolKind.Property or SymbolKind.Method
                && symbol.ContainingNamespace.ToDisplayString() == "Cpp2CS.Recovery" && !file.EndsWith("/Recovery/MethodRecovery.cs", StringComparison.Ordinal)
                && name.Parent is MemberAccessExpressionSyntax access && access.Name == name)
                Track("I10", Name(symbol), file, name);
        }
    }

    private void TestSource(SemanticModel semantic, SyntaxTree tree)
    {
        var file = model.Relative(tree);
        var internalReferences = 0;
        foreach (var node in tree.GetRoot().DescendantNodes())
        {
            if (node is ObjectCreationExpressionSyntax or ImplicitObjectCreationExpressionSyntax && semantic.GetTypeInfo(node).Type?.Name == "RecoveryScope")
                Count("scope-construction", "Tests");
            if (node is SimpleNameSyntax name && semantic.GetSymbolInfo(name).Symbol is INamedTypeSymbol type
                && type.DeclaredAccessibility is Accessibility.Internal && type.ContainingAssembly?.Name == "Cpp2CS.Core")
                internalReferences++;
        }
        if (internalReferences == 0) return;
        Count("core-internal-type-references", "Tests", internalReferences);
        Count("files-referencing-core-internals", "Tests");
    }

    /// <summary>未绑定的名称：语义检查看不到它们引用了什么，计数护栏只降不升。</summary>
    private void Unbound(SourceModel.Project project, SemanticModel semantic, SyntaxTree tree)
    {
        var unbound = tree.GetRoot().DescendantNodes().OfType<SimpleNameSyntax>().Count(name =>
            !name.Ancestors().Any(a => a is UsingDirectiveSyntax || a is BaseNamespaceDeclarationSyntax declaration && declaration.Name.Span.Contains(name.Span))
            && name.Parent is not NameColonSyntax and not NameEqualsSyntax
            && semantic.GetSymbolInfo(name) is { Symbol: null, CandidateSymbols.IsEmpty: true }
            && name.Identifier.Text is not ("var" or "_" or "nameof"));
        if (unbound > 0) Count("unbound-names", project.Name, unbound);
    }
}
