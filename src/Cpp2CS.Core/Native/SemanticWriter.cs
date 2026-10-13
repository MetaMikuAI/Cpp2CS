using System.Text;

namespace Cpp2CS.Native;

public sealed class SemanticWriter(Symbols symbols)
{
    public static string Expression(Expression e) => e switch
    {
        NameExpression n => n.Name,
        StaticMemberExpression m => m.Owner + "." + m.Name,
        CapturedExpression c => c.Name,
        ConstantExpression { EnumType: { } type, EnumMember: { } member } => type + "." + member,
        ConstantExpression { EnumType: { } type } c => "(" + type + ")" + c.Value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        ConstantExpression c => c.Value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        OperationExpression o => ValueOperations.Write(o),
        IndexedArrayAddress a => $"Runtime.ArrayAddress({Expression(a.Array)}, {Expression(a.Index)})",
        AddressExpression a => $"Runtime.Global(0x{a.Address:x})",
        AddressOfExpression a => "ref " + Expression(a.Target),
        StackAddressExpression a => $"Runtime.StackAddress({a.Offset})",
        MetadataExpression { IsSlot: false, Reference.Kind: "ScriptString" } m => System.Text.Json.JsonSerializer.Serialize(m.Reference.Name),
        MetadataExpression m => (m.IsSlot ? "MetadataSlot" : "MetadataValue") + "(\"" + m.Reference.Name.Replace("\"", "\\\"") + "\")",
        MemberExpression m => Expression(m.Receiver) + "." + m.DisplayName,
        SourceMemberExpression m => Expression(m.Receiver) + "." + m.Name,
        AwaitExpression a => "await " + Expression(a.Value),
        CastExpression c => "((" + c.Type + ")(" + Expression(c.Value) + "))",
        ObjectValueExpression o => o.Fields.Length == 0 ? "default(" + o.Type + ")" :
            "new " + o.Type + " { " + string.Join(", ", o.Fields.Select(f => f.Name + " = " + Expression(f.Value))) + " }",
        BinaryExpression b => "(" + Expression(b.Left) + " " + b.Operator + " " + Expression(b.Right) + ")",
        SliceExpression s => $"Runtime.Bits({Expression(s.Value)}, {s.BitOffset}, {s.BitWidth})",
        ComposeExpression c => "Runtime.ConcatBits(" + string.Join(", ", c.Parts.Select((p, i) => $"({Expression(p)}, {c.BitWidths[i]})")) + ")",
        AggregateExpression a => $"Runtime.Value<{a.Type}>({Expression(a.Bits)})",
        InvocationExpression c => (c.Receiver is null ? "" : Expression(c.Receiver) + ".") +
            (c.IsProperty ? c.Name.Replace("get_", "") : c.Name + "(" + string.Join(", ", c.Arguments.Select(Expression)) + ")"),
        LambdaExpression l => (l.Parameters.Length == 1 ? l.Parameters[0] : "(" + string.Join(", ", l.Parameters) + ")") + " => " + Expression(l.Body),
        LambdaBlockExpression b => new SemanticWriter(null!).Structured(b.Body, true).TrimEnd(),
        UnknownExpression u => "UNKNOWN(\"" + u.Reason + "\")",
        _ => throw new InvalidOperationException("缺少表达式输出器")
    };
    public static string Statement(Statement s) => s switch
    {
        AssignStatement a => $"{(a.Value is LambdaExpression ? a.Type : "var")} {a.Name} = {Expression(a.Value)};",
        EvaluateStatement e => Expression(e.Value) + ";",
        DeclareStatement d => $"{(d.Type is "int32_t" ? "int" : d.Type is "int64_t" ? "long" : d.Type)} {d.Name};",
        SetLocalStatement local => local.Name + " = " + Expression(local.Value) + ";",
        CallStatement { IsInstance: true, Name: ".ctor" } c => "Runtime.InvokeConstructor(" + string.Join(", ", new[] { c.Receiver! }.Concat(c.Arguments).Select(Expression)) + ");",
        CallStatement c => (c.Result is null ? "" : "var " + c.Result + " = ") +
            (c.IsInstance ? Expression(c.Receiver is AddressOfExpression address ? address.Target : c.Receiver!) + "." : "") + (c.IsProperty ? c.Name.Replace("get_", "") : c.Name) +
            (c.IsProperty ? ";" : "(" + string.Join(", ", c.Arguments.Select(Expression)) + ");"),
        StoreStatement s1 => Expression(s1.Target) + " = " + Expression(s1.Value) + ";",
        ReturnStatement r => r.Value is null ? "return;" : "return " + Expression(r.Value) + ";",
        ThrowStatement t => "throw new " + t.Type + "();",
        UnresolvedStatement u => "UNRESOLVED(\"" + u.Reason + "\");",
        EnsureMetadataStatement m => $"Runtime.EnsureMetadataInitialized(0x{m.Flag:x}, " + string.Join(", ", m.References.Select(r => Expression(new MetadataExpression(r, true)))) + ");",
        ConditionalInvokeStatement c => Expression(c.Receiver) + "?.Invoke(" + string.Join(", ", c.Arguments.Select(Expression)) + ");",
        DelegateCacheStatement c => $"var {c.Name} = {Expression(c.Cache)} ??= Runtime.CreateDelegate<{c.Type}>({Expression(c.Target)}, {Expression(c.Method)});",
        _ => throw new InvalidOperationException("缺少语句输出器")
    };
    public string Raw(LiftResult result)
    {
        var text = new StringBuilder();
        text.AppendLine($"// {result.Method.Name} @ 0x{result.Method.Address:x}");
        foreach (var block in result.Blocks.Values.OrderBy(b => b.Address))
        {
            text.AppendLine($"L_{block.Address:x}:");
            foreach (var s in block.Statements) text.AppendLine($"  /*0x{s.Address:x}*/ {Statement(s)}");
            if (block.Condition is not null && block.Successors.Length == 2)
                text.AppendLine($"  if {Expression(block.Condition)} goto L_{block.Successors[0]:x}; else goto L_{block.Successors[1]:x};");
            else if (block.Successors.Length == 1) text.AppendLine($"  goto L_{block.Successors[0]:x};");
        }
        return text.ToString();
    }
    public string Structured(LiftResult result, bool bodyOnly = false)
    {
        if (result.Blocks.Count == 0) return "// 未恢复：" + string.Join("; ", result.Problems);
        var loops = new NaturalLoops(result.Method.Address, result.Blocks.ToDictionary(p => p.Key, p => p.Value.Successors));
        if (!loops.Reducible) return "// 控制流未归约\n" + Raw(result);
        var loopExits = loops.Loops.ToDictionary(l => l.Header, l => l.Nodes.SelectMany(n => result.Blocks[n].Successors).Where(n => !l.Nodes.Contains(n) && !ThrowOnly(n)).Distinct().ToArray());
        if (loopExits.Values.Any(e => e.Length != 1)) return "// 循环出口未归约\n" + Raw(result);
        var activeLoops = new Stack<NaturalLoop>();
        const ulong exit = ulong.MaxValue;
        var universe = result.Blocks.Keys.Append(exit).ToHashSet();
        var post = universe.ToDictionary(x => x, x => x == exit ? new HashSet<ulong> { exit } : new HashSet<ulong>(universe));
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var block in result.Blocks.Values.Reverse())
            {
                var normal = block.Successors.Where(s => !ThrowOnly(s)).ToArray();
                var successors = normal.Length == 0 ? [exit] : normal;
                var set = new HashSet<ulong>(post[successors[0]]);
                foreach (var successor in successors.Skip(1)) set.IntersectWith(post[successor]);
                set.Add(block.Address);
                if (!set.SetEquals(post[block.Address])) { post[block.Address] = set; changed = true; }
            }
        }
        var text = new StringBuilder();
        if (!bodyOnly)
        {
        text.AppendLine(result.IsSourceProjection ? "// 高层源码视图；使用 --diagnostics 可查看缓存、捕获与初始化证据，非重编译等价证明。" :
            "// 自动生成的语义视图；Runtime/Metadata 显式保留运行时行为，不是独立可编译文件。");
        text.AppendLine("// " + result.Method.Name);
        if (result.Problems.Count > 0) text.AppendLine("// PARTIAL: " + string.Join("; ", result.Problems));
        var parameters = result.Method.Parameters.Where(p => p.Name != "__this" && !(p.Name == "method" && p.Type.Contains("MethodInfo"))).Select(p => symbols.Display(p.Type) + " " + p.Name);
        var asLambda = result.SourceLambdaOrigin is not null;
        text.AppendLine(result.SourceDeclaration ?? (asLambda ? $"// {result.SourceLambdaOrigin} 中的回调；外层实例由 this 捕获。\n({string.Join(", ", parameters)}) =>" :
            $"{symbols.Display(result.Method.ReturnType)} {result.Method.Name.Split("$$")[1]}({string.Join(", ", parameters)})"));
        }
        text.AppendLine("{");
        var names = new Dictionary<string, string>();
        var used = result.Method.Parameters.Select(p => p.Name).ToHashSet();
        used.UnionWith(result.Blocks.Values.SelectMany(b => b.Statements).OfType<CallStatement>()
            .SelectMany(c => c.Arguments).OfType<LambdaExpression>().SelectMany(l => l.Parameters));
        foreach (var statement in result.Blocks.Values.SelectMany(b => b.Statements))
        {
            var original = statement is AssignStatement a ? a.Name : statement is DeclareStatement declaration ? declaration.Name : statement is CallStatement c ? c.Result : statement is DelegateCacheStatement d ? d.Name : null;
            if (original is null) continue;
            var preferred = bodyOnly ? original : statement switch
            {
                DeclareStatement loopVariable when loopVariable.Name.StartsWith("loop_") => loopVariable.Type.EndsWith("[]") ? "loopArray" : loopVariable.Type is "System.Int32" or "int32_t" ? "loopIndex" : "loopValue",
                AssignStatement edgeValue when edgeValue.Name.StartsWith("edge_") => "nextValue",
                AssignStatement { Value: NameExpression n } when n.Name.StartsWith("captured") => n.Name + "Snapshot",
                AssignStatement { Value: MemberExpression m } => m.DisplayName,
                AssignStatement { Value: AddressExpression } => "metadataFlag",
                AssignStatement { Value: OperationExpression operation } => operation.Operation switch
                {
                    ValueOperation.NewArray => "array", ValueOperation.FloatDivide => "quotient", ValueOperation.Ceiling => "roundedValue",
                    ValueOperation.Add => "sum", ValueOperation.Subtract => "difference", _ => "value"
                },
                CallStatement invoked when result.IsSourceProjection && invoked.ReturnType is { } native && symbols.Display(native).Contains('_') =>
                    ManagedNames.SplitGeneric(invoked.Name[(ManagedNames.LastTopLevelDot(invoked.Name) + 1)..]).Name + "Result",
                CallStatement { ReturnType: { } t } => symbols.Display(t).Split('.').Last(),
                DelegateCacheStatement => "cachedDelegate",
                _ => original
            };
            if (!System.Text.RegularExpressions.Regex.IsMatch(preferred, @"^[A-Za-z_]\w*$")) preferred = original;
            preferred = char.ToLowerInvariant(preferred[0]) + preferred[1..];
            if (preferred is "string" or "object" or "delegate" or "int" or "bool" or "long" or "float" or "double") preferred += "Value";
            var candidate = preferred; var index = 2;
            while (!used.Add(candidate)) candidate = preferred + index++;
            names[original] = candidate;
        }
        Emit(result.Method.Address, exit, 1, []);
        text.AppendLine("}");
        return text.ToString();
        bool ThrowOnly(ulong address) => result.Blocks[address].Successors.Length == 0 && result.Blocks[address].Statements.LastOrDefault() is ThrowStatement or CallStatement { NoReturn: true };
        bool TerminalOnly(ulong address) => ThrowOnly(address) || result.Blocks[address].Statements is [ReturnStatement];
        static Expression Negate(Expression expression) => expression is BinaryExpression { Operator: "==" } eq ? eq with { Operator = "!=" } :
            expression is BinaryExpression { Operator: "!=" } ne ? ne with { Operator = "==" } :
            expression is BinaryExpression { Operator: "is" } isn ? isn with { Operator = "is not" } :
            expression is BinaryExpression { Operator: "is not" } isnot ? isnot with { Operator = "is" } : new BinaryExpression("==", expression, new ConstantExpression(0));
        Expression Rename(Expression e) => e switch
        {
            LambdaExpression l => l with { Body = SourceTree.Map(l.Body, node => node is NameExpression n && !l.Parameters.Contains(n.Name) ? n with { Name = names.GetValueOrDefault(n.Name, n.Name) } : node) },
            NameExpression n => n with { Name = names.GetValueOrDefault(n.Name, n.Name) },
            CapturedExpression c => c with { Name = names.GetValueOrDefault(c.Name, c.Name) },
            MemberExpression m => m with { Receiver = Rename(m.Receiver) },
            SourceMemberExpression m => m with { Receiver = Rename(m.Receiver) },
            AwaitExpression a => a with { Value = Rename(a.Value) },
            CastExpression c => c with { Value = Rename(c.Value) },
            ObjectValueExpression o => o with { Fields = o.Fields.Select(f => (f.Name, Rename(f.Value))).ToArray() },
            AddressOfExpression a => a with { Target = Rename(a.Target) },
            SliceExpression s => s with { Value = Rename(s.Value) },
            ComposeExpression c => c with { Parts = c.Parts.Select(Rename).ToArray() },
            AggregateExpression a => a with { Bits = Rename(a.Bits) },
            BinaryExpression b => b with { Left = Rename(b.Left), Right = Rename(b.Right) },
            OperationExpression o => o with { Arguments = o.Arguments.Select(Rename).ToArray() },
            InvocationExpression c => c with { Receiver = c.Receiver is null ? null : Rename(c.Receiver), Arguments = c.Arguments.Select(Rename).ToArray() },
            _ => e
        };
        string E(Expression e) => Expression(Rename(e));
        string S(Statement s) => Statement(s switch
        {
            AssignStatement a => a with { Name = names[a.Name], Value = Rename(a.Value) },
            EvaluateStatement e => e with { Value = Rename(e.Value) },
            CallStatement c => c with { Result = c.Result is null ? null : names[c.Result], Receiver = c.Receiver is null ? null : Rename(c.Receiver), Arguments = c.Arguments.Select(Rename).ToArray() },
            StoreStatement w => w with { Target = Rename(w.Target), Value = Rename(w.Value) },
            ReturnStatement r => r with { Value = r.Value is null ? null : Rename(r.Value) },
            DeclareStatement d => d with { Name = names.GetValueOrDefault(d.Name, d.Name), Type = symbols?.Display(d.Type) ?? d.Type },
            SetLocalStatement s1 => s1 with { Name = names.GetValueOrDefault(s1.Name, s1.Name), Value = Rename(s1.Value) },
            ConditionalInvokeStatement c => c with { Receiver = Rename(c.Receiver), Arguments = c.Arguments.Select(Rename).ToArray() },
            DelegateCacheStatement c => c with { Name = names[c.Name], Cache = (MemberExpression)Rename(c.Cache), Target = Rename(c.Target) },
            _ => s
        });
        void Emit(ulong address, ulong stop, int depth, HashSet<ulong> visiting)
        {
            while (address != stop && address != exit)
            {
                if (activeLoops.TryPeek(out var active))
                {
                    if (address == active.Header && visiting.Contains(address)) { text.AppendLine(new string(' ', depth * 4) + "continue;"); return; }
                    if (address == loopExits[active.Header][0]) { text.AppendLine(new string(' ', depth * 4) + "break;"); return; }
                }
                if (loops.Loops.SingleOrDefault(l => l.Header == address) is { } loop && !activeLoops.Contains(loop))
                {
                    var prefix = new string(' ', depth * 4);
                    var cleanup = result.Finally is { } region && region.Header == address ? region : null;
                    if (cleanup is not null) { text.AppendLine(prefix + "try"); text.AppendLine(prefix + "{"); depth++; prefix += "    "; }
                    text.AppendLine(prefix + "while (true)"); text.AppendLine(prefix + "{");
                    activeLoops.Push(loop); Emit(address, exit, depth + 1, new(visiting)); activeLoops.Pop();
                    text.AppendLine(prefix + "}"); address = loopExits[loop.Header][0];
                    if (cleanup is not null)
                    {
                        Emit(address, cleanup.Cleanup, depth, new(visiting));
                        depth--; prefix = new string(' ', depth * 4);
                        text.AppendLine(prefix + "}"); text.AppendLine(prefix + "finally"); text.AppendLine(prefix + "{");
                        foreach (var statement in result.Blocks[cleanup.Cleanup].Statements) text.AppendLine(prefix + "    " + S(statement));
                        text.AppendLine(prefix + "}"); address = cleanup.Continuation;
                    }
                    continue;
                }
                if (!visiting.Add(address)) throw new InvalidDataException("结构化遇到重复控制流");
                var block = result.Blocks[address]; var indent = new string(' ', depth * 4);
                foreach (var statement in block.Statements) text.AppendLine(indent + S(statement).Replace("\n", "\n" + indent));
                if (block.Successors.Length == 0) return;
                if (block.Successors.Length == 1) { address = block.Successors[0]; continue; }
                if (block.Condition is null) { text.AppendLine(indent + "UNRESOLVED_BRANCH();"); return; }
                var terminalIndex = TerminalOnly(block.Successors[0]) ? 0 : TerminalOnly(block.Successors[1]) ? 1 : -1;
                if (terminalIndex >= 0)
                {
                    var condition = terminalIndex == 0 ? block.Condition : Negate(block.Condition);
                    text.AppendLine(indent + "if " + E(condition)); text.AppendLine(indent + "{");
                    Emit(block.Successors[terminalIndex], exit, depth + 1, new(visiting)); text.AppendLine(indent + "}");
                    address = block.Successors[1 - terminalIndex]; continue;
                }
                if (activeLoops.TryPeek(out var current) && block.Successors.Contains(loopExits[current.Header][0]))
                {
                    var leaving = block.Successors[0] == loopExits[current.Header][0] ? 0 : 1;
                    text.AppendLine(indent + "if " + E(leaving == 0 ? block.Condition : Negate(block.Condition)) + " break;");
                    address = block.Successors[1 - leaving]; continue;
                }
                var common = post[block.Successors[0]].Intersect(post[block.Successors[1]]).ToArray();
                var join = common.OrderByDescending(n => post[n].Count).First();
                if (block.Successors.Contains(join))
                {
                    var branch = block.Successors[0] == join ? 1 : 0;
                    text.AppendLine(indent + "if " + E(branch == 0 ? block.Condition : Negate(block.Condition))); text.AppendLine(indent + "{");
                    Emit(block.Successors[branch], join, depth + 1, new(visiting)); text.AppendLine(indent + "}");
                    address = join; continue;
                }
                text.AppendLine(indent + "if " + E(block.Condition)); text.AppendLine(indent + "{");
                Emit(block.Successors[0], join, depth + 1, new(visiting)); text.AppendLine(indent + "}");
                text.AppendLine(indent + "else"); text.AppendLine(indent + "{");
                Emit(block.Successors[1], join, depth + 1, new(visiting)); text.AppendLine(indent + "}");
                address = join;
            }
        }
    }
}
