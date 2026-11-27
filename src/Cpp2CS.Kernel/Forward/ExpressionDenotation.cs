using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Kernel.Forward;

/// <summary>
/// 一段写出的 IL 表达式代表哪个项（设计第 10 节“每个表达式写出之后按目录展开回项”）。这是按目录展开的读法，不是下降的事：
/// 展开、分情况、重建选择项、换回绑定都在这里，下降只调用唯一的入口 <see cref="Denote"/>。
/// </summary>
internal static class ExpressionDenotation
{
    /// <summary>
    /// 把表达式放进一个只含这段指令的方法体，按目录展开，读出栈顶的值（branch 给出时读出转移的条件），
    /// 再把形参与局部变量换回它们绑定的项。variable 给出 ldarg（真）或 ldloc（假）的第几个变量的类型与它绑定的项，类型未知时为空。
    /// 展开出效果的不是表达式。表达式可以含转移（选择的写法）。展开之后，从最后一个块（值是它的参数）出发，按内核的分情况（设计 7.3）
    /// 读出各情况的取值：一个情况且没有条件时就是这个值；两个情况、各只有同一个分支条件的一真一假时，是按这个条件的选择。
    /// 其余的不当作表达式，返回空。
    /// </summary>
    internal static Term? Denote(IReadOnlyList<ManagedInstruction> expression, string? branch, Func<bool, int, (TypeShape Type, Term Value)?> variable,
        IMetadataView metadata, TermPool terms, int pointerBits)
    {
        var parameters = new List<TypeShape>();
        var bindings = new List<Term>();
        var slots = new Dictionary<(bool, int), int>();
        var marks = new Dictionary<long, int>();
        // 表达式里的标号换成从 1 起的编号，0 留给末尾。
        int Mark(long label) => marks.TryGetValue(label, out int known) ? known : marks[label] = marks.Count + 1;
        var il = new IlWriter();
        foreach (var instruction in expression)
        {
            if (instruction.Opcode == ".label") il.Mark(Mark(instruction.Operand));
            else if (instruction.Target >= 0) il.Branch(instruction.Opcode, Mark(instruction.Target));
            else if (instruction.Opcode is "ldarg" or "ldloc")
            {
                bool isArgument = instruction.Opcode == "ldarg";
                int index = (int)instruction.Operand;
                if (!slots.TryGetValue((isArgument, index), out int slot))
                {
                    if (variable(isArgument, index) is not { } known) return null;
                    slot = slots[(isArgument, index)] = parameters.Count;
                    parameters.Add(known.Type);
                    bindings.Add(known.Value);
                }
                il.Variable("ldarg", slot);
            }
            else if (instruction.Opcode == "ldc.i4") il.Int32("ldc.i4", (int)instruction.Operand);
            else il.Plain(instruction.Opcode);
        }
        // 末尾：值的写法转到只做出栈与返回的块，转移的写法以给定的转移结束。last 是最后一个块的起点不超过的偏移。
        int last;
        if (branch is null) { il.Branch("br", 0); last = il.Offset; il.Mark(0); il.Plain("pop"); il.Plain("ret"); }
        else { last = il.Offset; il.Branch(branch, 0); il.Plain("ret"); il.Mark(0); il.Plain("ret"); }
        var body = new MethodBody(new MethodShape(default, false, [.. parameters], null, VariantCondition.StaticMethod), [], il.Build(), 0, true);
        Expansion expansion;
        try
        {
            expansion = IlExpander.Expand(body, metadata, new NoTokens(), terms, 1, pointerBits);
        }
        catch (ExpansionException)
        {
            return null;
        }
        var flow = expansion.Graph;
        if (flow.Blocks.Any(b => b.Occurrences.Length > 0)) return null;
        var offsets = expansion.BlockOffsets;
        int final = -1;
        for (int b = 0; b < offsets.Length; b++)
            if (offsets[b] >= 0 && offsets[b] <= last && (final < 0 || offsets[b] > offsets[final])) final = b;
        if (final < 0) return null;
        var block = new BlockId(final);
        var row = flow.Parameters(block);
        Term value = branch is null ? row[^1] : flow.Terminator(block).Condition!;

        // 从最后一个块的参数出发分情况。形参在每个块里都是参数，有形参时展开一直到入口块，各情况的取值与条件只含入口的形参；
        // 没有形参时取值只含常量，在哪个块停下都一样。
        var table = new ValueSources(flow, terms).SplitCases(new ProgramPoint(block, 0), [value, .. row]);
        if (!table.Complete || table.Cases.Length is not (1 or 2)) return null;
        var map = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        foreach (var parameter in flow.EntryParameters) map[parameter] = bindings[parameter.Slot.Index];
        if (table.Cases.Length == 1) return table.Cases[0].Conditions.IsEmpty ? Substitute(terms, table.Cases[0].Terms[0], map) : null;
        Term? test = null;
        var arms = new Term?[2];
        foreach (var item in table.Cases)
        {
            if (item.Origin != flow.Entry) return null;
            // 情况的条件先列选择条件，再列所经各条入边的文字：只许有一条，且是一个二路分支的条件。
            int branches = item.Edges.Count(e => flow.Terminator(e.Source).Kind != TerminatorKind.Single);
            if (item.Conditions.Length != 1 || branches != 1 || item.Conditions[0] is not { Kind: LiteralKind.Condition, Term: { } condition } literal) return null;
            if (test is not null && !ReferenceEquals(test, condition)) return null;
            test = condition;
            int arm = literal.Value != 0 ? 0 : 1;
            if (arms[arm] is not null) return null;
            arms[arm] = item.Terms[0];
        }
        return terms.Select(Substitute(terms, test!, map), Substitute(terms, arms[0]!, map), Substitute(terms, arms[1]!, map));
    }

    private static Term Substitute(TermPool terms, Term term, Dictionary<Term, Term> map)
    {
        if (map.TryGetValue(term, out var bound)) return bound;
        if (term.Operands.Length == 0) return term;
        var parts = new Term[term.Operands.Length];
        bool changed = false;
        for (int i = 0; i < parts.Length; i++)
        {
            parts[i] = Substitute(terms, term.Operands[i], map);
            changed |= !ReferenceEquals(parts[i], term.Operands[i]);
        }
        return changed ? terms.Rebuild(term, parts) : term;
    }

    private sealed class NoTokens : ITokenResolver
    {
        public EntityRef Method(int token) => throw new ExpansionException("表达式里没有记号", "");
        public EntityRef Field(int token) => throw new ExpansionException("表达式里没有记号", "");
        public EntityRef Type(int token) => throw new ExpansionException("表达式里没有记号", "");
        public EntityRef String(int token) => throw new ExpansionException("表达式里没有记号", "");
    }
}
