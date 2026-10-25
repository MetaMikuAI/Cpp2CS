using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

[Flags]
public enum ReadabilityRules { None = 0, Int = 1, Null = 2, Goto = 4 }

/// <summary>
/// 定型后的局部等价改写，保留求值顺序与托管类型。
/// 由 BodyEmitter 在原有写出资格判定之后统一调用；不改变 L3 的洞与 L4 的接受集合。
/// </summary>
public static class ReadabilityRewriter
{
    public static ReadabilityRules FromEnvironment() => Parse(Environment.GetEnvironmentVariable("CPP2CS_READABILITY"));

    public static ReadabilityRules Parse(string? value)
    {
        if (value is null) return ReadabilityRules.Int | ReadabilityRules.Null;
        if (value == "none") return ReadabilityRules.None;
        if (value == "all") return ReadabilityRules.Int | ReadabilityRules.Null | ReadabilityRules.Goto;
        var rules = ReadabilityRules.None;
        foreach (var name in value.Split(','))
            rules |= name switch
            {
                "int" => ReadabilityRules.Int, "null" => ReadabilityRules.Null, "goto" => ReadabilityRules.Goto,
                _ => throw new ArgumentException($"CPP2CS_READABILITY 未知规则：{name}；可用 none、int、null、goto、all 或逗号组合"),
            };
        return rules;
    }

    public static ManagedBody Rewrite(ManagedBody body, ManagedTypes types, ReadabilityRules rules)
    {
        if ((rules & ReadabilityRules.Int) != 0)
            body = ManagedValues.Map(body, RewriteInteger);
        // 原规则只证明普通 CFG；跨 EH 边界的判空迁移和空块收缩需要额外证明。
        if (body.Regions.Count == 0 && (rules & ReadabilityRules.Null) != 0) body = AbsorbNull(body, types);
        if (body.Regions.Count == 0 && (rules & ReadabilityRules.Goto) != 0) body = BypassJumps(body);
        return body;
    }

    // 只处理固定宽度整数；bool、浮点、指针转换不能借此规则获得额外假设。
    private static bool Integer(ManagedValue value) => value.Width is 8 or 16 or 32 or 64
        && ManagedTypes.PrimitiveName(ManagedTypes.Underlying(value.Type)) is "SByte" or "Byte" or "Char" or "Int16" or "UInt16" or "Int32" or "UInt32" or "Int64" or "UInt64";

    private static ManagedValue RewriteInteger(ManagedValue value)
    {
        value = ManagedValues.Map(value, RewriteInteger);
        // ECMA-335 III.3.27：扩展不改变低 w 位，随后截回 w 位；类型也必须相同。
        return value is ConversionValue { Kind: ConvKind.Truncate,
            Operand: ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } extend } truncate
            && Integer(truncate) && Integer(extend) && Integer(extend.Operand)
            && extend.Width > extend.Operand.Width && truncate.Width == extend.Operand.Width
            && truncate.Type.Equals(extend.Operand.Type) ? extend.Operand : value;
    }

    private static IEnumerable<ManagedEdge> Edges(ManagedStatement statement) => ManagedValues.Edges(statement);

    private static Dictionary<ulong, int> Predecessors(ManagedBody body) => body.Blocks
        .SelectMany(b => b.Statements).SelectMany(Edges).GroupBy(e => e.Target).ToDictionary(g => g.Key, g => g.Count());

    private static ManagedBody AbsorbNull(ManagedBody body, ManagedTypes types)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var predecessors = Predecessors(body);
        ManagedStatement? Next(ManagedBlock block, int index)
        {
            var visited = new HashSet<ulong>();
            while (visited.Add(block.Address))
            {
                if (++index >= block.Statements.Count) return null;
                if (block.Statements[index] is not ManagedJump jump) return block.Statements[index];
                if (index != block.Statements.Count - 1 || jump.Edge.Copies.Count != 0
                    || jump.Edge.Target == body.Blocks[0].Address || predecessors.GetValueOrDefault(jump.Edge.Target) != 1) return null;
                block = blocks[jump.Edge.Target];
                index = -1;
            }
            return null;
        }

        bool Absorbed(ManagedBlock block, int index)
        {
            if (block.Statements[index] is not ManagedCheck
                {
                    Exception.Method: { Name: ".ctor", IsStatic: false, Parameters.Count: 0,
                        Owner: { Assembly: "mscorlib.dll", FullName: "System.NullReferenceException" } },
                    Condition: ComparisonValue { Condition: Cond.Eq } comparison,
                }) return false;
            var receiver = comparison.Right is ConstantValue { Bits: 0 } right && ManagedTypes.IsReferenceType(right.Type) ? comparison.Left
                : comparison.Left is ConstantValue { Bits: 0 } left && ManagedTypes.IsReferenceType(left.Type) ? comparison.Right : null;
            if (receiver is not (ArgumentValue or LocalValue) || !ManagedTypes.IsReferenceType(receiver.Type)
                || Next(block, index) is not ManagedAssignment assignment) return false;
            var value = assignment.Value;
            // bool/8 字段的 ZeroExtend 只表示整数位宽扩展。
            // 外层仍须为固定宽度整数，排除浮点与指针。字段读取后的扩展/掩码完全不改，不假定 bool 为 0/1。
            while (value is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } c
                && Integer(c) && (Integer(c.Operand) || c.Kind == ConvKind.ZeroExtend
                    && c.Operand.Width == 8 && c.Width > 8 && c.Operand.Type.Equals(types.Boolean))) value = c.Operand;
            // ECMA-335 III.4.10：同一引用的 ldfld 在这里抛 NRE；之前没有任何其他求值或边赋值。
            return value is FieldValue { Field.Field.IsStatic: false } field && field.Receiver == receiver
                && types.IsAssignable(receiver.Type, field.Field.DeclaringType)
                && ManagedAccess.Field(types, body.Method.Method.Owner, field.Field, receiver.Type);
        }

        return body with { Blocks = body.Blocks.Select(b => b with
        { Statements = b.Statements.Where((_, i) => !Absorbed(b, i)).ToArray() }).ToArray() };
    }

    private static ManagedBody BypassJumps(ManagedBody body)
    {
        // ManagedBody 尚无 EH 表达；仅收缩空跳转，保留入边的并行复制，不复制任何求值。
        while (true)
        {
            var predecessors = Predecessors(body);
            var candidate = body.Blocks.Skip(1).FirstOrDefault(b => predecessors.GetValueOrDefault(b.Address) == 1
                && b.Statements is [ManagedJump { Edge.Copies.Count: 0 } jump] && jump.Edge.Target != b.Address);
            if (candidate is null) return body;
            var target = ((ManagedJump)candidate.Statements[0]).Edge.Target;
            ManagedEdge Redirect(ManagedEdge edge) => edge.Target == candidate.Address ? edge with { Target = target } : edge;
            body = body with { Blocks = body.Blocks.Where(b => b != candidate).Select(b => b with
            {
                Statements = b.Statements.Select(s => ManagedValues.MapEdges(s, Redirect)).ToArray(),
            }).ToArray() };
            // 环中的最后一个块会成为自环并保留，绝不把无限循环变成退出。
        }
    }
}
