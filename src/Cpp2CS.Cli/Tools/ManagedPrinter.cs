using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Cli;

/// <summary>托管方法体的紧凑文本（调试用）。</summary>
internal static class ManagedPrinter
{
    internal static IEnumerable<string> Lines(ManagedBody body)
    {
        foreach (var block in body.Blocks)
        {
            yield return $"  M@0x{block.Address:x}";
            foreach (var statement in block.Statements) yield return "    " + Statement(statement);
        }
    }

    private static string Statement(ManagedStatement statement) => statement switch
    {
        ManagedAssignment a => $"{Value(a.Target)} = {Value(a.Value)}",
        ManagedStore s => $"{Value(s.Target)} := {Value(s.Value)}",
        ManagedCall c => $"{(c.Result is { } r ? Value(r) + " = " : "")}{(c.Tail ? "tail " : "")}{Invocation(c.Invocation)}",
        ManagedReturn r => $"return {(r.Value is { } v ? Value(v) : "")}",
        ManagedJump j => $"goto {Edge(j.Edge)}",
        ManagedBranch b => $"if {Value(b.Condition)} goto {Edge(b.Taken)} else {Edge(b.Fallthrough)}",
        ManagedThrow t => $"throw {Value(t.Exception)}",
        ManagedCheck c => $"check {Value(c.Condition)} → {c.Exception.DeclaringType}",
        ManagedHole h => $"HOLE {h.Reason}",
        _ => statement.ToString(),
    };

    private static string Edge(ManagedEdge edge) => $"0x{edge.Target:x}" + (edge.Copies.Count == 0 ? "" : $" [{string.Join(", ", edge.Copies.Select(c => $"{Value(c.Target)} = {Value(c.Value)}"))}]");

    private static string Invocation(ManagedInvocation i) =>
        $"{(i.Virtual ? "callvirt " : "")}{(i.Receiver is { } r ? Value(r) + "." : "")}{i.Method.Method.Name}({string.Join(", ", i.Arguments.Select(Value))})";

    internal static string Value(ManagedValue value) => value switch
    {
        ArgumentValue a => a.Index < 0 ? "this" : $"arg{a.Index}",
        LocalValue l => $"loc{l.Variable.Storage.Index}:{Short(l.Type)}",
        ConstantValue c => $"{c.Bits:x}:{Short(c.Type)}",
        StringValue s => $"\"{s.Text}\"",
        FieldValue f => $"{Value(f.Receiver)}.{f.Field.Field.Name}",
        StaticFieldValue s => $"{Short(s.Field.DeclaringType)}.{s.Field.Field.Name}",
        ArrayElementValue e => $"{Value(e.Array)}[{Value(e.Index)}]",
        ArrayLengthValue l => $"{Value(l.Array)}.Length",
        StringLengthValue l => $"{Value(l.String)}.Length",
        IndirectValue i => $"*{Value(i.Address)}",
        AddressValue a => $"&{Value(a.Target)}",
        BinaryValue b => $"({Value(b.Left)} {b.Op} {Value(b.Right)}):{Short(b.Type)}",
        UnaryValue u => $"{u.Op}({Value(u.Operand)})",
        ComparisonValue c => $"({Value(c.Left)} {c.Condition} {Value(c.Right)})",
        ConversionValue c => $"{c.Kind}<{Short(c.Type)}>({Value(c.Operand)})",
        ChoiceValue c => $"({Value(c.Condition)} ? {Value(c.True)} : {Value(c.False)})",
        BooleanValue b => $"({Value(b.Left)} {(b.IsAnd ? "&&" : "||")} {Value(b.Right)})",
        NegatedValue n => $"!{Value(n.Operand)}",
        NewObjectValue n => $"new {Short(n.Constructor.DeclaringType)}({string.Join(", ", n.Arguments.Select(Value))})",
        NewArrayValue n => $"new {Short(n.ArrayType)}({Value(n.Length)})",
        DelegateValue d => $"delegate {Short(d.DelegateType)}({Value(d.Target)}, {d.Method.Method.Name})",
        BoxValue b => $"box<{Short(b.Boxed)}>({Value(b.Operand)})",
        UnboxAddressValue u => $"unbox<{Short(u.Target)}>({Value(u.Operand)})",
        IsInstValue i => $"isinst<{Short(i.Target)}>({Value(i.Operand)})",
        ComposedValue c => $"{Short(c.Type)} {{{string.Join(", ", c.Leaves.Select(l => string.Join(".", l.Path.Select(p => p.Field.Name)) + " = " + Value(l.Value)))}}}",
        HoleValue h => $"HOLE<{h.Reason}>",
        _ => value.GetType().Name,
    };

    private static string Short(TypeRef type)
    {
        var text = type.ToString();
        var dot = text.LastIndexOf('.', text.IndexOf('<') is var lt and >= 0 ? lt : text.Length - 1);
        return dot >= 0 ? text[(dot + 1)..] : text;
    }
}
