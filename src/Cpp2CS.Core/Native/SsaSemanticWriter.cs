namespace Cpp2CS.Native;

public static class SsaSemanticWriter
{
    public static string Write(SsaRecovery recovery) => string.Join('\n', recovery.Calls
        .Select(c => (c.Address, Text: $"0x{c.Address:x}: {c.Kind} {c.Value} = {c.Name}({string.Join(", ", c.Arguments.Select(Value))})"))
        .Concat(recovery.Stores.Select(s => (s.Address, Text: $"0x{s.Address:x}: store{ s.Value.Width } {Value(s.AddressValue)} <- {Value(s.Value)}")))
        .OrderBy(x => x.Address).Select(x => x.Text));
    private static string Value(SemanticTerm value) => value.Kind switch
    {
        "constant" => $"0x{value.Offset:x}:{value.Width}",
        "parameter" => value.Name,
        "stack" => "frame",
        "address" => $"({Value(value.Inputs[0])}{(value.Offset >= 0 ? "+" : "")}{value.Offset})",
        "field" or "value-field" => $"{Value(value.Inputs[0])}.{value.Name}",
        "call-storage" => $"after({value.Name}, {Value(value.Inputs[0])})",
        "metadata" => value.Name,
        "metadata-slot" => "&" + value.Name,
        "call-result" => value.Name,
        "slice" => $"bits({Value(value.Inputs[0])}, {value.Offset}, {value.Width})",
        "new-object" => $"new({value.Type}, {value.Name})",
        "phi" => $"phi[{value.Name}]({string.Join(", ", value.Inputs.Select(Value))})",
        _ => $"{value.Kind}[{value.Name}]({string.Join(", ", value.Inputs.Select(Value))})"
    };
}
