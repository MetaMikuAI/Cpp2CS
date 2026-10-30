namespace Cpp2CS.Model;

/// <summary>C 数学库中同精度标量函数的签名；带指针出参的函数另行处理。</summary>
internal sealed record MathImportSignature(bool Single, string[] Parameters)
{
    internal static MathImportSignature? Find(string? symbol)
    {
        if (symbol is null) return null;
        var single = symbol.EndsWith('f');
        var name = single ? symbol[..^1] : symbol;
        string[]? parameters = name switch
        {
            "sin" or "cos" or "tan" or "asin" or "acos" or "atan"
                or "exp" or "exp2" or "log" or "log2" or "log10" or "logb"
                or "sqrt" or "cbrt" or "fabs" or "floor" or "ceil" or "round" or "trunc" => ["value"],
            "fmod" => ["value", "divisor"],
            "pow" => ["value", "power"],
            "atan2" => ["y", "x"],
            "hypot" => ["x", "y"],
            _ => null,
        };
        return parameters is null ? null : new(single, parameters);
    }
}
