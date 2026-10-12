namespace Cpp2CS.Native;

public sealed record UniTaskStorage(string Type, int Bytes, HeaderField Source, HeaderField Token, HeaderField? Result)
{
    public static UniTaskStorage? Read(string nativeType, Symbols symbols, HeaderLayout layouts)
    {
        var (name, arguments) = ManagedNames.SplitGeneric(symbols.Display(nativeType));
        if (name != "Cysharp.Threading.Tasks.UniTask" || arguments.Length > 1) return null;
        var fields = layouts.Flatten(nativeType, 0).ToArray();
        var source = fields.Where(f => f.Name == "source" && f.Type.EndsWith('*') && f.Size == 8).ToArray();
        var token = fields.Where(f => f.Name == "token" && f.Type == "int16_t" && f.Size == 2).ToArray();
        var result = fields.Where(f => f.Name == "result").ToArray();
        if (source.Length != 1 || token.Length != 1 || result.Length != arguments.Length || fields.Length != 2 + result.Length) return null;
        return new(symbols.Display(nativeType), layouts.Size(nativeType), source[0], token[0], result.SingleOrDefault());
    }
    public SemanticTerm ReadSource(SemanticTerm value) => SsaSemantics.Slice(value, Source.Offset * 8, Source.Size * 8);
    public SemanticTerm ReadToken(SemanticTerm value) => SsaSemantics.Slice(value, Token.Offset * 8, Token.Size * 8);
    public SemanticTerm? ReadInlineResult(SemanticTerm value) => Result is { } field ? SsaSemantics.Slice(value, field.Offset * 8, field.Size * 8) : null;
}
