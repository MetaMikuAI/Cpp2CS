
namespace Cpp2CS.Extensions.SourceView;

public sealed record SourcePass(string Rule, bool Changed, int InputStatements, int OutputStatements, double Milliseconds);
