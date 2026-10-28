namespace Cpp2CS.Structure;

public sealed record SourcePass(string Rule, bool Changed, int InputStatements, int OutputStatements, double Milliseconds);
