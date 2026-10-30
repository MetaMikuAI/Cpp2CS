using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed class StructsState : IStatementKeyed
{
    internal readonly Dictionary<Variable, Fragment> fragmentLocals = new();
    internal readonly Dictionary<Variable, Expr> fragmentDefinitions = new();
    internal readonly HashSet<Variable> fragmentActive = [];
    internal int fragmentSteps;
    internal readonly NameSupply Locals = new(-1, -1);
    internal readonly Dictionary<Variable, (StructPhi Group, AbiPiece Piece)> structPhiMembers = new();
    internal readonly List<StructPhi> structPhis = [];
    internal readonly Dictionary<Call, LocalValue> structResults = new(ReferenceEqualityComparer.Instance);
    internal readonly Dictionary<TypeRef, (FieldRef[] Path, TypeRef Type, int Offset)[]> scalarPaths = new();

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(structResults, previous, replacement);
    }
}
