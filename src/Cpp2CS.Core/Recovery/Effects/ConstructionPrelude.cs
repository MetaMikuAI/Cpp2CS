using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Effects;

/// <summary>新对象在同块基类构造之前只接受字段初始化，保持私有身份供构造模板证明。</summary>
internal static class ConstructionPrelude
{
    internal static (DefinitionRef Type, MethodRef Base, ulong Address)? Find(MethodAnalysis analysis, TypeOracle oracle, Call allocation)
    {
        if (oracle.ClassOperand(allocation) is not DefinitionRef allocated) return null;
        var values = analysis.Values;
        var result = values.Syms.Result(allocation, 0, 64);
        var block = values.BlockOf(allocation);
        bool Contains(Sym value) => SymTable.Resolve(value) is var resolved && (ReferenceEquals(resolved, result) || resolved switch
        {
            ReadSym read => Contains(read.Address),
            SliceSym slice => Contains(slice.Base),
            ConcatSym concat => concat.Parts.Any(Contains),
            OpSym op => op.Args.Any(Contains),
            PhiSym => true,
            _ => false,
        });
        foreach (var statement in block.Statements.Skip(block.Statements.IndexOf(allocation) + 1))
        {
            var operands = values.Operands(statement);
            if (statement is Define && values.ReadsAt(statement).Count == 0 || statement is Nop) continue;
            if (statement is Store && oracle.Decompose(operands[0]).Root == result && !Contains(operands[1])) continue;
            if (statement is Call { Op.Kind: OpKind.WriteBarrier } && oracle.Decompose(operands[1]).Root == result && !Contains(operands[2])) continue;
            if (statement is not Call call || analysis.Environment.Shape(call).Signature?.This is not { } receiver
                || oracle.Callee(call) is not { Method: { Name: ".ctor", IsStatic: false }, DeclaringType: DefinitionRef declaring } constructor
                || declaring.Definition == allocated.Definition) return null;
            var content = values.ArgumentContent(call, receiver, operands.Skip(1).Take(call.Arguments.Length).ToArray());
            return SymTable.Resolve(content) == result ? (allocated, constructor, call.Address) : null;
        }
        return null;
    }
}
