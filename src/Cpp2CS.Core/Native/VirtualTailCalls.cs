using Cpp2CS.Abi;

namespace Cpp2CS.Native;

public sealed partial class FunctionLifter
{
    private bool TryVirtualTailCall(Instruction instruction, NativeState state, List<Statement> statements, LiftResult result)
    {
        var target = Read(state, instruction.Operands[0].Register!).Expression;
        var receiver = Read(state, "x0");
        if (Unwrap(target) is not MemberExpression { Field.Name: "methodPtr" } pointer ||
            Unwrap(pointer.Receiver) is not MemberExpression { Field.Name: "klass", Field.Offset: 0 } klass || klass.Receiver != receiver.Expression) return false;
        var type = receiver.Type.TrimEnd('*');
        if (!type.EndsWith("_o")) return false;
        var table = layouts.Members(type[..^2] + "_c").SingleOrDefault(f => f.Name == "vtable");
        if (table is null) return false;
        var slot = layouts.Members(table.Type).SingleOrDefault(f => f.Type == "VirtualInvokeData" && f.Offset + table.Offset == pointer.Field.Offset);
        if (slot is null || slot.Name.IndexOf('_', 1) is not > 0) return false;
        var name = slot.Name[(slot.Name.IndexOf('_', 1) + 1)..];
        var candidates = symbols.NamedMethods.GetValueOrDefault(symbols.Display(receiver.Type) + "$$" + name, []);
        if (candidates.Length != 1 || Classify(candidates[0]) is not { } abi ||
            abi.Arguments.Last().Pieces.ToArray() is not [{ Location: RegisterLocation register, Size: 8 }]) return false;
        var methodInfo = Read(state, register.Name.ToLowerInvariant()).Expression;
        if (Unwrap(methodInfo) is not MemberExpression { Field.Name: "method" } info || info.Receiver != pointer.Receiver ||
            info.Field.Offset != pointer.Field.Offset + layouts.Members("VirtualInvokeData").Single(f => f.Name == "method").Offset) return false;
        DirectCall(instruction, state, statements, result, candidates[0]);
        statements.Add(new ReturnStatement(instruction.Address, ReturnValue(result.Method, state)));
        foreach (var nameToRemove in new[] { target, methodInfo, pointer.Receiver }.OfType<CapturedExpression>().Select(c => c.Name))
            if (!result.Blocks.Values.Any(b => b.Statements.SelectMany(ViewNormalizer.Expressions).Any(e => ViewNormalizer.Count(e, nameToRemove) != 0) || b.Condition is { } condition && ViewNormalizer.Count(condition, nameToRemove) != 0))
                statements.RemoveAll(s => s is AssignStatement a && a.Name == nameToRemove);
        result.Proofs.Add(new(instruction.Address, "VirtualTailCall", "receiver class slot and paired MethodInfo; unique metadata method; managed virtual call retains dynamic dispatch"));
        return true;
    }
}
