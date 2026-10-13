using System.Text;

namespace Cpp2CS.Nir;

public static class NirText
{
    public static string Format(NirModule module)
    {
        var text = new StringBuilder();
        text.AppendLine(module.Version);
        foreach (var space in module.MemorySpaces) text.AppendLine($"space @{space.Id}: address({space.AddressWidth}), local=[{space.LocalBase}, {space.LocalBase + space.LocalLength})");
        foreach (var data in module.DataObjects) text.AppendLine($"data @{data.Id}: @{data.Space}+{data.Address}, bytes={Convert.ToHexString(data.Bytes.AsSpan())}, writable={data.Writable}");
        foreach (var external in module.Externals) text.AppendLine($"external @{external.Id}{Signature(external.Signature)} effects={external.Effects} outcomes={external.Outcomes}");
        foreach (var function in module.Functions)
        {
            text.AppendLine($"function @{function.Id}{Signature(function.Signature)} entry=b{function.Entry.Id} outcomes={function.Outcomes} {{");
            foreach (var block in function.Blocks)
            {
                text.AppendLine($"  b{block.Id.Id}({string.Join(", ", block.Parameters.Select(Definition))}):");
                foreach (var operation in block.Operations) text.AppendLine("    " + Operation(operation));
                text.AppendLine("    " + Terminator(block.Terminator));
            }
            text.AppendLine("}");
        }
        return text.ToString();
    }
    public static string Type(NirType type) => type switch
    {
        NirBitsType bits => $"bits{bits.Width}", NirEffectType => "effect",
        NirExceptionType => "exception",
        NirAddressType address => $"address(@{address.Space},{address.Width})",
        NirFunctionType function => "function" + Signature(function.Signature) + $"[{function.Outcomes}]",
        _ => throw new ArgumentOutOfRangeException(nameof(type))
    };
    private static string Signature(NirSignature signature) => $"({string.Join(", ", signature.Parameters.Select(Type))}) -> ({string.Join(", ", signature.Results.Select(Type))})";
    private static string Value(NirValue value) => $"%{value.Id.Id}";
    private static string Definition(NirValue value) => Value(value) + ": " + Type(value.Type);
    private static string Values(IEnumerable<NirValue> values) => string.Join(", ", values.Select(Value));
    private static string Target(NirCallTarget target) => target switch
    {
        NirDirectTarget direct => "@" + direct.Function, NirIndirectTarget indirect => Value(indirect.Function),
        _ => throw new ArgumentOutOfRangeException(nameof(target))
    };
    private static string Edge(NirEdge edge) => $"b{edge.Target.Id}({Values(edge.Arguments)})";
    private static string Operation(NirOperation operation) => operation switch
    {
        NirConstant x => $"{Definition(x.Result)} = const {x.Bits}",
        NirFunctionConstant x => $"{Definition(x.Result)} = function @{x.Function}",
        NirPure x => $"{Definition(x.Result)} = {x.Code}({Values(x.Inputs)})" + (x.Code == NirPureCode.Extract ? $" offset={x.BitOffset}" : ""),
        NirFloat x => $"{Definition(x.Result)}, {Definition(x.Exceptions)} = float.{x.Spec.Kind}({Values(x.Inputs)}) spec={System.Text.Json.JsonSerializer.Serialize(x.Spec)}" +
            (x.Controls is { } controls ? $" controls=({Values(controls.Values)})" : ""),
        NirLoad x => $"{Definition(x.Result)}, {Value(x.Flow.Output)} = load.{x.Order}({Value(x.Address)}, {Value(x.Flow.Input)}) order={x.MemoryOrder} atomic={x.AtomicWidth} fault=propagate",
        NirStore x => $"{Value(x.Flow.Output)} = store.{x.Order}({Value(x.Address)}, {Value(x.Value)}, {Value(x.Flow.Input)}) order={x.MemoryOrder} atomic={x.AtomicWidth} fault=propagate",
        NirAtomicRmw x => $"{Definition(x.Result)}, {Value(x.Flow.Output)} = atomic.{x.Code}.{x.Order}({Value(x.Address)}, {Value(x.Value)}, {Value(x.Flow.Input)}) order={x.MemoryOrder} fault=propagate",
        NirCompareExchange x => $"{Definition(x.OldValue)}, {Definition(x.Success)}, {Value(x.Flow.Output)} = compare.exchange.{x.Order}({Value(x.Address)}, {Value(x.Expected)}, {Value(x.Replacement)}, {Value(x.Flow.Input)}) success={x.SuccessOrder} failure={x.FailureOrder} failure-writeback={x.WriteBackOnFailure} fault=propagate",
        NirFence x => $"{Value(x.Flow.Output)} = fence.{x.MemoryOrder}({Value(x.Flow.Input)})",
        NirLocalAlloc x => $"{Definition(x.Result)}, {Value(x.Flow.Output)} = local.alloc({Value(x.Size)}, align={x.Alignment}, {Value(x.Flow.Input)}) fault=propagate",
        NirChoose x => $"{Definition(x.Result)}, {Value(x.Flow.Output)} = choose({Value(x.Flow.Input)})",
        NirExceptionCreate x => $"{Definition(x.Result)}, {Value(x.Flow.Output)} = exception.create({Value(x.Flow.Input)})",
        NirEnvironmentRead x => $"{Definition(x.Result)}, {Value(x.Flow.Output)} = environment.read.{x.Field}({Value(x.Flow.Input)})",
        NirEnvironmentWrite x => $"{Value(x.Flow.Output)} = environment.write.{x.Field}({Value(x.Value)}, {Value(x.Flow.Input)})",
        NirCall x => $"{Values(x.Results.Append(x.Flow.Output))} = call {Target(x.Target)}({Values(x.Arguments.Append(x.Flow.Input))}) fault=propagate",
        _ => throw new ArgumentOutOfRangeException(nameof(operation))
    };
    private static string Terminator(NirTerminator terminator) => terminator switch
    {
        NirJump x => "jump " + Edge(x.Edge),
        NirBranch x => $"branch {Value(x.Condition)}, {Edge(x.WhenTrue)}, {Edge(x.WhenFalse)}",
        NirReturn x => $"return ({Values(x.Values.Append(x.Effect))})",
        NirTailCall x => $"tailcall {Target(x.Target)}({Values(x.Arguments.Append(x.Effect))})",
        NirNoReturnCall x => $"noreturn {Target(x.Target)}({Values(x.Arguments.Append(x.Effect))})",
        NirRaise x => $"raise {Value(x.Exception)}, {Value(x.Effect)}",
        NirInvoke x => $"invoke {Target(x.Target)}({Values(x.Arguments.Append(x.Effect))}) normal=" +
            (x.Normal is { } normal ? $"b{normal.Target.Id}(results..., {Values(normal.Captured)}, effect)" : "none") +
            $" unwind=b{x.Unwind.Target.Id}(exception, {Values(x.Unwind.Captured)}, effect)",
        NirFault x => $"fault {System.Text.Json.JsonSerializer.Serialize(x.Code)}, {Value(x.Effect)}",
        NirTerminate x => $"terminate {System.Text.Json.JsonSerializer.Serialize(x.Reason)}, {Value(x.Effect)}",
        _ => throw new ArgumentOutOfRangeException(nameof(terminator))
    };
}
