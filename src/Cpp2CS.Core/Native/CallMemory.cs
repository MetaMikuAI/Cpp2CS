using Cpp2CS.Abi;
using Cpp2CS.IR;

namespace Cpp2CS.Native;

public sealed partial class FunctionLifter
{
    private readonly Dictionary<(ulong Address, string Register), bool> unusedArguments = [];
    private bool UnusedArgument(NativeMethod method, AbiValue argument)
    {
        if (argument.Pieces is not [var piece] || piece.Location is not RegisterLocation register) return false;
        var key = (method.Address, Arm64Registers.Canonical(register.Name));
        if (unusedArguments.TryGetValue(key, out var known)) return known;
        var boundary = UnwindBoundary.Read(image, method.Address);
        var unused = false;
        if (boundary.Start == method.Address && boundary.End > method.Address && boundary.End - method.Address <= 16384 && boundary.Lsda is null && boundary.Unsupported is null)
        {
            var instructions = decoder.Decode(image.Read(method.Address, (int)(boundary.End - method.Address)), method.Address);
            var graph = new NativeGraph(instructions, runtime.NoReturn, target => symbols.Unique(target) is not null || runtime.Helpers.ContainsKey(target));
            var abi = new NativeAbi(layouts, managed);
            unused = UnusedReceiver.Prove(graph, key.Item2, call => Arm64Calls.Inputs(call, symbols, abi, runtime));
        }
        unusedArguments[key] = unused;
        return unused;
    }
    private static bool MayReferenceStack(NativeValue value)
    {
        var possible = value.Type is "stack-address" or "unknown";
        SourceTree.Map(value.Expression, expression =>
        {
            possible |= expression is StackAddressExpression or UnknownExpression;
            return expression;
        });
        return possible;
    }
    private void TransferCallMemory(ulong pc, NativeMethod method, CallLayout layout, List<NativeValue> arguments,
        StackAddressExpression? returnBuffer, NativeState state, LiftResult result)
    {
        var receiverType = new NativeAbi(layouts, managed).MutableReceiverType(method);
        var receiver = arguments.FirstOrDefault()?.Expression as StackAddressExpression;
        var boundReceiver = receiver is not null && receiverType is not null &&
            mutableStack.TryGetValue(receiver.Offset, out var local) && local.Type == receiverType;
        var possible = arguments.Select((value, index) => (value, index)).Where(p => (!boundReceiver || p.index != 0) && MayReferenceStack(p.value)).ToArray();
        var mayWrite = possible.Any(p => !UnusedArgument(method, layout.Arguments[p.index]));
        foreach (var (_, index) in possible.Where(p => UnusedArgument(method, layout.Arguments[p.index])))
            result.Proofs.Add(new(pc, "UnusedCallArgument", $"argument {index}: callee never reads the input before a full overwrite; shared machine effects and call ABI"));
        if (state.StackEscaped || mayWrite || layout.Return.Indirect && returnBuffer is null)
        {
            result.Proofs.Add(new(pc, "CallStackInvalidation", $"prior escape={state.StackEscaped}; possible stack arguments=" +
                string.Join(",", possible.Select(p => p.index)) +
                $"; bound receiver={boundReceiver}; unknown return buffer={layout.Return.Indirect && returnBuffer is null}"));
            InvalidateCallMemory(state, pc);
            return;
        }
        if (!boundReceiver) return;
        // 已绑定的可变局部随实例调用更新；调用前的寄存器快照仍引用旧身份。
        var name = mutableStack[receiver!.Offset].Name;
        var previous = NativeValues.LoadStack(state, stackRegion, receiver.Offset, layouts.Size(receiverType!));
        var value = new NativeValue(new InputBits($"after-call:{pc:x}", layouts.Size(receiverType!) * 8), receiverType!, new NameExpression(name));
        aggregateValues[value.Bits] = (value.Type, value.Expression);
        if (aggregateLogicalTypes.TryGetValue(previous.Bits, out var logical)) aggregateLogicalTypes[value.Bits] = logical;
        NativeValues.StoreStack(state, stackRegion, receiver.Offset, value, $"call:{pc:x}");
    }
}
