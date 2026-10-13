using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.SemanticCore;

namespace Cpp2CS.Nir;

public static class NirInterpreter
{
    private sealed class Frame
    {
        public NirFunction Function { get; }
        public Dictionary<NirBlockId, NirBlock> Blocks { get; }
        public Dictionary<NirValueId, NirRuntimeValue> Values { get; } = [];
        public List<NirAllocation> Allocations { get; } = [];
        public NirBlock Block { get; set; }
        public int Position { get; set; }
        public NirCall? ReturnBinding { get; }
        public bool ForbidReturn { get; }
        public Frame(NirFunction function, NirBlockId entry, ImmutableArray<NirRuntimeValue> arguments,
            NirRuntimeValue effect, NirCall? binding, bool forbidReturn)
        {
            Function = function;
            Blocks = function.Blocks.ToDictionary(b => b.Id);
            Block = Blocks[entry];
            ReturnBinding = binding;
            ForbidReturn = forbidReturn;
            BindEntry([.. arguments, effect]);
        }
        public void BindEntry(ImmutableArray<NirRuntimeValue> arguments)
        {
            for (var i = 0; i < arguments.Length; i++) Values[Block.Parameters[i].Id] = arguments[i];
            Position = 0;
        }
        public NirRuntimeValue Get(NirValue value) => Values[value.Id];
        public void Set(NirValue value, NirRuntimeValue data) => Values[value.Id] = data;
    }

    public static NirExecutionResult Execute(NirModule module, string function, IEnumerable<NirRuntimeValue> arguments,
        NirExecutionContext? context = null, NirExecutionOptions? options = null)
    {
        var validation = NirValidator.Validate(module);
        if (!validation.IsValid) return new(NirExecutionStatus.InvalidModule, [], 0, 0, "NIR validation failed", validation.Diagnostics, []);
        options ??= new();
        if (options.MaxSteps < 1 || options.MaxDepth < 1 || options.MaxAllocationBytes < 1)
            return new(NirExecutionStatus.InvalidInput, [], 0, 0, "Execution limits must be positive", [], []);
        if (context is not null && !ReferenceEquals(context.Module, module))
            return new(NirExecutionStatus.InvalidInput, [], 0, 0, "Context belongs to another module", [], []);
        context ??= new(module);
        var functions = module.Functions.ToDictionary(f => f.Id, StringComparer.Ordinal);
        var externals = module.Externals.ToDictionary(e => e.Id, StringComparer.Ordinal);
        var stack = new Stack<Frame>();
        long steps = 0;
        NirExecutionResult Result(NirExecutionStatus status, string? detail = null, ImmutableArray<NirRuntimeValue> values = default)
        {
            var outcome = status switch { NirExecutionStatus.Faulted => NirOutcomes.Fault, NirExecutionStatus.Terminated => NirOutcomes.Terminate, _ => NirOutcomes.None };
            if (outcome != NirOutcomes.None && stack.Any(f => !f.Function.Outcomes.HasFlag(outcome)))
            { status = NirExecutionStatus.ContractViolation; detail = "Observed outcome exceeds active function contract: " + detail; }
            return new(status, values.IsDefault ? [] : values, context.Effect, steps, detail, [], [.. context.Events]);
        }
        bool ValidValue(NirRuntimeValue value, NirType expected)
        {
            if (!NirInspection.TypeEquals(value.Type, expected)) return false;
            if (expected is NirFunctionType functionType)
            {
                if (value.Function is null || !value.Bits.IsZero) return false;
                var signature = functions.TryGetValue(value.Function, out var target) ? target.Signature : externals.GetValueOrDefault(value.Function)?.Signature;
                var targetOutcomes = target?.Outcomes ?? externals.GetValueOrDefault(value.Function)?.Outcomes ?? NirOutcomes.None;
                return signature is not null && NirInspection.SignatureEquals(signature, functionType.Signature) && (targetOutcomes & ~functionType.Outcomes) == 0;
            }
            var width = expected switch { NirBitsType x => x.Width, NirAddressType x => x.Width, _ => 0 };
            return width > 0 && value.Function is null && value.Bits >= 0 && value.Bits <= BitVectorMath.Mask(width);
        }
        bool ValidValues(ImmutableArray<NirRuntimeValue> values, ImmutableArray<NirType> expected) =>
            !values.IsDefault && values.Length == expected.Length && values.Where((value, i) => !ValidValue(value, expected[i])).Any() == false;
        var args = arguments.ToImmutableArray();
        if (!functions.TryGetValue(function, out var root) || !ValidValues(args, root.Signature.Parameters))
            return Result(NirExecutionStatus.InvalidInput, "Unknown function or invalid arguments");
        var entry = options.Entry ?? root.Entry;
        if (entry != root.Entry && !root.AdditionalEntries.Contains(entry)) return Result(NirExecutionStatus.InvalidInput, "Entry is not an external entry of the function");
        stack.Push(new(root, entry, args, context.Token(), null, false));

        NirExecutionResult? Invoke(Frame caller, NirCallTarget target, ImmutableArray<NirValue> inputValues,
            NirCall? binding, bool tail, bool noReturn)
        {
            var input = inputValues.Select(caller.Get).ToImmutableArray();
            var name = target is NirDirectTarget direct ? direct.Function : caller.Get(((NirIndirectTarget)target).Function).Function;
            if (name is null) return Result(NirExecutionStatus.ContractViolation, "Invalid function reference");
            var internalFunction = functions.GetValueOrDefault(name);
            var external = externals.GetValueOrDefault(name);
            var signature = internalFunction?.Signature ?? external?.Signature;
            var possible = internalFunction?.Outcomes ?? external?.Outcomes ?? NirOutcomes.None;
            if (signature is null || !ValidValues(input, signature.Parameters)) return Result(NirExecutionStatus.ContractViolation, "Call signature mismatch");
            if (noReturn && possible.HasFlag(NirOutcomes.Return)) return Result(NirExecutionStatus.ContractViolation, "No-return target contract permits return");
            if (!tail && !noReturn && !possible.HasFlag(NirOutcomes.Return)) return Result(NirExecutionStatus.ContractViolation, "Ordinary call target contract excludes return");
            if ((possible & (NirOutcomes.Fault | NirOutcomes.Terminate | NirOutcomes.Diverge) & ~caller.Function.Outcomes) != 0)
                return Result(NirExecutionStatus.ContractViolation, "Target outcomes exceed caller contract");
            if (target is NirIndirectTarget indirect && !ValidValue(caller.Get(indirect.Function), indirect.Function.Type))
                return Result(NirExecutionStatus.ContractViolation, "Indirect target violates function-value contract");
            var returnBinding = tail ? caller.ReturnBinding : binding;
            var forbidReturn = noReturn || tail && caller.ForbidReturn;
            if (tail)
            {
                stack.Pop();
                context.Memory.Release(caller.Allocations);
            }
            context.Advance(tail ? "tail-call" : noReturn ? "no-return-call" : "call", caller.Function.Id, name);
            if (internalFunction is not null)
            {
                if (stack.Count >= options.MaxDepth) return Result(NirExecutionStatus.BudgetExceeded, "Call depth budget exceeded");
                stack.Push(new(internalFunction, internalFunction.Entry, input, context.Token(), returnBinding, forbidReturn));
                return null;
            }
            if (!context.Externals.TryGetValue(name, out var implementation)) return Result(NirExecutionStatus.MissingExternal, name);
            var invocation = new NirExternalInvocation(external!, input, context.Memory);
            var output = implementation(invocation);
            if (invocation.Violation is not null) return Result(NirExecutionStatus.ContractViolation, invocation.Violation);
            var actual = output.Outcome switch
            {
                NirExternalOutcome.Return => NirOutcomes.Return, NirExternalOutcome.Fault => NirOutcomes.Fault,
                NirExternalOutcome.Terminate => NirOutcomes.Terminate, _ => NirOutcomes.None
            };
            if (actual == NirOutcomes.None || !possible.HasFlag(actual)) return Result(NirExecutionStatus.ContractViolation, "External result violates declared outcomes");
            if (output.Outcome == NirExternalOutcome.Fault) return Result(NirExecutionStatus.Faulted, output.Detail ?? "ExternalFault");
            if (output.Outcome == NirExternalOutcome.Terminate) return Result(NirExecutionStatus.Terminated, output.Detail ?? "ExternalTermination");
            if (forbidReturn) return Result(NirExecutionStatus.ContractViolation, "No-return invocation returned");
            if (!ValidValues(output.Values, signature.Results)) return Result(NirExecutionStatus.ContractViolation, "External results violate declared signature");
            if (tail)
            {
                if (stack.Count == 0) return Result(NirExecutionStatus.Returned, values: output.Values);
                BindReturn(stack.Peek(), returnBinding!, output.Values, context.Token());
            }
            else BindReturn(caller, binding!, output.Values, context.Token());
            return null;
        }

        while (stack.Count > 0)
        {
            if (steps >= options.MaxSteps) return Result(NirExecutionStatus.BudgetExceeded, "Step budget exceeded");
            steps++;
            var frame = stack.Peek();
            if (frame.Position < frame.Block.Operations.Length)
            {
                var operation = frame.Block.Operations[frame.Position++];
                if (NirInspection.Flow(operation) is { } flow && frame.Get(flow.Input).Bits != context.Effect)
                    return Result(NirExecutionStatus.ContractViolation, "Runtime Effect chain is stale");
                switch (operation)
                {
                    case NirConstant constant: frame.Set(constant.Result, new(constant.Result.Type, constant.Bits)); break;
                    case NirFunctionConstant constant:
                    {
                        var value = new NirRuntimeValue(constant.Result.Type, 0, constant.Function);
                        if (!ValidValue(value, constant.Result.Type)) return Result(NirExecutionStatus.ContractViolation, "Function constant outcome contract mismatch");
                        frame.Set(constant.Result, value);
                        break;
                    }
                    case NirPure pure: frame.Set(pure.Result, EvaluatePure(pure, pure.Inputs.Select(frame.Get).ToArray())); break;
                    case NirChoose choose:
                        if (!context.Choices.TryDequeue(out var choice)) return Result(NirExecutionStatus.MissingInput, "Choose requires an explicit dynamic choice");
                        var chosen = new NirRuntimeValue(choose.Result.Type, choice);
                        if (!ValidValue(chosen, choose.Result.Type)) return Result(NirExecutionStatus.InvalidInput, "Choice exceeds declared width");
                        context.Advance("choose", frame.Function.Id);
                        frame.Set(choose.Result, chosen);
                        frame.Set(choose.Flow.Output, context.Token());
                        break;
                    case NirLoad load:
                    {
                        var address = frame.Get(load.Address);
                        var read = context.Memory.Read(((NirAddressType)address.Type).Space, address.Bits, ((NirBitsType)load.Result.Type).Width / 8);
                        context.Advance("read", frame.Function.Id, read.Error);
                        if (!read.Success) return Result(read.MissingInput ? NirExecutionStatus.MissingInput : NirExecutionStatus.Faulted, read.Error);
                        var bits = new BigInteger(read.Bytes.AsSpan(), isUnsigned: true, isBigEndian: load.Order == NirByteOrder.Big);
                        frame.Set(load.Result, new(load.Result.Type, bits));
                        frame.Set(load.Flow.Output, context.Token());
                        break;
                    }
                    case NirStore store:
                    {
                        var address = frame.Get(store.Address);
                        var value = frame.Get(store.Value);
                        var length = ((NirBitsType)value.Type).Width / 8;
                        var raw = new byte[length];
                        var bytes = value.Bits.ToByteArray(isUnsigned: true, isBigEndian: store.Order == NirByteOrder.Big);
                        bytes.CopyTo(raw, store.Order == NirByteOrder.Big ? length - bytes.Length : 0);
                        var write = context.Memory.Write(((NirAddressType)address.Type).Space, address.Bits, [.. raw]);
                        context.Advance("write", frame.Function.Id, write.Error);
                        if (!write.Success) return Result(NirExecutionStatus.Faulted, write.Error);
                        frame.Set(store.Flow.Output, context.Token());
                        break;
                    }
                    case NirLocalAlloc alloc:
                    {
                        var size = frame.Get(alloc.Size).Bits;
                        if (size > options.MaxAllocationBytes) return Result(NirExecutionStatus.BudgetExceeded, "Local allocation exceeds execution budget");
                        var allocation = context.Memory.Allocate(((NirAddressType)alloc.Result.Type).Space, (int)size, alloc.Alignment);
                        context.Advance("allocate", frame.Function.Id);
                        if (allocation is null) return Result(NirExecutionStatus.Faulted, "LocalAllocationFailed");
                        frame.Allocations.Add(allocation);
                        frame.Set(alloc.Result, new(alloc.Result.Type, allocation.Address));
                        frame.Set(alloc.Flow.Output, context.Token());
                        break;
                    }
                    case NirCall call:
                        var result = Invoke(frame, call.Target, call.Arguments, call, false, false);
                        if (result is not null) return result;
                        break;
                    default: throw new InvalidOperationException("Validated NIR contains an unknown operation");
                }
                continue;
            }
            switch (frame.Block.Terminator)
            {
                case NirJump jump: Follow(frame, jump.Edge); break;
                case NirBranch branch: Follow(frame, frame.Get(branch.Condition).Bits.IsZero ? branch.WhenFalse : branch.WhenTrue); break;
                case NirReturn ret:
                {
                    var output = ret.Values.Select(frame.Get).ToImmutableArray();
                    if (frame.Get(ret.Effect).Bits != context.Effect) return Result(NirExecutionStatus.ContractViolation, "Stale return Effect");
                    if (frame.ForbidReturn || !frame.Function.Outcomes.HasFlag(NirOutcomes.Return)) return Result(NirExecutionStatus.ContractViolation, "No-return function returned");
                    stack.Pop();
                    context.Memory.Release(frame.Allocations);
                    if (stack.Count == 0) return Result(NirExecutionStatus.Returned, values: output);
                    BindReturn(stack.Peek(), frame.ReturnBinding!, output, context.Token());
                    break;
                }
                case NirTailCall tail:
                {
                    var result = Invoke(frame, tail.Target, tail.Arguments, null, true, false);
                    if (result is not null) return result;
                    break;
                }
                case NirNoReturnCall call:
                {
                    var result = Invoke(frame, call.Target, call.Arguments, null, false, true);
                    if (result is not null) return result;
                    break;
                }
                case NirFault fault: return Result(NirExecutionStatus.Faulted, fault.Code);
                case NirTerminate terminate: return Result(NirExecutionStatus.Terminated, terminate.Reason);
                default: throw new InvalidOperationException("Validated NIR contains an unknown terminator");
            }
        }
        throw new InvalidOperationException("NIR execution ended without an outcome");
    }

    private static void BindReturn(Frame caller, NirCall binding, ImmutableArray<NirRuntimeValue> values, NirRuntimeValue effect)
    {
        for (var i = 0; i < values.Length; i++) caller.Set(binding.Results[i], values[i]);
        caller.Set(binding.Flow.Output, effect);
    }
    private static void Follow(Frame frame, NirEdge edge)
    {
        var arguments = edge.Arguments.Select(frame.Get).ToImmutableArray();
        frame.Block = frame.Blocks[edge.Target];
        frame.BindEntry(arguments);
    }
    private static NirRuntimeValue EvaluatePure(NirPure operation, NirRuntimeValue[] inputs)
    {
        var a = inputs[0].Bits;
        var b = inputs.Length > 1 ? inputs[1].Bits : BigInteger.Zero;
        var aw = inputs[0].Type is NirBitsType ab ? ab.Width : inputs[0].Type is NirAddressType aa ? aa.Width : 0;
        var width = operation.Result.Type is NirBitsType rb ? rb.Width : operation.Result.Type is NirAddressType ra ? ra.Width : 0;
        if (operation.Code == NirPureCode.Select) return inputs[a.IsZero ? 2 : 1] with { Type = operation.Result.Type };
        var bits = operation.Code switch
        {
            NirPureCode.Add or NirPureCode.AddressAdd => a + b, NirPureCode.Sub => a - b, NirPureCode.Mul => a * b,
            NirPureCode.And => a & b, NirPureCode.Or => a | b, NirPureCode.Xor => a ^ b, NirPureCode.Not => ~a,
            NirPureCode.Shl => BitVectorMath.ShiftLeft(a, b, width), NirPureCode.Shr => BitVectorMath.ShiftRight(a, b, width),
            NirPureCode.Sar => BitVectorMath.ArithmeticRight(a, b, width),
            NirPureCode.UDiv => BitVectorMath.UnsignedDivide(a, b), NirPureCode.SDiv => BitVectorMath.SignedDivide(a, b, width),
            NirPureCode.Eq => a == b && inputs[0].Function == inputs[1].Function ? BigInteger.One : BigInteger.Zero,
            NirPureCode.Ult => a < b ? BigInteger.One : BigInteger.Zero,
            NirPureCode.Slt => BitVectorMath.Signed(a, aw) < BitVectorMath.Signed(b, aw) ? BigInteger.One : BigInteger.Zero,
            NirPureCode.Zext or NirPureCode.AddressToBits or NirPureCode.BitsToAddress => a,
            NirPureCode.Sext => BitVectorMath.Signed(a, aw), NirPureCode.Extract => a >> operation.BitOffset,
            NirPureCode.Concat => (a << ((NirBitsType)inputs[1].Type).Width) | b,
            _ => throw new InvalidOperationException("Validated NIR contains an unknown pure operation")
        };
        return new(operation.Result.Type, BitVectorMath.Wrap(bits, width));
    }
}
