using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.SemanticCore;

namespace Cpp2CS.Nir;

public static class NirInterpreter
{
    private sealed record Continuation(NirCall? Call, NirInvoke? Invoke,
        ImmutableArray<NirRuntimeValue> NormalCaptured, ImmutableArray<NirRuntimeValue> UnwindCaptured);
    private sealed class Frame
    {
        public NirFunction Function { get; }
        public Dictionary<NirBlockId, NirBlock> Blocks { get; }
        public Dictionary<NirValueId, NirRuntimeValue> Values { get; } = [];
        public List<NirAllocation> Allocations { get; } = [];
        public NirBlock Block { get; set; }
        public int Position { get; set; }
        public Continuation? ReturnBinding { get; }
        public bool ForbidReturn { get; }
        public Frame(NirFunction function, NirBlockId entry, ImmutableArray<NirRuntimeValue> arguments,
            NirRuntimeValue effect, Continuation? binding, bool forbidReturn)
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
        NirExecutionResult Result(NirExecutionStatus status, string? detail = null, ImmutableArray<NirRuntimeValue> values = default,
            NirRuntimeValue? exception = null)
        {
            var outcome = status switch { NirExecutionStatus.Faulted => NirOutcomes.Fault, NirExecutionStatus.Terminated => NirOutcomes.Terminate, _ => NirOutcomes.None };
            if (outcome != NirOutcomes.None && stack.Any(f => !f.Function.Outcomes.HasFlag(outcome)))
            { status = NirExecutionStatus.ContractViolation; detail = "Observed outcome exceeds active function contract: " + detail; }
            if (outcome != NirOutcomes.None)
                while (stack.TryPop(out var completed)) context.Memory.Release(completed.Allocations);
            return new(status, values.IsDefault ? [] : values, context.Effect, steps, detail, [], [.. context.Events], exception);
        }
        bool ValidValue(NirRuntimeValue value, NirType expected)
        {
            if (value is null) return false;
            if (!NirInspection.TypeEquals(value.Type, expected)) return false;
            if (expected is NirExceptionType)
                return value.Bits.IsZero && value.Function is null && value.Exception is { } token && ReferenceEquals(token.Owner, context);
            if (value.Exception is not null) return false;
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

        NirExecutionResult? Returned(Continuation? binding, ImmutableArray<NirRuntimeValue> output)
        {
            if (stack.Count == 0) return Result(NirExecutionStatus.Returned, values: output);
            var caller = stack.Peek();
            if (binding?.Call is { } call) BindReturn(caller, call, output, context.Token());
            else if (binding?.Invoke?.Normal is { } normal)
                Resume(caller, normal.Target, [.. output, .. binding.NormalCaptured, context.Token()]);
            else return Result(NirExecutionStatus.ContractViolation, "Invocation has no normal continuation");
            return null;
        }
        NirExecutionResult? UnwindFrames(NirRuntimeValue exception)
        {
            while (stack.TryPeek(out var frame))
            {
                if (!frame.Function.Outcomes.HasFlag(NirOutcomes.Unwind))
                    return Result(NirExecutionStatus.ContractViolation, "Unwind exceeds function contract: " + frame.Function.Id);
                stack.Pop();
                context.Memory.Release(frame.Allocations);
                if (frame.ReturnBinding?.Invoke is { } invoke)
                {
                    Resume(stack.Peek(), invoke.Unwind.Target, [exception, .. frame.ReturnBinding.UnwindCaptured, context.Token()]);
                    return null;
                }
            }
            return Result(NirExecutionStatus.Unwound, exception: exception);
        }
        NirExecutionResult? ExternalUnwind(Continuation? binding, NirRuntimeValue exception)
        {
            if (binding?.Invoke is { } invoke)
            {
                Resume(stack.Peek(), invoke.Unwind.Target, [exception, .. binding.UnwindCaptured, context.Token()]);
                return null;
            }
            return UnwindFrames(exception);
        }

        NirExecutionResult? Invoke(Frame caller, NirCallTarget target, ImmutableArray<NirValue> inputValues,
            Continuation? binding, bool tail, bool noReturn)
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
            if (!tail && !noReturn && binding?.Invoke is null && !possible.HasFlag(NirOutcomes.Return)) return Result(NirExecutionStatus.ContractViolation, "Ordinary call target contract excludes return");
            var propagated = NirOutcomes.Fault | NirOutcomes.Terminate | NirOutcomes.Diverge | (binding?.Invoke is null ? NirOutcomes.Unwind : 0);
            if ((possible & propagated & ~caller.Function.Outcomes) != 0)
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
            var invocation = new NirExternalInvocation(external!, input, context.Memory, context.Environment, context.CreateException);
            var output = implementation(invocation);
            if (invocation.Violation is not null) return Result(NirExecutionStatus.ContractViolation, invocation.Violation);
            if (output is null) return Result(NirExecutionStatus.ContractViolation, "External result is null");
            var actual = output.Outcome switch
            {
                NirExternalOutcome.Return => NirOutcomes.Return, NirExternalOutcome.Fault => NirOutcomes.Fault,
                NirExternalOutcome.Terminate => NirOutcomes.Terminate, NirExternalOutcome.Unwind => NirOutcomes.Unwind, _ => NirOutcomes.None
            };
            if (actual == NirOutcomes.None || !possible.HasFlag(actual)) return Result(NirExecutionStatus.ContractViolation, "External result violates declared outcomes");
            if (output.Outcome == NirExternalOutcome.Unwind)
            {
                if (output.Values.IsDefault || output.Values.Length != 0 || output.Exception is not { } exception || !ValidValue(exception, NirExceptionType.Instance))
                    return Result(NirExecutionStatus.ContractViolation, "External unwind requires one owned exception and no normal results");
                return ExternalUnwind(returnBinding, exception);
            }
            if (output.Exception is not null) return Result(NirExecutionStatus.ContractViolation, "Non-unwind result contains an exception");
            if (output.Outcome == NirExternalOutcome.Fault) return Result(NirExecutionStatus.Faulted, output.Detail ?? "ExternalFault");
            if (output.Outcome == NirExternalOutcome.Terminate) return Result(NirExecutionStatus.Terminated, output.Detail ?? "ExternalTermination");
            if (forbidReturn) return Result(NirExecutionStatus.ContractViolation, "No-return invocation returned");
            if (!ValidValues(output.Values, signature.Results)) return Result(NirExecutionStatus.ContractViolation, "External results violate declared signature");
            return Returned(returnBinding, output.Values);
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
                    case NirExceptionCreate create:
                        context.Advance("exception-create", frame.Function.Id);
                        frame.Set(create.Result, context.CreateException());
                        frame.Set(create.Flow.Output, context.Token());
                        break;
                    case NirFloat floating:
                    {
                        var specification = floating.Spec;
                        if (floating.Controls is { } controls)
                        {
                            var rounding = (int)frame.Get(controls.RoundingMode).Bits;
                            if (!Enum.IsDefined((BinaryFloatRounding)rounding)) return Result(NirExecutionStatus.ContractViolation, "InvalidFloatingRoundingMode");
                            specification = specification with
                            {
                                Rounding = (BinaryFloatRounding)rounding,
                                Rules = specification.Rules with
                                {
                                    SubnormalInput = frame.Get(controls.FlushSubnormalInput).Bits.IsZero ? BinarySubnormalInput.Preserve : BinarySubnormalInput.SignedZero,
                                    SubnormalOutput = frame.Get(controls.FlushSubnormalOutput).Bits.IsZero ? BinarySubnormalOutput.Preserve : specification.Rules.SubnormalOutput,
                                    NaN = frame.Get(controls.CanonicalNaN).Bits.IsZero ? specification.Rules.NaN : BinaryNaNRule.Canonical,
                                    ExactTinyUnderflow = controls.ExactTinyUnderflow is { } exact ? !frame.Get(exact).Bits.IsZero : specification.Rules.ExactTinyUnderflow
                                }
                            };
                        }
                        var evaluated = BinaryFloatMath.Evaluate(specification, floating.Inputs.Select(v => frame.Get(v).Bits).ToArray());
                        frame.Set(floating.Result, new(floating.Result.Type, evaluated.Bits));
                        frame.Set(floating.Exceptions, new(floating.Exceptions.Type, (uint)evaluated.Exceptions));
                        break;
                    }
                    case NirEnvironmentRead read:
                        if (!context.Environment.TryGetValue(read.Field, out var environmentValue))
                            return Result(NirExecutionStatus.MissingInput, "Environment requires an explicit value: " + read.Field);
                        if (!NirEnvironmentContract.Valid(read.Field, environmentValue))
                            return Result(NirExecutionStatus.InvalidInput, "Invalid environment value: " + read.Field);
                        context.Advance("environment-read", frame.Function.Id, read.Field.ToString());
                        frame.Set(read.Result, new(read.Result.Type, environmentValue));
                        frame.Set(read.Flow.Output, context.Token());
                        break;
                    case NirEnvironmentWrite write:
                        var replacement = frame.Get(write.Value).Bits;
                        if (!NirEnvironmentContract.Valid(write.Field, replacement))
                            return Result(NirExecutionStatus.ContractViolation, "Invalid environment write: " + write.Field);
                        context.Environment[write.Field] = replacement;
                        context.Advance("environment-write", frame.Function.Id, write.Field.ToString());
                        frame.Set(write.Flow.Output, context.Token());
                        break;
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
                        var space = ((NirAddressType)address.Type).Space;
                        var width = ((NirBitsType)load.Result.Type).Width;
                        var beatWidth = load.AtomicWidth == 0 ? width : load.AtomicWidth;
                        var raw = new byte[width / 8];
                        for (var offset = 0; offset < raw.Length; offset += beatWidth / 8)
                        {
                            var at = BitVectorMath.Wrap(address.Bits + offset, ((NirAddressType)address.Type).Width);
                            var atomicFailure = context.Memory.CheckAtomicRange(space, at, load.AtomicWidth);
                            var read = atomicFailure is null ? context.Memory.Read(space, at, beatWidth / 8) : new NirMemoryResult([], atomicFailure);
                            if (!read.Success)
                            {
                                context.Advance("read", frame.Function.Id, read.Error, new(space, at, beatWidth, load.AtomicWidth, load.MemoryOrder));
                                return Result(read.MissingInput ? NirExecutionStatus.MissingInput : NirExecutionStatus.Faulted, read.Error);
                            }
                            var beat = new BigInteger(read.Bytes.AsSpan(), isUnsigned: true, isBigEndian: load.Order == NirByteOrder.Big);
                            context.Advance("read", frame.Function.Id, memory: new(space, at, beatWidth, load.AtomicWidth, load.MemoryOrder, ReadValue: beat));
                            read.Bytes.CopyTo(raw, offset);
                        }
                        var bits = new BigInteger(raw, isUnsigned: true, isBigEndian: load.Order == NirByteOrder.Big);
                        frame.Set(load.Result, new(load.Result.Type, bits));
                        frame.Set(load.Flow.Output, context.Token());
                        break;
                    }
                    case NirStore store:
                    {
                        var address = frame.Get(store.Address);
                        var value = frame.Get(store.Value);
                        var width = ((NirBitsType)value.Type).Width;
                        var space = ((NirAddressType)address.Type).Space;
                        var beatWidth = store.AtomicWidth == 0 ? width : store.AtomicWidth;
                        var bytes = NirAtomicContract.Bytes(value.Bits, width, store.Order);
                        for (var offset = 0; offset < bytes.Length; offset += beatWidth / 8)
                        {
                            var at = BitVectorMath.Wrap(address.Bits + offset, ((NirAddressType)address.Type).Width);
                            var slice = bytes.Slice(offset, beatWidth / 8);
                            var beat = new BigInteger(slice.AsSpan(), isUnsigned: true, isBigEndian: store.Order == NirByteOrder.Big);
                            var atomicFailure = context.Memory.CheckAtomicRange(space, at, store.AtomicWidth);
                            var write = atomicFailure is null ? context.Memory.Write(space, at, slice) : new NirMemoryResult([], atomicFailure);
                            context.Advance("write", frame.Function.Id, write.Error, new(space, at, beatWidth, store.AtomicWidth, store.MemoryOrder, WrittenValue: write.Success ? beat : null));
                            if (!write.Success) return Result(NirExecutionStatus.Faulted, write.Error);
                        }
                        frame.Set(store.Flow.Output, context.Token());
                        break;
                    }
                    case NirAtomicRmw atomic:
                    {
                        var address = frame.Get(atomic.Address);
                        var space = ((NirAddressType)address.Type).Space;
                        var width = ((NirBitsType)atomic.Result.Type).Width;
                        var memory = context.Memory.Atomic(space, address.Bits, width, atomic.Order, atomic.Code, frame.Get(atomic.Value).Bits);
                        context.Advance("atomic-rmw", frame.Function.Id, memory.Error,
                            new(space, address.Bits, width, width, atomic.MemoryOrder, memory.Error is null ? memory.Previous : null, memory.Written));
                        if (memory.Error is not null) return Result(memory.MissingInput ? NirExecutionStatus.MissingInput : NirExecutionStatus.Faulted, memory.Error);
                        frame.Set(atomic.Result, new(atomic.Result.Type, memory.Previous));
                        frame.Set(atomic.Flow.Output, context.Token());
                        break;
                    }
                    case NirCompareExchange exchange:
                    {
                        var address = frame.Get(exchange.Address);
                        var space = ((NirAddressType)address.Type).Space;
                        var width = ((NirBitsType)exchange.OldValue.Type).Width;
                        var memory = context.Memory.Atomic(space, address.Bits, width, exchange.Order, NirAtomicCode.Exchange,
                            frame.Get(exchange.Replacement).Bits, frame.Get(exchange.Expected).Bits, exchange.WriteBackOnFailure);
                        context.Advance("compare-exchange", frame.Function.Id, memory.Error,
                            new(space, address.Bits, width, width, memory.Success ? exchange.SuccessOrder : exchange.FailureOrder,
                                memory.Error is null ? memory.Previous : null, memory.Written, memory.Error is null ? memory.Success : null));
                        if (memory.Error is not null) return Result(memory.MissingInput ? NirExecutionStatus.MissingInput : NirExecutionStatus.Faulted, memory.Error);
                        frame.Set(exchange.OldValue, new(exchange.OldValue.Type, memory.Previous));
                        frame.Set(exchange.Success, new(exchange.Success.Type, memory.Success ? 1 : 0));
                        frame.Set(exchange.Flow.Output, context.Token());
                        break;
                    }
                    case NirFence fence:
                        context.Advance("fence", frame.Function.Id, memory: new(null, null, 0, 0, fence.MemoryOrder));
                        frame.Set(fence.Flow.Output, context.Token());
                        break;
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
                        var result = Invoke(frame, call.Target, call.Arguments, new(call, null, [], []), false, false);
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
                    var result = Returned(frame.ReturnBinding, output);
                    if (result is not null) return result;
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
                case NirInvoke invoke:
                {
                    if (frame.Get(invoke.Effect).Bits != context.Effect) return Result(NirExecutionStatus.ContractViolation, "Stale invoke Effect");
                    var binding = new Continuation(null, invoke,
                        invoke.Normal?.Captured.Select(frame.Get).ToImmutableArray() ?? [], invoke.Unwind.Captured.Select(frame.Get).ToImmutableArray());
                    var result = Invoke(frame, invoke.Target, invoke.Arguments, binding, false, invoke.Normal is null);
                    if (result is not null) return result;
                    break;
                }
                case NirRaise raise:
                {
                    var exception = frame.Get(raise.Exception);
                    if (!ValidValue(exception, NirExceptionType.Instance) || frame.Get(raise.Effect).Bits != context.Effect)
                        return Result(NirExecutionStatus.ContractViolation, "Raise requires an owned exception and current Effect");
                    context.Advance("raise", frame.Function.Id);
                    var result = UnwindFrames(exception);
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
        Resume(frame, edge.Target, arguments);
    }
    private static void Resume(Frame frame, NirBlockId target, ImmutableArray<NirRuntimeValue> arguments)
    {
        frame.Block = frame.Blocks[target];
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
            NirPureCode.Eq => a == b && inputs[0].Function == inputs[1].Function && ReferenceEquals(inputs[0].Exception, inputs[1].Exception) ? BigInteger.One : BigInteger.Zero,
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
