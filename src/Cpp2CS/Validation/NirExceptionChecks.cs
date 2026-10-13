using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Nir;

namespace Cpp2CS.Validation;

public static class NirExceptionChecks
{
    private static readonly NirBitsType I32 = new(32);
    private static readonly NirExceptionType ExceptionType = NirExceptionType.Instance;
    private static NirValue Exception(int id) => new(new(id), ExceptionType);
    private static NirModule Module(params NirFunction[] functions) => new([.. functions], [], [], []);
    private sealed class Checks
    {
        public int Count { get; private set; }
        public void Require(bool condition, string label)
        {
            if (!condition) throw new InvalidOperationException("NIR exception check failed: " + label);
            Count++;
        }
    }
    public static int Run()
    {
        var checks = new Checks();
        Identity(checks); InvokeEdges(checks); Propagation(checks); Recursion(checks); LocalLifetime(checks);
        External(checks); Validation(checks);
        return checks.Count;
    }
    private static NirFunction Thrower(string name = "thrower", bool permitsReturn = false)
    {
        var exception = Exception(0); var effect = NirValue.Effect(1);
        return new(name, new([ExceptionType], [I32]), new(0), [new(new(0), [exception, effect], [], new NirRaise(exception, effect))])
        { Outcomes = NirOutcomes.Unwind | (permitsReturn ? NirOutcomes.Return : 0) };
    }
    private static NirFunction Catcher(string target, bool permitsReturn = true, NirOutcomes extra = NirOutcomes.None)
    {
        var exception = Exception(0); var e = NirValue.Effect(1); var normal = NirValue.Bits(2, 32); var en = NirValue.Effect(3);
        var caught = Exception(4); var eu = NirValue.Effect(5);
        var blocks = ImmutableArray.CreateBuilder<NirBlock>();
        blocks.Add(new(new(0), [exception, e], [], new NirInvoke(new NirDirectTarget(target), [exception],
            permitsReturn ? new(new(1), []) : null, new(new(2), []), e)));
        if (permitsReturn) blocks.Add(new(new(1), [normal, en], [], new NirReturn([exception], en)));
        blocks.Add(new(new(2), [caught, eu], [], new NirReturn([caught], eu)));
        return new("catcher", new([ExceptionType], [ExceptionType]), new(0), blocks.ToImmutable()) { Outcomes = NirOutcomes.Return | extra };
    }
    private static NirFunction Choice()
    {
        var condition = NirValue.Bits(0, 1); var exception = Exception(1); var value = NirValue.Bits(2, 32); var e = NirValue.Effect(3);
        var en = NirValue.Effect(4); var eu = NirValue.Effect(5);
        return new("choice", new([condition.Type, ExceptionType, I32], [I32]), new(0), [
            new(new(0), [condition, exception, value, e], [], new NirBranch(condition, new(new(1), [e]), new(new(2), [e]))),
            new(new(1), [en], [], new NirReturn([value], en)), new(new(2), [eu], [], new NirRaise(exception, eu))])
        { Outcomes = NirOutcomes.Return | NirOutcomes.Unwind };
    }
    private static NirFunction ChoiceCatcher(string target = "choice")
    {
        var condition = NirValue.Bits(0, 1); var exception = Exception(1); var value = NirValue.Bits(2, 32); var e = NirValue.Effect(3);
        var normal = NirValue.Bits(4, 32); var normalCapture = NirValue.Bits(5, 32); var en = NirValue.Effect(6); var sum = NirValue.Bits(7, 32);
        var caught = Exception(8); var unwindCapture = NirValue.Bits(9, 32); var eu = NirValue.Effect(10);
        return new("choice-catcher", new([condition.Type, ExceptionType, I32], [I32, ExceptionType]), new(0), [
            new(new(0), [condition, exception, value, e], [], new NirInvoke(new NirDirectTarget(target), [condition, exception, value], new(new(1), [value]), new(new(2), [value]), e)),
            new(new(1), [normal, normalCapture, en], [new NirPure(sum, NirPureCode.Add, [normal, normalCapture])], new NirReturn([sum, exception], en)),
            new(new(2), [caught, unwindCapture, eu], [], new NirReturn([unwindCapture, caught], eu))]) { Outcomes = NirOutcomes.Return };
    }

    private static void Identity(Checks checks)
    {
        var condition = NirValue.Bits(0, 1); var e0 = NirValue.Effect(1); var x = Exception(2); var e1 = NirValue.Effect(3);
        var y = Exception(4); var e2 = NirValue.Effect(5); var selected = Exception(6); var same = NirValue.Bits(7, 1); var different = NirValue.Bits(8, 1);
        var function = new NirFunction("identity", new([condition.Type], [ExceptionType, ExceptionType, same.Type, different.Type]), new(0),
            [new(new(0), [condition, e0], [new NirExceptionCreate(x, new(e0, e1)), new NirExceptionCreate(y, new(e1, e2)),
                new NirPure(selected, NirPureCode.Select, [condition, x, y]), new NirPure(same, NirPureCode.Eq, [selected, x]),
                new NirPure(different, NirPureCode.Eq, [x, y])], new NirReturn([x, selected, same, different], e2))]) { Outcomes = NirOutcomes.Return };
        var module = NirJson.Deserialize(NirJson.Serialize(Module(function)));
        checks.Require(NirValidator.Validate(module).IsValid, "exception creation and select validate after JSON");
        var context = new NirExecutionContext(module);
        NirRuntimeValue? previous = null;
        foreach (var bit in new[] { 0, 1, 1 })
        {
            var result = NirInterpreter.Execute(module, "identity", [NirRuntimeValue.Integer(1, bit)], context);
            checks.Require(result.Status == NirExecutionStatus.Returned && result.Values[2].Bits == bit && result.Values[3].Bits == 0, "exception Eq compares identity");
            checks.Require(result.Values[0].Exception is not null && result.Values[0].Bits == 0 && result.Values[0].Function is null, "exception has no numeric address");
            if (previous is not null) checks.Require(!ReferenceEquals(previous.Exception, result.Values[0].Exception), "each dynamic create is fresh");
            previous = result.Values[0];
        }
        var input = Exception(0); var effect = NirValue.Effect(1);
        var echo = new NirFunction("echo", new([ExceptionType], [ExceptionType]), new(0), [new(new(0), [input, effect], [], new NirReturn([input], effect))]) { Outcomes = NirOutcomes.Return };
        module = Module(echo); context = new(module);
        var token = context.CreateException();
        checks.Require(ReferenceEquals(NirInterpreter.Execute(module, "echo", [token], context).Values[0].Exception, token.Exception), "context factory exception parameter");
        checks.Require(NirInterpreter.Execute(module, "echo", [new(ExceptionType, 1)], context).Status == NirExecutionStatus.InvalidInput, "bits cannot manufacture exception");
        checks.Require(NirInterpreter.Execute(module, "echo", [new(ExceptionType, 0)], context).Status == NirExecutionStatus.InvalidInput, "missing token rejected");
        checks.Require(NirInterpreter.Execute(module, "echo", [new NirExecutionContext(module).CreateException()], context).Status == NirExecutionStatus.InvalidInput, "foreign context token rejected");
    }

    private static void InvokeEdges(Checks checks)
    {
        var module = Module(Choice(), ChoiceCatcher());
        var json = NirJson.Serialize(module);
        module = NirJson.Deserialize(json);
        checks.Require(NirValidator.Validate(module).IsValid && NirJson.Serialize(module) == json, "Invoke JSON roundtrip");
        checks.Require(NirText.Format(module).Contains("unwind=b2", StringComparison.Ordinal), "Invoke text exposes both continuations");
        foreach (var normal in new[] { 0, 1 })
        {
            var context = new NirExecutionContext(module); var token = context.CreateException();
            var result = NirInterpreter.Execute(module, "choice-catcher", [NirRuntimeValue.Integer(1, normal), token, NirRuntimeValue.Integer(32, 11)], context);
            checks.Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == (normal == 1 ? 22 : 11), "Invoke binds result prefix and captures only on chosen edge");
            checks.Require(ReferenceEquals(result.Values[1].Exception, token.Exception), "Invoke preserves exception identity");
        }
        var catcher = Catcher("thrower", false);
        module = Module(Thrower(), catcher);
        var owned = new NirExecutionContext(module); var exception = owned.CreateException();
        checks.Require(NirInterpreter.Execute(module, "catcher", [exception], owned).Status == NirExecutionStatus.Returned, "Invoke with no normal continuation catches no-return unwind");
        var entry = catcher.Blocks[0]; var invoke = (NirInvoke)entry.Terminator;
        var reference = new NirValue(new(10), new NirFunctionType(Thrower().Signature, NirOutcomes.Unwind));
        catcher = catcher with { Blocks = [entry with { Operations = [new NirFunctionConstant(reference, "thrower")], Terminator = invoke with { Target = new NirIndirectTarget(reference) } }, .. catcher.Blocks.Skip(1)] };
        module = Module(Thrower(), catcher); owned = new(module); exception = owned.CreateException();
        checks.Require(NirInterpreter.Execute(module, "catcher", [exception], owned).Status == NirExecutionStatus.Returned, "indirect Invoke validates exception outcomes");
    }

    private static void Propagation(Checks checks)
    {
        var exception = Exception(0); var e = NirValue.Effect(1); var returned = NirValue.Bits(2, 32); var done = NirValue.Effect(3);
        var forward = new NirFunction("forward", new([ExceptionType], [I32]), new(0), [new(new(0), [exception, e],
            [new NirCall(new NirDirectTarget("thrower"), [exception], [returned], new(e, done))], new NirReturn([returned], done))])
        { Outcomes = NirOutcomes.Return | NirOutcomes.Unwind };
        var module = Module(Thrower(permitsReturn: true), forward, Catcher("forward"));
        var context = new NirExecutionContext(module); var token = context.CreateException();
        var result = NirInterpreter.Execute(module, "forward", [token], context);
        checks.Require(result.Status == NirExecutionStatus.Unwound && result.Values.IsEmpty && ReferenceEquals(result.Exception!.Exception, token.Exception), "ordinary Call propagates exact exception to root");
        result = NirInterpreter.Execute(module, "catcher", [token], context);
        checks.Require(result.Status == NirExecutionStatus.Returned && ReferenceEquals(result.Values[0].Exception, token.Exception), "ordinary Call propagates to ancestor Invoke");

        foreach (var tail in new[] { false, true })
        {
            var middle = new NirFunction("middle", new([ExceptionType], [I32]), new(0), [new(new(0), [exception, e], [],
                tail ? new NirTailCall(new NirDirectTarget("thrower"), [exception], e) : new NirNoReturnCall(new NirDirectTarget("thrower"), [exception], e))])
            { Outcomes = NirOutcomes.Unwind };
            module = Module(Thrower(), middle, Catcher("middle", false)); context = new(module); token = context.CreateException();
            result = NirInterpreter.Execute(module, "catcher", [token], context);
            checks.Require(result.Status == NirExecutionStatus.Returned && ReferenceEquals(result.Values[0].Exception, token.Exception), tail ? "tail inherits ancestor handler" : "NoReturn may unwind into ancestor handler");
        }
        var choice = Choice();
        var tailChoice = new NirFunction("tail-choice", choice.Signature, new(0), [choice.Blocks[0] with
        { Operations = [], Terminator = new NirTailCall(new NirDirectTarget("choice"), choice.Blocks[0].Parameters[..^1], choice.Blocks[0].Parameters[^1]) }])
        { Outcomes = choice.Outcomes };
        module = Module(choice, tailChoice, ChoiceCatcher("tail-choice")); context = new(module); token = context.CreateException();
        foreach (var normal in new[] { 0, 1 })
        {
            result = NirInterpreter.Execute(module, "choice-catcher", [NirRuntimeValue.Integer(1, normal), token, NirRuntimeValue.Integer(32, 6)], context);
            checks.Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == (normal == 1 ? 12 : 6), "tail inherits normal and exceptional edge bindings");
        }
        var rethrow = Catcher("thrower", false) with { Id = "rethrow", Signature = new([ExceptionType], [I32]), Outcomes = NirOutcomes.Unwind };
        var handler = rethrow.Blocks[1];
        rethrow = rethrow with { Blocks = [rethrow.Blocks[0], handler with { Terminator = new NirRaise(handler.Parameters[0], handler.Parameters[^1]) }] };
        module = Module(Thrower(), rethrow, Catcher("rethrow", false)); context = new(module); token = context.CreateException();
        result = NirInterpreter.Execute(module, "catcher", [token], context);
        checks.Require(result.Status == NirExecutionStatus.Returned && ReferenceEquals(result.Values[0].Exception, token.Exception), "rethrow preserves identity and finds outer handler");
    }

    private static void Recursion(Checks checks)
    {
        var n = NirValue.Bits(0, 32); var ex = Exception(1); var e = NirValue.Effect(2); var zero = NirValue.Bits(3, 32); var isZero = NirValue.Bits(4, 1);
        var baseEffect = NirValue.Effect(5); var stepEffect = NirValue.Effect(6); var one = NirValue.Bits(7, 32); var smaller = NirValue.Bits(8, 32);
        var value = NirValue.Bits(9, 32); var done = NirValue.Effect(10);
        var recursive = new NirFunction("recursive", new([I32, ExceptionType], [I32]), new(0), [
            new(new(0), [n, ex, e], [new NirConstant(zero, 0), new NirPure(isZero, NirPureCode.Eq, [n, zero])], new NirBranch(isZero, new(new(1), [e]), new(new(2), [e]))),
            new(new(1), [baseEffect], [], new NirRaise(ex, baseEffect)),
            new(new(2), [stepEffect], [new NirConstant(one, 1), new NirPure(smaller, NirPureCode.Sub, [n, one]),
                new NirCall(new NirDirectTarget("recursive"), [smaller, ex], [value], new(stepEffect, done))], new NirReturn([value], done))])
        { Outcomes = NirOutcomes.Return | NirOutcomes.Unwind | NirOutcomes.Diverge };
        var normal = NirValue.Bits(3, 32); var en = NirValue.Effect(4); var caught = Exception(5); var eu = NirValue.Effect(6);
        var root = new NirFunction("root", new([I32, ExceptionType], [ExceptionType]), new(0), [
            new(new(0), [n, ex, e], [], new NirInvoke(new NirDirectTarget("recursive"), [n, ex], new(new(1), []), new(new(2), []), e)),
            new(new(1), [normal, en], [], new NirReturn([ex], en)), new(new(2), [caught, eu], [], new NirReturn([caught], eu))])
        { Outcomes = NirOutcomes.Return | NirOutcomes.Diverge };
        var module = Module(recursive, root);
        foreach (var depth in new[] { 0, 1, 17, 200 })
        {
            var context = new NirExecutionContext(module); var exception = context.CreateException();
            var result = NirInterpreter.Execute(module, "root", [NirRuntimeValue.Integer(32, depth), exception], context);
            checks.Require(result.Status == NirExecutionStatus.Returned && ReferenceEquals(result.Values[0].Exception, exception.Exception), "recursive stack unwinds into explicit continuation");
        }
    }

    private static void LocalLifetime(Checks checks)
    {
        var addressType = new NirAddressType("mem", 16);
        var ex = Exception(0); var e = NirValue.Effect(1); var size = NirValue.Bits(2, 16); var local = new NirValue(new(3), addressType);
        var allocated = NirValue.Effect(4); var byteValue = NirValue.Bits(5, 8); var written = NirValue.Effect(6);
        var leaf = new NirFunction("leaf", new([ExceptionType], []), new(0), [new(new(0), [ex, e], [new NirConstant(size, 1),
            new NirLocalAlloc(local, size, 1, new(e, allocated)), new NirConstant(byteValue, 0x55), new NirStore(local, byteValue, NirByteOrder.Little, new(allocated, written))],
            new NirRaise(ex, written))]) { Outcomes = NirOutcomes.Unwind | NirOutcomes.Fault };
        var caught = Exception(7); var captured = new NirValue(new(8), addressType); var handlerEffect = NirValue.Effect(9);
        var read = NirValue.Bits(10, 8); var loaded = NirValue.Effect(11); var reused = new NirValue(new(12), addressType); var done = NirValue.Effect(13); var location = NirValue.Bits(14, 16);
        var owner = new NirFunction("owner", new([ExceptionType], [read.Type, location.Type, ExceptionType]), new(0), [
            new(new(0), [ex, e], [new NirConstant(size, 1), new NirLocalAlloc(local, size, 1, new(e, allocated)), new NirConstant(byteValue, 0x42),
                new NirStore(local, byteValue, NirByteOrder.Little, new(allocated, written))], new NirInvoke(new NirDirectTarget("leaf"), [ex], null, new(new(1), [local]), written)),
            new(new(1), [caught, captured, handlerEffect], [new NirLoad(read, captured, NirByteOrder.Little, new(handlerEffect, loaded)),
                new NirLocalAlloc(reused, size, 1, new(loaded, done)), new NirPure(location, NirPureCode.AddressToBits, [reused])], new NirReturn([read, location, caught], done))])
        { Outcomes = NirOutcomes.Return | NirOutcomes.Fault };
        var module = new NirModule([leaf, owner], [], [new("mem", 16, 0x100, 2)], []);
        var context = new NirExecutionContext(module); var token = context.CreateException();
        for (var i = 0; i < 2; i++)
        {
            var result = NirInterpreter.Execute(module, "owner", [token], context);
            checks.Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == 0x42 && result.Values[1].Bits == 0x101, "callee locals release while handler frame remains alive");
            checks.Require(!context.Memory.Read("mem", 0x100, 1).Success && !context.Memory.Read("mem", 0x101, 1).Success, "normal completion releases caught frame locals");
        }
        var direct = NirInterpreter.Execute(module, "leaf", [token], context);
        checks.Require(direct.Status == NirExecutionStatus.Unwound && !context.Memory.Read("mem", 0x100, 1).Success, "uncaught unwind releases root locals");

        var address = new NirValue(new(0), addressType); var inputEffect = NirValue.Effect(1); var loadedByte = NirValue.Bits(2, 8); var loadEffect = NirValue.Effect(3);
        var reader = new NirFunction("reader", new([addressType], [loadedByte.Type]), new(0), [new(new(0), [address, inputEffect],
            [new NirLoad(loadedByte, address, NirByteOrder.Little, new(inputEffect, loadEffect))], new NirReturn([loadedByte], loadEffect))]);
        var tail = new NirFunction("tail", new([], [loadedByte.Type]), new(0), [new(new(0), [e], [new NirConstant(size, 1), new NirLocalAlloc(local, size, 1, new(e, allocated))],
            new NirTailCall(new NirDirectTarget("reader"), [local], allocated))]);
        module = new([reader, tail], [], [new("mem", 16, 0x100, 2)], []); context = new(module);
        checks.Require(NirInterpreter.Execute(module, "tail", [], context).Status == NirExecutionStatus.Faulted, "tail releases own local frame before callee access");
    }

    private static void External(Checks checks)
    {
        var catcher = Catcher("external", false, NirOutcomes.Fault);
        var module = new NirModule([catcher], [new("external", new([ExceptionType], [I32]), NirExternalEffects.WriteMemory | NirExternalEffects.Environment, NirOutcomes.Unwind)],
            [new("mem", 16, 0, 0)], [new("global", "mem", 0x100, [0], true)]);
        var context = new NirExecutionContext(module); var input = context.CreateException();
        NirRuntimeValue? raised = null;
        context.Externals.Add("external", invocation =>
        {
            checks.Require(invocation.Write("mem", 0x100, [99]).Success, "external commits memory before unwind");
            checks.Require(invocation.WriteEnvironment(NirEnvironmentField.FloatingExceptions, 7).Success, "external commits environment before unwind");
            raised = invocation.CreateException();
            return NirExternalResult.Unwound(raised);
        });
        var result = NirInterpreter.Execute(module, "catcher", [input], context);
        checks.Require(result.Status == NirExecutionStatus.Returned && ReferenceEquals(result.Values[0].Exception, raised!.Exception), "external factory exception is caught");
        checks.Require(context.Memory.Read("mem", 0x100, 1).Bytes[0] == 99 && context.Environment[NirEnvironmentField.FloatingExceptions] == 7, "unwind preserves already committed external effects");
        foreach (var malformed in new[]
        {
            new NirExternalResult(NirExternalOutcome.Unwind, []),
            new NirExternalResult(NirExternalOutcome.Unwind, [NirRuntimeValue.Integer(32, 1)], Exception: input),
            NirExternalResult.Unwound(new NirExecutionContext(module).CreateException()),
            NirExternalResult.Returned(NirRuntimeValue.Integer(32, 1))
        })
        {
            context.Externals["external"] = _ => malformed;
            checks.Require(NirInterpreter.Execute(module, "catcher", [input], context).Status == NirExecutionStatus.ContractViolation, "malformed or forbidden external outcome rejected");
        }
        var exception = Exception(0); var e = NirValue.Effect(1);
        var tail = new NirFunction("tail-external", new([ExceptionType], [I32]), new(0), [new(new(0), [exception, e], [],
            new NirTailCall(new NirDirectTarget("external"), [exception], e))]) { Outcomes = NirOutcomes.Unwind };
        module = module with { Functions = [tail, Catcher("tail-external", false)] };
        context = new(module); input = context.CreateException(); context.Externals["external"] = invocation => NirExternalResult.Unwound(invocation.Arguments[0]);
        result = NirInterpreter.Execute(module, "catcher", [input], context);
        checks.Require(result.Status == NirExecutionStatus.Returned && ReferenceEquals(result.Values[0].Exception, input.Exception), "external unwind through tail preserves handler");
        result = NirInterpreter.Execute(module, "tail-external", [input], context);
        checks.Require(result.Status == NirExecutionStatus.Unwound && ReferenceEquals(result.Exception!.Exception, input.Exception), "root external tail unwind");
    }

    private static void Validation(Checks checks)
    {
        var choice = Choice(); var catcher = ChoiceCatcher(); var entry = catcher.Blocks[0]; var invoke = (NirInvoke)entry.Terminator;
        void Bad(NirFunction bad, string label) => checks.Require(!NirValidator.Validate(Module(choice, bad)).IsValid, label);
        foreach (var changed in new[]
        {
            invoke with { Normal = invoke.Normal! with { Target = new(99) } },
            invoke with { Unwind = invoke.Unwind with { Target = new(99) } },
            invoke with { Normal = null },
            invoke with { Unwind = invoke.Unwind with { Captured = [catcher.Blocks[1].Parameters[0]] } },
            invoke with { Unwind = invoke.Unwind with { Captured = [entry.Parameters[^1]] } },
            invoke with { Effect = NirValue.Effect(99) },
            invoke with { Unwind = null! },
            invoke with { Arguments = default },
            invoke with { Normal = invoke.Normal! with { Captured = default } },
            invoke with { Target = null! }
        }) Bad(catcher with { Blocks = [entry with { Terminator = changed }, .. catcher.Blocks.Skip(1)] }, "invalid invoke structure, capture, target or outcome rejected");
        var handler = catcher.Blocks[2];
        Bad(catcher with { Blocks = [entry, catcher.Blocks[1], handler with { Terminator = new NirReturn([catcher.Blocks[1].Parameters[0], handler.Parameters[0]], handler.Parameters[^1]) }] },
            "normal result cannot be used on exceptional edge");
        var normal = catcher.Blocks[1];
        Bad(catcher with { Blocks = [entry, normal with { Terminator = new NirReturn([normal.Parameters[0], handler.Parameters[0]], normal.Parameters[^1]) }, handler] },
            "exceptional result cannot be used on normal edge");
        checks.Require(!NirValidator.Validate(Module(Thrower() with { Outcomes = NirOutcomes.Return })).IsValid, "Raise requires escaping unwind contract");
        var exception = Exception(0); var e = NirValue.Effect(1); var r = NirValue.Bits(2, 32); var done = NirValue.Effect(3);
        var call = new NirCall(new NirDirectTarget("thrower"), [exception], [r], new(e, done));
        var ordinary = new NirFunction("ordinary", new([ExceptionType], [I32]), new(0), [new(new(0), [exception, e], [call], new NirReturn([r], done))])
        { Outcomes = NirOutcomes.Return };
        checks.Require(!NirValidator.Validate(Module(Thrower(permitsReturn: true), ordinary)).IsValid, "ordinary Call cannot hide callee unwind");
        var noReturn = ordinary with { Blocks = [ordinary.Blocks[0] with { Operations = [], Terminator = new NirNoReturnCall(new NirDirectTarget("thrower"), [exception], e) }] };
        checks.Require(!NirValidator.Validate(Module(Thrower(), noReturn)).IsValid, "NoReturn cannot hide callee unwind");
        var create = new NirExceptionCreate(exception, new(e, done));
        var created = new NirFunction("create", new([], []), new(0), [new(new(0), [e], [create], new NirRaise(exception, e))]) { Outcomes = NirOutcomes.Unwind };
        checks.Require(!NirValidator.Validate(Module(created)).IsValid, "Raise cannot consume stale Effect");
        created = created with { Blocks = [created.Blocks[0] with { Operations = [create with { Flow = null! }], Terminator = new NirRaise(exception, done) }] };
        checks.Require(!NirValidator.Validate(Module(created)).IsValid, "ExceptionCreate null flow is a diagnostic");
        created = created with { Blocks = [new(new(0), [e], [new NirConstant(exception, 0)], new NirRaise(exception, e))] };
        checks.Require(!NirValidator.Validate(Module(created)).IsValid, "constant bits cannot define exception identity");

        void Structure(NirOperation? operation, NirTerminator terminator)
        {
            var candidate = catcher with { Blocks = [entry with { Operations = operation is null ? [] : [operation], Terminator = terminator }, .. catcher.Blocks.Skip(1)] };
            var diagnostics = NirValidator.Validate(Module(choice, candidate)).Diagnostics;
            checks.Require(diagnostics.Length > 0 && diagnostics.All(item => item.Code.StartsWith("structure-", StringComparison.Ordinal) ||
                item.Code is "operation-array" or "terminator-array"), "exception node invalid structure stops before SSA inspection");
        }
        Structure(new NirExceptionCreate(default, new(e, done)), invoke);
        Structure(new NirExceptionCreate(exception, null!), invoke);
        Structure(new NirExceptionCreate(exception, new(default, done)), invoke);
        Structure(new NirExceptionCreate(exception, new(e, default)), invoke);
        Structure(null, new NirRaise(default, e));
        Structure(null, new NirRaise(exception, default));
        Structure(null, invoke with { Target = null! });
        Structure(null, invoke with { Target = new NirDirectTarget(null!) });
        Structure(null, invoke with { Target = new NirIndirectTarget(default) });
        Structure(null, invoke with { Arguments = default });
        Structure(null, invoke with { Arguments = [default] });
        Structure(null, invoke with { Effect = default });
        Structure(null, invoke with { Normal = invoke.Normal! with { Captured = default } });
        Structure(null, invoke with { Normal = invoke.Normal! with { Captured = [default] } });
        Structure(null, invoke with { Unwind = null! });
        Structure(null, invoke with { Unwind = invoke.Unwind with { Captured = default } });
        Structure(null, invoke with { Unwind = invoke.Unwind with { Captured = [default] } });
    }
}
