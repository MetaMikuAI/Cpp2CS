using Cpp2CS.Ir;
using Cpp2CS.X64;
using Iced.Intel;
using System.Numerics;

namespace Cpp2CS.Validation;

public static class EffectBoundaryChecks
{
    public static int Run()
    {
        var checks = 0;
        var origin = new InstructionOrigin("fixture:guard", 0x1000, 0, new byte[4]);
        var b = new MirBuilder(Architecture.Arm64, origin, "fixture.guard");
        b.Guard(b.Eq(b.Read("x0", 64), b.Const(64, 1UL)), "fixture condition not satisfied");
        b.Write("x1", b.Const(64, 42UL));
        var guarded = MirJson.Deserialize(MirJson.Serialize(b.Finish(MirExit.Next(0x1004))));
        foreach (var input in new[] { 0, 1 })
        {
            var state = CoreChecks.CreateArmState();
            state.Slots["x0"] = input;
            state.Slots["x1"] = 7;
            var execution = MirInterpreter.Execute(guarded, state);
            CoreChecks.Require(execution.Outcome == (input == 0 ? "UnmodeledFaultStop" : "Normal"), "guard outcome");
            CoreChecks.Require(state.ReadSlot("x1") == (input == 0 ? 7 : 42), "guard stops subsequent writes");
            CoreChecks.Require(state.Accesses.Count == 0, "guard is not a memory access");
            checks += 3;
        }
        var brokenWorld = guarded.Operations.Select(op => op.Code == OpCode.Guard ? op with { WorldOut = op.WorldIn } : op).ToArray();
        CoreChecks.Require(MirValidator.Validate(guarded with { Operations = brokenWorld }).Count > 0, "guard World validation");
        CoreChecks.Require(MirValidator.Validate(guarded with { Support = SupportClass.Exact, Limitations = [] }).Count > 0, "guard cannot claim exact");
        checks += 2;

        foreach (var bytes in new[] { new byte[] { 0xCC }, new byte[] { 0x66, 0xCC }, new byte[] { 0x0F, 0x0B } })
        {
            var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes));
            decoder.IP = 0x1000;
            var instruction = decoder.Decode();
            var lifted = X64Lifter.Lift(new("fixture:trap", 0x1000, 0, bytes), instruction).Ir!;
            var ir = MirJson.Deserialize(MirJson.Serialize(lifted));
            CoreChecks.Require(ir.Support == SupportClass.ExceptionBoundaryOnly, "trap is an explicit boundary");
            var state = new MachineState();
            foreach (var slot in StateLayout.For(Architecture.X64)) state.Slots[slot.Key] = MirInterpreter.Mask(slot.Value);
            state.Memory[0x8000] = 0xA5;
            var before = new Dictionary<string, BigInteger>(state.Slots);
            var result = MirInterpreter.Execute(ir, state);
            CoreChecks.Require(result.Outcome == "Trap" && result.NextAddress is null, "trap is not fallthrough");
            CoreChecks.Require(result.Event == (bytes[^1] == 0xCC ? "x64.#BP" : "x64.#UD"), "trap event identity");
            CoreChecks.Require(result.ResumeAddress == (bytes[^1] == 0xCC ? instruction.NextIP : instruction.IP), "trap versus fault saved address");
            CoreChecks.Require(before.All(pair => state.Slots[pair.Key] == pair.Value) && state.Memory[0x8000] == 0xA5 && state.Accesses.Count == 0, "trap boundary does not simulate a handler");
            CoreChecks.Require(MirValidator.Validate(ir with { Exit = ir.Exit with { ResumeAddress = null } }).Count > 0, "trap address required");
            CoreChecks.Require(MirValidator.Validate(ir with { Support = SupportClass.Exact, Limitations = [] }).Count > 0, "trap boundary cannot claim full semantics");
            checks += 7;
        }

        var f = new MirBuilder(Architecture.Arm64, origin, "fixture.float-contract");
        var a = f.Const(32, 0UL);
        f.Float(new(FloatKind.Add, 32, 32), a, a, a);
        var valid = f.Finish(MirExit.Next(0x1004));
        CoreChecks.Require(MirValidator.Validate(valid).Count == 0, "typed float operation");
        foreach (var spec in new[] { new FloatOperation((FloatKind)999, 32, 32), new(FloatKind.Add, 16, 32),
            new(FloatKind.Add, 32, 64), new(FloatKind.Compare, 32, 32), new(FloatKind.Add, 32, 32, (FloatRounding)999) })
        {
            var operations = valid.Operations.Select(op => op.Code == OpCode.Float ? op with { Floating = spec } : op).ToArray();
            CoreChecks.Require(MirValidator.Validate(valid with { Operations = operations }).Count > 0, "reject malformed float specification");
            checks++;
        }
        var stray = valid.Operations.Select(op => op.Code == OpCode.Constant ? op with { Floating = new(FloatKind.Add, 32, 32) } : op).ToArray();
        CoreChecks.Require(MirValidator.Validate(valid with { Operations = stray }).Count > 0, "float metadata only on Float");
        return checks + 2;
    }
}
