using Cpp2CS.Ir;
using System.Collections.Immutable;
using System.Numerics;

namespace Cpp2CS.Validation;

public static class CoreChecks
{
    private static readonly InstructionOrigin Fixture = new("fixture:core", 0x1000, 0, new byte[4]);

    public static int Run()
    {
        var regionChecks = RegionChecks.Run();
        var ssaChecks = StateSsaChecks.Run();
        var normalizationChecks = NativePureRuleChecks.Run() + NativeParameterChecks.Run() + NativeNormalizationChecks.Run();
        var nativeChecks = NativeExecutionChecks.Run() + NativeEdgeExecutionChecks.Run();
        var nirCoreChecks = NirCoreChecks.Run();
        var recoveryGraphChecks = RecoveryGraphChecks.Run();
        var nirRecoveryChecks = NirRecoveryChecks.Run();
        var nirInterfaceChecks = NirInterfaceChecks.Run();
        var nirNumericChecks = NirNumericChecks.Run();
        var nirFloatingRecoveryChecks = NirFloatingRecoveryChecks.Run();
        var nirAtomicChecks = NirAtomicChecks.Run() + NirAtomicRecoveryChecks.Run();
        var nirEnvironmentChecks = NirEnvironmentChecks.Run();
        var nirCorpusChecks = NirCorpusChecks.RunSelfChecks();
        var nirInputChecks = NirInputChecks.Run();
        var nirTailRecoveryChecks = NirTailRecoveryChecks.Run();
        var nirExceptionChecks = NirExceptionChecks.Run();
        var checks = Images.ImageSelfTests.Run() + DivisionChecks.Run() + FloatChecks.Run() + EffectBoundaryChecks.Run() + MemoryEffectChecks.Run() + AtomicMemoryChecks.Run()
            + ExecutionContractChecks.Run() + MirStructureChecks.Run() + MirInspectionChecks.Run()
            + regionChecks + ssaChecks + nativeChecks + normalizationChecks + nirCoreChecks + recoveryGraphChecks + nirRecoveryChecks + nirInterfaceChecks + nirNumericChecks
            + nirAtomicChecks + nirEnvironmentChecks + nirCorpusChecks + nirFloatingRecoveryChecks + nirInputChecks + nirTailRecoveryChecks + nirExceptionChecks;
        Console.WriteLine($"native core checks passed: region={regionChecks}, ssa={ssaChecks}, execution={nativeChecks}, normalization={normalizationChecks}");
        Console.WriteLine($"NIR checks passed: core={nirCoreChecks}, graph={recoveryGraphChecks}, recovery={nirRecoveryChecks}, interfaces={nirInterfaceChecks}, numeric={nirNumericChecks}");
        Console.WriteLine($"NIR extended checks passed: atomic={nirAtomicChecks}, floating-recovery={nirFloatingRecoveryChecks}, environment={nirEnvironmentChecks}, corpus={nirCorpusChecks}, input={nirInputChecks}, tail-recovery={nirTailRecoveryChecks}, exception={nirExceptionChecks}");
        var originalBytes = Convert.FromHexString("1F2003D5");
        var immutableOrigin = new InstructionOrigin("fixture:immutable", 0x1000, 0, originalBytes);
        originalBytes[0] = 0;
        Require(immutableOrigin.Bytes.Span[0] == 0x1F, "origin snapshot");
        var minimal = new MirBuilder(Architecture.Arm64, immutableOrigin, "fixture.structure").Finish(MirExit.Next(0x1004));
        Require(MirValidator.Validate(minimal with { ProfileId = "unknown-profile" }).Count > 0, "reject unknown profile");
        Require(MirValidator.Validate(minimal with { Exit = MirExit.Trap(ExceptionKind.X64Breakpoint, "fixture", 0x1000) }).Count > 0, "reject trap from another architecture");
        Require(MirValidator.Validate(minimal with { Origin = new("fixture:unaligned", 0x1001, 0, originalBytes) }).Count > 0, "reject ARM alignment");
        checks += 4;
        foreach (var subtract in new[] { false, true })
        {
            var b = new MirBuilder(Architecture.Arm64, Fixture, "fixture.arithmetic8");
            var a = b.Trunc(b.Read("x0", 64), 8);
            var operand = b.Trunc(b.Read("x1", 64), 8);
            var carry = b.Read("c", 1);
            var result = Arithmetic.AddWithCarry(b, a, subtract ? b.Not(operand) : operand, carry);
            b.Write("x2", b.Zext(result.Result, 64));
            b.Write("c", result.Carry);
            b.Write("v", result.Overflow);
            var ir = b.Finish(MirExit.Next(0x1004));
            Require(MirValidator.Validate(ir).Count == 0, "arithmetic fixture validation");
            Require(MirJson.Serialize(MirJson.Deserialize(MirJson.Serialize(ir))) == MirJson.Serialize(ir), "MIR roundtrip");
            var state = CreateArmState();
            for (var x = 0; x < 256; x++)
            for (var y = 0; y < 256; y++)
            for (var c = 0; c < 2; c++)
            {
                state.Slots["x0"] = x;
                state.Slots["x1"] = y;
                state.Slots["c"] = c;
                MirInterpreter.Execute(ir, state);
                var integer = subtract ? x - y - (1 - c) : x + y + c;
                var sx = x < 128 ? x : x - 256;
                var sy = y < 128 ? y : y - 256;
                var signed = subtract ? sx - sy - (1 - c) : sx + sy + c;
                Require(state.ReadSlot("x2") == (integer & 255), "8-bit result");
                Require(state.ReadSlot("c") == (subtract ? integer >= 0 ? 1 : 0 : integer > 255 ? 1 : 0), "8-bit carry/no-borrow");
                Require(state.ReadSlot("v") == (signed is < -128 or > 127 ? 1 : 0), "8-bit signed overflow");
                checks++;
            }
        }
        var invalid = new MirBuilder(Architecture.Arm64, Fixture, "fixture.invalid");
        invalid.Write("x0", invalid.Const(32, 1UL));
        Require(MirValidator.Validate(invalid.Finish(MirExit.Next(0))).Count != 0, "reject alias width mismatch");
        checks++;
        var memory = new MirBuilder(Architecture.Arm64, Fixture, "fixture.memory");
        var address = memory.Const(64, 0x2000UL);
        memory.Write("x0", memory.Load(address, 64));
        memory.Store(address, memory.Const(64, 42UL));
        var memoryIr = memory.Finish(MirExit.Next(0));
        Require(memoryIr.Support == SupportClass.NormalPathOnly, "fault boundary");
        Require(MirValidator.Validate(memoryIr).Count == 0, "memory validation");
        var faultState = CreateArmState();
        faultState.Slots["x0"] = 99;
        Require(MirInterpreter.Execute(memoryIr, faultState).Outcome == "UnmodeledFaultStop" && faultState.ReadSlot("x0") == 99, "no fabricated load result");
        var broken = memoryIr with { Operations = memoryIr.Operations.Select(op => op.Code == OpCode.Store ? op with { Flow = new(new(0), op.Flow!.Output) } : op).ToImmutableArray() };
        Require(MirValidator.Validate(broken).Count != 0, "reject broken World chain");
        checks += 4;
        for (var count = 0; count <= 80; count++)
        {
            var b = new MirBuilder(Architecture.Arm64, Fixture, "fixture.totalshift");
            b.Write("x0", b.Shl(b.Const(64, 1UL), b.Const(8, (ulong)count)));
            var state = CreateArmState();
            MirInterpreter.Execute(b.Finish(MirExit.Next(0)), state);
            Require(state.ReadSlot("x0") == (count >= 64 ? 0 : BigInteger.One << count), "total shift");
            checks++;
        }
        foreach (var initial in new[] { 1, 2 })
        {
            var state = CreateArmState(0x55D979C);
            state.Slots["x9"] = initial;
            state.Slots["x10"] = 8;
            var code = Convert.FromHexString("290500F14A41009161FFFF54");
            ExecutionResult? result = null;
            for (var offset = 0; offset < code.Length; offset += 4)
            {
                var lifted = Arm64.Arm64Lifter.Lift(new("fixture:flag-chain", 0x55D979CUL + (ulong)offset, offset, code.AsMemory(offset, 4)));
                Require(lifted.Ir is not null, "flag-chain lift");
                Require(MirValidator.Validate(lifted.Ir!).Count == 0, "flag-chain validate");
                result = MirInterpreter.Execute(lifted.Ir!, state);
            }
            Require(state.ReadSlot("x10") == 24, "ADD result");
            Require(result!.NextAddress == (initial == 1 ? 0x55D97A8UL : 0x55D9790UL), "B.NE reads SUBS flags across ADD");
            checks++;
        }
        Console.WriteLine($"core checks passed: {checks}");
        return 0;
    }

    public static MachineState CreateArmState(ulong address = 0x1000)
    {
        var state = new MachineState();
        state.Slots["btype"] = 0;
        state.CodeGuardedPages[address >> 12] = false;
        return state;
    }

    public static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
