using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Validation;

public static class NirTailRecoveryChecks
{
    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        {
            var arm = architecture == Architecture.Arm64;
            var caller = NirRecoveryChecks.Contract(architecture, "tail_owner", 0x1000, 2);
            var callee = NirRecoveryChecks.Contract(architecture, "tail_target", 0x1100, 2);
            var source = Tail(architecture);
            source.Add(0x1100, arm ? ["0000018B", "C0035FD6"] : ["488D0411", "C3"]);

            var conservative = FunctionGraphBuilder.Build(source, caller, [caller, callee]);
            Check(conservative.Gaps.Any(gap => gap.Kind == RecoveryGapKind.UnclassifiedTailCall),
                "graph discovery alone does not adopt an automatic tail relation by default");
            var candidate = FunctionGraphBuilder.Build(source, caller, [caller, callee], new(InferTailCallCandidates: true));
            Check(candidate.IsClosed && candidate.Entry.Edges.Single().IsTailCandidate &&
                candidate.Entry.Edges.Single().Kind == DerivedEdgeKind.TailCall,
                "direct compatible transfer is a candidate awaiting frame and argument proof");
            var noEvidence = candidate with { Dependencies = candidate.Dependencies.Where(dependency =>
                !dependency.StartsWith("tail-call-candidate:", StringComparison.Ordinal)).ToImmutableArray() };
            Check(DerivedGraphValidator.Validate(noEvidence).Count != 0,
                "automatic candidate requires its exact source and target dependency");
            var forged = candidate with { Blocks = candidate.Blocks.Select(block => block with
                { Edges = block.Edges.Select(edge => edge with { IsTailCandidate = false }).ToImmutableArray() }).ToImmutableArray() };
            Check(DerivedGraphValidator.Validate(forged).Count != 0,
                "a candidate cannot masquerade as an adopted tail relation");

            var recovered = NirRecoveryChecks.Recover(source, [caller, callee]);
            Check(recovered.Complete, "automatic tail fixture: " + NirRecoveryChecks.Explain(recovered));
            var owner = recovered.Functions.Single(function => function.Graph.Contract.Name == caller.Name);
            Check(owner.Function!.Blocks.Any(block => block.Terminator is NirTailCall) &&
                owner.Evidence.Any(evidence => evidence.Rule == "tail.return-protocol"),
                "only a proved frame transfer emits an architecture-free tail call");
            foreach (var values in new[] { new BigInteger[] { 0, 0 }, [7, 11], [ulong.MaxValue, 1] })
                checks += NirRecoveryChecks.Compare(source, recovered.Module, caller.Name, caller.EntryAddress,
                    values, (values[0] + values[1]) & MirInterpreter.Mask(64));

            var restored = Tail(architecture, arm
                ? ["FF4300D1", "F30300F9", "F30300AA", "F30340F9", "FF430091"]
                : ["53", "4889CB", "5B"]);
            restored.Add(0x1100, arm ? ["0000018B", "C0035FD6"] : ["488D0411", "C3"]);
            var restoredResult = NirRecoveryChecks.Recover(restored, [caller, callee]);
            Check(restoredResult.Complete, "restored nonvolatile tail: " + NirRecoveryChecks.Explain(restoredResult));
            checks += NirRecoveryChecks.Compare(restored, restoredResult.Module, caller.Name, caller.EntryAddress, [7, 11], 18);

            Reject(Tail(architecture, arm ? ["FF4300D1"] : ["4883EC10"]), caller, callee,
                "tail.proof-return-stack", "automatic tail does not adopt a displaced stack");
            Reject(Tail(architecture, arm ? ["1E0080D2"] : ["48C7042400000000"]), caller, callee,
                "tail.proof-tail-return-address", "caller return address must survive tail transfer");
            Reject(Tail(architecture, arm ? ["130080D2"] : ["31DB"]), caller, callee,
                "tail.proof-return-preserved", "automatic tail does not adopt a nonvolatile clobber");
            Reject(Tail(architecture), caller with { Signature = caller.Signature with { Arguments = [new(64)] } }, callee,
                "tail.arguments", "unbound register inputs cannot become invented logical arguments");
            Reject(Tail(architecture), caller, callee with { Signature = callee.Signature with { Result = new(32) } },
                "graph.UnsupportedInterface", "tail result interface must match exactly");
            Reject(Tail(architecture), caller, callee with { Abi = arm ? MachineAbiKind.WindowsX64 : MachineAbiKind.Aapcs64 },
                "graph.UnsupportedInterface", "tail transfer cannot silently adapt a different ABI");

            var arity = arm ? 9 : 5;
            var stackCaller = NirRecoveryChecks.Contract(architecture, "tail_owner", 0x1000, arity);
            var stackCallee = NirRecoveryChecks.Contract(architecture, "tail_target", 0x1100, arity);
            var stacked = Tail(architecture);
            stacked.Add(0x1100, arm ? ["E90340F9", "0000098B", "C0035FD6"] : ["488B442428", "4801C8", "C3"]);
            var stackResult = NirRecoveryChecks.Recover(stacked, [stackCaller, stackCallee]);
            Check(stackResult.Complete, "incoming stack tail argument: " + NirRecoveryChecks.Explain(stackResult));
            var stackValues = Enumerable.Range(1, arity).Select(value => new BigInteger(value)).ToArray();
            checks += NirRecoveryChecks.Compare(stacked, stackResult.Module, caller.Name, caller.EntryAddress, stackValues, arity + 1);
            Reject(Tail(architecture, arm ? ["E00300F9"] : ["48894C2428"]),
                stackCaller with { Signature = stackCaller.Signature with { Arguments = stackCaller.Signature.Arguments.RemoveAt(arity - 1) } },
                stackCallee, "tail.stack-capacity", "initialized outgoing bytes do not prove caller-owned argument capacity");

            var pointerCallee = callee with { Signature = callee.Signature with { Arguments = [new(64, RecoveryScalarKind.Address)] } };
            Reject(Tail(architecture, arm ? ["E0030091"] : ["488D4C24F0"]), caller, pointerCallee,
                "frame.escape-call", "tail call cannot retain a pointer into the destroyed machine frame");
            Reject(Tail(architecture, arm
                ? ["FF4300D1", "E9030091", "E90300F9", "E00340F9", "FF430091"]
                : ["4883EC10", "4889E0", "48890424", "488B0C24", "4883C410"]), caller, pointerCallee,
                "frame.escape-call", "spilling and reloading a frame pointer cannot hide its tail-call escape");
            var terminalCaller = caller with { Signature = caller.Signature with { Result = null },
                Effects = caller.Effects with { MayReturn = false, MayTerminate = true } };
            var terminalCallee = pointerCallee with { Signature = pointerCallee.Signature with { Result = null },
                Effects = pointerCallee.Effects with { MayReturn = false, MayTerminate = true } };
            Reject(Tail(architecture, arm ? ["E0030091"] : ["488D4C24F0"]), terminalCaller, terminalCallee,
                "frame.escape-call", "nonreturning tail still proves frame lifetime before discarding the frame");

            var conditional = new NirRecoveryChecks.FixtureSource(architecture, "fixture:conditional-tail");
            conditional.Add(0x1000, arm ? ["00080054", "C0035FD6"] : ["0F84FA000000", "C3"]);
            var conditionalGraph = FunctionGraphBuilder.Build(conditional, caller, [callee], new(InferTailCallCandidates: true));
            Check(conditionalGraph.Gaps.Any(gap => gap.Kind == RecoveryGapKind.UnclassifiedTailCall) &&
                conditionalGraph.Blocks.SelectMany(block => block.Edges).All(edge => !edge.IsTailCandidate),
                "conditional branches into known entries do not acquire unconditional tail semantics");
            var indirect = new NirRecoveryChecks.FixtureSource(architecture, "fixture:indirect-tail");
            indirect.Add(0x1000, arm ? "00001FD6" : "FFE0");
            var indirectGraph = FunctionGraphBuilder.Build(indirect, caller, [callee], new(InferTailCallCandidates: true));
            Check(indirectGraph.Gaps.Single().Kind == RecoveryGapKind.UnknownJumpTarget,
                "unresolved indirect transfer does not borrow a known function contract");
            var self = new NirRecoveryChecks.FixtureSource(architecture, "fixture:self-loop");
            self.Add(0x1000, Jump(architecture, 0x1000, 0x1000));
            var selfGraph = FunctionGraphBuilder.Build(self, caller, [caller], new(InferTailCallCandidates: true));
            Check(selfGraph.IsClosed && selfGraph.Entry.Edges.Single().Kind == DerivedEdgeKind.Direct,
                "a self-entry loop remains a machine CFG edge");
            var missing = Tail(architecture);
            var missingGraph = FunctionGraphBuilder.Build(missing, caller, [caller], new(InferTailCallCandidates: true));
            Check(missingGraph.Gaps.Any(gap => gap.Kind == RecoveryGapKind.Decode) &&
                missingGraph.Blocks.SelectMany(block => block.Edges).All(edge => !edge.IsTailCandidate),
                "unmapped target without a known contract is a discovery gap");

            var throwingCaller = caller with { Effects = caller.Effects with { MayThrow = true } };
            var throwingCallee = callee with { Effects = callee.Effects with { MayThrow = true } };
            var throwing = RecoverOne(Tail(architecture), throwingCaller, throwingCallee);
            Check(throwing.Complete && throwing.Module.Functions.Single().Outcomes.HasFlag(NirOutcomes.Unwind) &&
                throwing.Module.Externals.Single().Outcomes.HasFlag(NirOutcomes.Unwind),
                "proved tail keeps the callee language-exception outcome in both contracts");
            var context = new NirExecutionContext(throwing.Module);
            var exception = context.CreateException();
            context.Externals[callee.Name] = invocation =>
            {
                Check(invocation.Arguments[0].Bits == 7 && invocation.Arguments[1].Bits == 11,
                    "unwinding tail receives restored logical arguments");
                return NirExternalResult.Unwound(exception);
            };
            var unwound = NirInterpreter.Execute(throwing.Module, caller.Name,
                [NirRuntimeValue.Integer(64, 7), NirRuntimeValue.Integer(64, 11)], context);
            Check(unwound.Status == NirExecutionStatus.Unwound && unwound.Exception?.Exception == exception.Exception,
                "tail propagates the same opaque exception instead of faulting or fabricating a return");
            var forbiddenUnwind = RecoverOne(Tail(architecture), caller, throwingCallee);
            Check(!forbiddenUnwind.Complete && forbiddenUnwind.Gaps.Any(gap => gap.Code == "contract.call-unwind"),
                "proved throwing tail contradicts a no-throw owner contract");
            var noReturnOwner = throwingCaller with { Signature = throwingCaller.Signature with { Result = null },
                Effects = throwingCaller.Effects with { MayReturn = false, MayTerminate = true } };
            var noReturnTarget = throwingCallee with { Signature = throwingCallee.Signature with { Result = null },
                Effects = throwingCallee.Effects with { MayReturn = false, MayTerminate = true } };
            var noReturnTail = RecoverOne(Tail(architecture), noReturnOwner, noReturnTarget);
            Check(noReturnTail.Complete && noReturnTail.Module.Functions.Single().Blocks.Any(block => block.Terminator is NirTailCall),
                "proved nonreturning transfer remains a tail call with an explicit unwind outcome");

            var ordinary = NirRecoveryChecks.Caller(architecture);
            var ordinaryOwner = caller with { Name = "ordinary_owner", Effects = caller.Effects with { MayThrow = true } };
            var ordinaryResult = RecoverOne(ordinary, ordinaryOwner, throwingCallee);
            Check(!ordinaryResult.Complete && ordinaryResult.Gaps.Any(gap => gap.Code == "call.unwind"),
                "a regular potentially-throwing call still needs source local exception evidence");
        }
        return checks;

        void Reject(NirRecoveryChecks.FixtureSource source, FunctionContract caller, FunctionContract callee,
            string code, string reason)
        {
            var result = RecoverOne(source, caller, callee);
            Check(!result.Complete && result.Gaps.Any(gap => gap.Code == code), reason + ": " + NirRecoveryChecks.Explain(result));
            if (code.StartsWith("tail.proof-", StringComparison.Ordinal) || code == "tail.arguments")
                Check(result.Gaps.All(gap => !gap.Code.StartsWith("contract.", StringComparison.Ordinal)),
                    "failed automatic candidate proof does not withdraw an otherwise unrefuted function contract");
        }
    }

    private static NirRecoveryResult RecoverOne(NirRecoveryChecks.FixtureSource source, FunctionContract caller, FunctionContract callee)
    {
        var result = NirRecovery.RecoverOne(source, caller, new([caller, callee]));
        var json = NirJson.Serialize(result.Module);
        var detached = NirJson.Deserialize(json);
        CoreChecks.Require(NirValidator.Validate(detached).IsValid && NirJson.Serialize(detached) == json,
            "tail recovery roundtrip retains a valid standalone NIR module");
        return result with { Module = detached };
    }

    private static NirRecoveryChecks.FixtureSource Tail(Architecture architecture, params string[] prefix)
    {
        var source = new NirRecoveryChecks.FixtureSource(architecture, "fixture:automatic-tail");
        source.Add(0x1000, prefix);
        var site = 0x1000UL + (ulong)prefix.Sum(hex => hex.Length / 2);
        source.Add(site, Jump(architecture, site, 0x1100));
        return source;
    }

    private static string Jump(Architecture architecture, ulong site, ulong target)
    {
        if (architecture == Architecture.Arm64)
        {
            var arm = new byte[4];
            BinaryPrimitives.WriteUInt32LittleEndian(arm, 0x14000000U | ((uint)((long)target - (long)site) >> 2 & 0x03FFFFFF));
            return Convert.ToHexString(arm);
        }
        var x64 = new byte[5];
        x64[0] = 0xE9;
        BinaryPrimitives.WriteInt32LittleEndian(x64.AsSpan(1), checked((int)((long)target - (long)site - 5)));
        return Convert.ToHexString(x64);
    }
}
