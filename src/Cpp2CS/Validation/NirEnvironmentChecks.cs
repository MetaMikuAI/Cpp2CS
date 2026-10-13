using System.Collections.Immutable;
using Cpp2CS.Nir;

namespace Cpp2CS.Validation;

public static class NirEnvironmentChecks
{
    public static int Run()
    {
        var checks = 0;
        void Check(bool passed, string reason) { CoreChecks.Require(passed, reason); checks++; }
        foreach (var field in Enum.GetValues<NirEnvironmentField>())
        {
            var width = NirEnvironmentContract.Width(field);
            var value = NirValue.Bits(0, width);
            var read = NirValue.Bits(3, width);
            var before = NirValue.Effect(1);
            var written = NirValue.Effect(2);
            var after = NirValue.Effect(4);
            var function = new NirFunction("environment", new([value.Type], [value.Type]), new(0),
                [new(new(0), [value, before],
                    [new NirEnvironmentWrite(field, value, new(before, written)),
                     new NirEnvironmentRead(read, field, new(written, after))], new NirReturn([read], after))]);
            var module = new NirModule([function], [], [], []);
            var detached = NirJson.Deserialize(NirJson.Serialize(module));
            Check(NirValidator.Validate(detached).IsValid, "environment operations preserve their field and SSA through JSON");
            for (var bits = 0; bits < 1 << width; bits++)
            {
                var context = new NirExecutionContext(detached);
                var execution = NirInterpreter.Execute(detached, "environment", [NirRuntimeValue.Integer(width, bits)], context);
                var valid = NirEnvironmentContract.Valid(field, bits);
                Check(valid ? execution.Status == NirExecutionStatus.Returned && execution.Values[0].Bits == bits && context.Environment[field] == bits
                    && execution.Events.Select(item => item.Kind).SequenceEqual(["environment-write", "environment-read"])
                    : execution.Status == NirExecutionStatus.ContractViolation && context.Environment.Count == 0,
                    "semantic environment writes reject undefined values and preserve ordered observations");
            }
            var readOnly = function with
            {
                Signature = new([], [value.Type]),
                Blocks = [new(new(0), [before], [new NirEnvironmentRead(read, field, new(before, after))], new NirReturn([read], after))]
            };
            var readModule = module with { Functions = [readOnly] };
            var missing = NirInterpreter.Execute(readModule, "environment", []);
            Check(missing.Status == NirExecutionStatus.MissingInput && missing.Effect == 0, "floating environment has no implicit default");
            var invalidContext = new NirExecutionContext(readModule);
            invalidContext.Environment[field] = -1;
            Check(NirInterpreter.Execute(readModule, "environment", [], invalidContext).Status == NirExecutionStatus.InvalidInput,
                "invalid external environment input does not fabricate a read");
            var invalid = module with { Functions = [function with
            {
                Blocks = [function.Blocks[0] with { Operations = [new NirEnvironmentWrite((NirEnvironmentField)100, value, new(before, after))] }]
            }] };
            Check(!NirValidator.Validate(invalid).IsValid, "undefined environment fields are rejected statically");
        }
        foreach (var permitted in new[] { false, true })
        {
            var before = NirValue.Effect(0);
            var after = NirValue.Effect(1);
            var result = NirValue.Bits(2, 6);
            var signature = new NirSignature([], [result.Type]);
            var function = new NirFunction("caller", signature, new(0),
                [new(new(0), [before], [new NirCall(new NirDirectTarget("external"), [], [result], new(before, after))], new NirReturn([result], after))]);
            var module = new NirModule([function], [new("external", signature,
                permitted ? NirExternalEffects.Environment : NirExternalEffects.None, NirOutcomes.Return)], [], []);
            var context = new NirExecutionContext(module);
            context.Externals["external"] = invocation =>
            {
                var written = invocation.WriteEnvironment(NirEnvironmentField.FloatingExceptions, 17);
                var read = invocation.ReadEnvironment(NirEnvironmentField.FloatingExceptions);
                return NirExternalResult.Returned(NirRuntimeValue.Integer(6, written.Success && read.Success ? read.Value : 0));
            };
            var execution = NirInterpreter.Execute(module, "caller", [], context);
            Check(permitted ? execution.Status == NirExecutionStatus.Returned && execution.Values[0].Bits == 17
                : execution.Status == NirExecutionStatus.ContractViolation && context.Environment.Count == 0,
                "external semantic environment access obeys the declared effect contract");
        }
        return checks;
    }
}
