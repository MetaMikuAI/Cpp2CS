using System.Collections.Immutable;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Validation;

// 对每个已支持候选执行共享纯值 pass；不构造或宣称全程序 CFG。
public sealed class NativeCorpusChecks
{
    private static readonly BitsType[] Types = Enumerable.Range(0, 4097).Select(width => new BitsType(width)).ToArray();
    private long candidates, changedCandidates, originalNodes, retainedNodes, effects, aliases, rewrites;
    private readonly SortedDictionary<string, long> rules = new(StringComparer.Ordinal);

    public object Summary() => new
    {
        enabled = true, passed = true, ruleVersion = NativePurePass.Version,
        checkedCandidates = candidates, changedCandidates, originalNodes, retainedNodes, retainedEffectNodes = effects,
        aliases, rewrites, rules, passesPerCandidate = 1,
        scope = "Every supported candidate with its actual constants enters the shared NativePurePass once; all retained operations and remapped exits are rechecked by MirValidator, with effect order, payload, source stage and World identities preserved. Slot reads remain explicit; this is instruction-local pure-pass validation, not full-program SSA or block-parameter elimination. Cross-block and parameter transformations are covered by separate region fixtures. Structural checking does not prove semantic equivalence."
    };

    public void Check(MirInstruction instruction)
    {
        NativeValue Bits(Value value) => new(new(value.Id), Types[value.Width]);
        var worldOffset = instruction.Operations.Length + 1;
        NativeValue World(StateToken token) => new(new(worldOffset + token.Id), WorldType.Instance);
        var nodes = ImmutableArray.CreateBuilder<NativeNode>(instruction.Operations.Length);
        for (var index = 0; index < instruction.Operations.Length; index++)
        {
            var operation = instruction.Operations[index];
            nodes.Add(new(operation.Code, operation.Result is { } result ? Bits(result) : null,
                operation.Inputs.Select(Bits).ToImmutableArray(), operation.Payload,
                operation.Flow is { } flow ? new(World(flow.Input), World(flow.Output)) : null,
                new(instruction.Origin, index)));
        }
        var original = nodes.ToImmutable();
        var normalized = NativePurePass.Run(original);
        var definitions = new Dictionary<ValueId, Value>();
        var originalDefinitions = original.Where(node => node.Result is not null).ToDictionary(node => node.Result!.Value.Id);
        NativeValue Resolve(NativeValue value)
        {
            var count = 0;
            while (normalized.Aliases.TryGetValue(value.Id, out var replacement))
            {
                if (replacement.Type != value.Type || ++count > normalized.Aliases.Count)
                    throw new InvalidDataException("Native candidate alias changes type or contains a cycle");
                value = replacement;
            }
            return value;
        }
        Value Lookup(NativeValue value)
        {
            if (!definitions.TryGetValue(value.Id, out var definition) || value.Type is not BitsType bits || bits.Width != definition.Width)
                throw new InvalidDataException("Native candidate uses an undefined or mismatched value");
            return definition;
        }
        var operations = ImmutableArray.CreateBuilder<Operation>(normalized.Nodes.Length);
        var effectIndex = 0;
        var expectedEffects = original.Where(node => OperationSpecs.For(node.Code).Effects != OperationEffects.None).ToArray();
        var lastSource = -1;
        foreach (var node in normalized.Nodes)
        {
            var source = node.Source.OperationIndex;
            if (source <= lastSource || source >= original.Length || node.Source.Origin != instruction.Origin)
                throw new InvalidDataException("Native candidate lost operation provenance or order");
            lastSource = source;
            var before = original[source];
            if (node.Result != before.Result || node.Flow != before.Flow)
                throw new InvalidDataException("Native candidate changed result or World identity");
            if (OperationSpecs.For(before.Code).Effects != OperationEffects.None)
            {
                if (effectIndex == expectedEffects.Length || expectedEffects[effectIndex++] != before ||
                    node.Code != before.Code || node.Payload != before.Payload || !node.Inputs.SequenceEqual(before.Inputs.Select(Resolve)))
                    throw new InvalidDataException("Native candidate changed an effect or its relative position");
            }
            else if (OperationSpecs.For(node.Code).Effects != OperationEffects.None)
                throw new InvalidDataException("Native candidate introduced an effect");
            var inputs = node.Inputs.Select(Lookup).ToImmutableArray();
            Value? result = null;
            if (node.Result is { Type: BitsType bits } value)
            {
                result = new(definitions.Count, bits.Width);
                definitions.Add(value.Id, result.Value);
            }
            else if (node.Result is not null)
                throw new InvalidDataException("Native candidate introduced a non-bit result");
            operations.Add(new(node.Code, result, inputs, node.Payload, instruction.Operations[source].Flow));
        }
        if (effectIndex != expectedEffects.Length) throw new InvalidDataException("Native candidate removed an effect");
        foreach (var (id, replacement) in normalized.Aliases)
        {
            if (!originalDefinitions.TryGetValue(id, out var before) || before.Result!.Value.Type != replacement.Type ||
                OperationSpecs.For(before.Code).Effects != OperationEffects.None || definitions.ContainsKey(id))
                throw new InvalidDataException("Native candidate alias has no removable pure definition");
            _ = Lookup(Resolve(replacement));
        }
        if (definitions.Count + normalized.Aliases.Count != originalDefinitions.Count)
            throw new InvalidDataException("Native candidate removed a value without recording its replacement");
        Value ExitValue(Value value) => Lookup(Resolve(Bits(value)));
        var exit = instruction.Exit switch
        {
            JumpExit jump => jump with { Destination = ExitValue(jump.Destination) },
            BranchExit branch => branch with
            {
                Predicate = ExitValue(branch.Predicate), Taken = ExitValue(branch.Taken), NotTaken = ExitValue(branch.NotTaken)
            },
            NextExit or TrapExit => instruction.Exit,
            _ => throw new InvalidDataException("Unknown candidate exit")
        };
        var checkedInstruction = instruction with
        {
            Operations = operations.ToImmutable(), Exit = exit,
            Annotations = instruction.Annotations.Select(annotation => annotation with { OperationIndex = null }).ToImmutableArray()
        };
        var errors = MirValidator.Validate(checkedInstruction);
        if (errors.Count != 0)
            throw new InvalidDataException($"Native pure candidate 0x{instruction.Origin.Address:X}: {string.Join("; ", errors)}");
        candidates++;
        if (normalized.Rewrites.Length != 0) changedCandidates++;
        originalNodes += original.Length;
        retainedNodes += normalized.Nodes.Length;
        effects += expectedEffects.Length;
        aliases += normalized.Aliases.Count;
        rewrites += normalized.Rewrites.Length;
        foreach (var rewrite in normalized.Rewrites) rules[rewrite.Rule] = rules.GetValueOrDefault(rewrite.Rule) + 1;
    }
}
