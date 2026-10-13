using System.Collections.Immutable;
using Cpp2CS.Ir;

namespace Cpp2CS.Native;

public sealed record NativePureRewrite(string Rule, NativeNode Before, NativeValue? Alias, NativeNode? After);
public sealed record NativePurePassResult(ImmutableArray<NativeNode> Nodes,
    ImmutableDictionary<ValueId, NativeValue> Aliases, ImmutableArray<NativePureRewrite> Rewrites);

// 只改值表达式；调用者负责将别名同步到阶段、状态和控制流使用。
public static class NativePurePass
{
    public const string Version = "native-pure-pass/1:" + NativePureRules.Version;
    public static NativePurePassResult Run(ImmutableArray<NativeNode> nodes,
        IReadOnlyDictionary<ValueId, NativeNode>? externalDefinitions = null,
        Func<NativeNode, NativeValue, int, NativeNode>? createLowExtract = null)
    {
        var definitions = new DefinitionOverlay(externalDefinitions);
        var aliases = new Dictionary<ValueId, NativeValue>();
        var expressions = new Dictionary<Expression, NativeValue>();
        var output = ImmutableArray.CreateBuilder<NativeNode>();
        var rewrites = ImmutableArray.CreateBuilder<NativePureRewrite>();
        NativeValue Resolve(NativeValue value)
        {
            while (aliases.TryGetValue(value.Id, out var next)) value = next;
            return value;
        }
        foreach (var original in nodes)
        {
            var node = original with { Inputs = original.Inputs.Select(Resolve).ToImmutableArray() };
            var reduction = NativePureRules.TryReduce(node, definitions, createLowExtract is null ? null : LowBits);
            if (reduction?.Alias is { } alias)
            {
                alias = Resolve(alias);
                aliases.Add(node.Result!.Value.Id, alias);
                rewrites.Add(new(reduction.Rule, node, alias, null));
                definitions.Remove(node.Result.Value.Id);
                continue;
            }
            if (reduction?.Replacement is { } replacement)
            {
                rewrites.Add(new(reduction.Rule, node, null, replacement));
                node = replacement;
            }
            if (node.Result is { } result && node.Flow is null && node.Inputs.Length <= 4 && OperationSpecs.For(node.Code).Effects == OperationEffects.None)
            {
                var key = new Expression(node.Code, result.Type, node.Payload,
                    node.Inputs.Length > 0 ? node.Inputs[0] : null, node.Inputs.Length > 1 ? node.Inputs[1] : null,
                    node.Inputs.Length > 2 ? node.Inputs[2] : null, node.Inputs.Length > 3 ? node.Inputs[3] : null);
                if (expressions.TryGetValue(key, out var common))
                {
                    aliases.Add(result.Id, common);
                    rewrites.Add(new("local-common-expression", node, common, null));
                    definitions.Remove(result.Id);
                    continue;
                }
                expressions.Add(key, result);
            }
            output.Add(node);
            if (node.Result is { } definition) definitions[definition.Id] = node;

            NativeValue LowBits(NativeValue value, int width)
            {
                var extract = createLowExtract!(node, value, width);
                if (extract.Code != OpCode.Extract || extract.Result is not { } narrowed || narrowed.Type != new BitsType(width) ||
                    extract.Inputs.Length != 1 || extract.Inputs[0] != value || extract.Flow is not null ||
                    extract.Payload is not ImmediatePayload { Value.IsZero: true } || definitions.ContainsKey(narrowed.Id))
                    throw new InvalidOperationException("Low-bit materialization must define a fresh pure extract");
                output.Add(extract);
                definitions[narrowed.Id] = extract;
                return narrowed;
            }
        }
        return new(output.ToImmutable(), aliases.ToImmutableDictionary(p => p.Key, p => Resolve(p.Value)), rewrites.ToImmutable());
    }

    private sealed record Expression(OpCode Code, NativeType Type, OperationPayload Payload,
        NativeValue? A, NativeValue? B, NativeValue? C, NativeValue? D);

    private sealed class DefinitionOverlay(IReadOnlyDictionary<ValueId, NativeNode>? inherited) : IReadOnlyDictionary<ValueId, NativeNode>
    {
        private readonly Dictionary<ValueId, NativeNode?> local = [];
        public NativeNode this[ValueId key]
        {
            get => TryGetValue(key, out var value) ? value : throw new KeyNotFoundException();
            set => local[key] = value;
        }
        public void Remove(ValueId key) => local[key] = null;
        public bool TryGetValue(ValueId key, out NativeNode value)
        {
            if (local.TryGetValue(key, out var current)) { value = current!; return current is not null; }
            if (inherited is not null) return inherited.TryGetValue(key, out value!);
            value = null!;
            return false;
        }
        public bool ContainsKey(ValueId key) => TryGetValue(key, out _);
        public IEnumerable<ValueId> Keys => (inherited?.Keys ?? []).Concat(local.Keys).Distinct().Where(ContainsKey);
        public IEnumerable<NativeNode> Values => Keys.Select(key => this[key]);
        public int Count => Keys.Count();
        public IEnumerator<KeyValuePair<ValueId, NativeNode>> GetEnumerator() => Keys.Select(key => new KeyValuePair<ValueId, NativeNode>(key, this[key])).GetEnumerator();
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }
}
