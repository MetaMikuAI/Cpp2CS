using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<Storage, ManagedValue> indirectRoots = new();
        private LocalValue? ownReturnBuffer;
        private bool IndirectStruct(AbiValue value) => value.Passing == Passing.Indirect && (types.Kind(value.Type) == TypeKind.Struct || ManagedAbi.SharedValue(value.Type));

        [ParameterBinding(20)]
        private bool PrepareIndirectArgument(AbiValue parameter, int index)
        {
            if (!IndirectStruct(parameter)) return false;
            var register = parameter.Pieces.Single().Register;
            var root = new AddressValue(new ArgumentValue(index, parameter.Type, 0));
            indirectRoots.Add(register, root);
            arguments[register] = new(index, root.Type, 64);
            return true;
        }

        private void PrepareReturnBuffer(AbiValue? value)
        {
            if (value is null || !IndirectStruct(value)) return;
            ownReturnBuffer = StructLocal(value.Type, 0);
            var root = new AddressValue(ownReturnBuffer);
            var register = value.Pieces.Single().Register;
            indirectRoots.Add(register, root);
            arguments[register] = new(-2, root.Type, 64);
        }

        [ArgumentRule(20)]
        private ManagedValue? IndirectStructArgument(AbiValue parameter, ArgumentSite site) => !IndirectStruct(parameter) ? null
            : new IndirectValue(StructAddress(site.Argument(new AbiValue(new ByRefRef(parameter.Type), Passing.Registers, parameter.Pieces), site.Name), parameter.Type), parameter.Type);

        [InvocationOutputRule(10)]
        private bool IndirectInvocation(Call call, AbiSignature signature, Dictionary<Storage, Expr> registers,
            ManagedInvocation invocation, List<ManagedStatement> output)
        {
            if (signature.Return is not { } returned || !IndirectStruct(returned)) return false;
            if (!registers.TryGetValue(returned.Pieces.Single().Register, out var expression)) throw Fail(call.Address, "调用 缺少返回缓冲区");
            var address = StructAddress(expression, returned.Type);
            var result = CallStructLocal(call, returned.Type);
            output.Add(new ManagedCall(call.Address, invocation, result, false));
            output.Add(new ManagedStore(call.Address, new IndirectValue(address, returned.Type), result));
            if (call.Kind is CallKind.Tail or CallKind.TailIndirect)
            {
                if (ownReturnBuffer is null || !address.Equals(new AddressValue(ownReturnBuffer)) || !returned.Type.Equals(returnType))
                    throw Fail(call.Address, "尾调用缓冲区不是本方法返回根");
                output.Add(new ManagedReturn(call.Address, ownReturnBuffer));
            }
            return true;
        }

        /// <summary>返回缓冲区没有隐含默认值。按 CFG 前驱交集证明每条正常返回路径都定义了全部叶子。</summary>
        [BodyProof(10)]
        private void ProveReturnBuffer(ManagedBody body)
        {
            if (ownReturnBuffer is null) return;
            var address = new AddressValue(ownReturnBuffer);
            var leaves = StructPaths(ownReturnBuffer.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null))
                .Select(p => PathValue(address, p.Path)).ToHashSet();
            if (ManagedAbi.SharedValue(ownReturnBuffer.Type)) leaves.Add(ownReturnBuffer);
            var blocksByAddress = body.Blocks.ToDictionary(b => b.Address);
            IEnumerable<ulong> Successors(ManagedBlock block) => block.Statements.LastOrDefault() is { } last ? ManagedValues.Edges(last).Select(e => e.Target) : [];
            var predecessors = body.Blocks.SelectMany(b => Successors(b).Select(s => (From: b.Address, To: s)))
                .ToLookup(e => e.To, e => e.From);
            var outputs = body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<ManagedValue>(leaves));
            HashSet<ManagedValue> Input(ManagedBlock block)
            {
                if (block == body.Blocks[0]) return [];
                var sources = predecessors[block.Address].Where(blocksByAddress.ContainsKey).ToArray();
                if (sources.Length == 0) return [];
                var state = new HashSet<ManagedValue>(outputs[sources[0]]);
                foreach (var source in sources.Skip(1)) state.IntersectWith(outputs[source]);
                return state;
            }
            void Apply(HashSet<ManagedValue> state, ManagedStatement statement)
            {
                if (statement is ManagedAssignment assignment && assignment.Target.Equals(ownReturnBuffer)) state.UnionWith(leaves);
                if (statement is ManagedCall { Result: { } result } && result.Equals(ownReturnBuffer)) state.UnionWith(leaves);
                if (statement is ManagedStore store)
                {
                    if (leaves.Contains(store.Target)) state.Add(store.Target);
                    if (store.Target is IndirectValue i && i.Address.Equals(address)) state.UnionWith(leaves);
                }
            }
            bool changed;
            do
            {
                changed = false;
                foreach (var block in body.Blocks)
                {
                    var state = Input(block);
                    foreach (var statement in block.Statements) Apply(state, statement);
                    if (!outputs[block.Address].SetEquals(state)) { outputs[block.Address] = state; changed = true; }
                }
            } while (changed);
            foreach (var block in body.Blocks)
            {
                var state = Input(block);
                foreach (var statement in block.Statements)
                {
                    Apply(state, statement);
                    if (statement is ManagedReturn && !state.IsSupersetOf(leaves))
                        Hole(statement.Address, $"返回缓冲区仍有 {leaves.Count - state.Count} 个叶子未在所有路径定义");
                }
            }
        }
    }
}
