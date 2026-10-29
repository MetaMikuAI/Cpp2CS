using Cpp2CS.Recovery.Analysis;
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

        // 尾部 memcpy 完整写入本方法返回根时，保留有类型的结构体读取与复制。
        [CallRule(21)]
        private RecoveryResult<bool> CopyStructReturn(Call call, List<ManagedStatement> output)
        {
            if (call is not { Kind: CallKind.Tail, Op: { Kind: OpKind.Import, Operand: "memcpy" },
                    Arguments: [var destination, var source, Const count] }
                || ownReturnBuffer is null || types.Kind(returnType) != TypeKind.Struct
                || types.Size(returnType) <= 0 || count.Value != (ulong)types.Size(returnType)) return false;
            if (!StructAddress(destination, returnType).TryGet(out var target, out var failure)) return failure;
            if (!target.Equals(new AddressValue(ownReturnBuffer))) return false;
            if (!StructAddress(source, returnType).TryGet(out var address, out failure)) return failure;
            if (ManagedValues.Walk(address).Contains(ownReturnBuffer)) return false;
            output.Add(new ManagedAssignment(call.Address, ownReturnBuffer, new IndirectValue(address, returnType)));
            output.Add(new ManagedReturn(call.Address, ownReturnBuffer));
            return true;
        }

        [ArgumentRule(20)]
        private RecoveryResult<ManagedValue?> IndirectStructArgument(AbiValue parameter, ArgumentSite site) => !IndirectStruct(parameter) ? (ManagedValue?)null
            : site.Argument(new AbiValue(new ByRefRef(parameter.Type), Passing.Registers, parameter.Pieces), site.Name)
                .Bind(expression => StructAddress(expression, parameter.Type)).Map<ManagedValue?>(address => new IndirectValue(address, parameter.Type));

        [InvocationOutputRule(10)]
        private RecoveryResult<bool> IndirectInvocation(Call call, AbiSignature signature, Dictionary<Storage, Expr> registers,
            ManagedInvocation invocation, List<ManagedStatement> output)
        {
            if (signature.Return is not { } returned || !IndirectStruct(returned)) return false;
            if (!registers.TryGetValue(returned.Pieces.Single().Register, out var expression)) return Fail(call.Address, "调用 缺少返回缓冲区");
            if (!StructAddress(expression, returned.Type).TryGet(out var address, out var failure)) return failure;
            var result = CallStructLocal(call, returned.Type);
            output.Add(new ManagedCall(call.Address, invocation, result, false));
            output.Add(new ManagedStore(call.Address, new IndirectValue(address, returned.Type), result));
            if (call.Kind is CallKind.Tail or CallKind.TailIndirect)
            {
                if (ownReturnBuffer is null || !address.Equals(new AddressValue(ownReturnBuffer)) || !returned.Type.Equals(returnType))
                    return Fail(call.Address, "尾调用缓冲区不是本方法返回根");
                output.Add(new ManagedReturn(call.Address, ownReturnBuffer));
            }
            return true;
        }

        [InvocationOutputRule(20)]
        private RecoveryResult<bool> ConstructReturnBuffer(Call call, AbiSignature signature, Dictionary<Storage, Expr> registers,
            ManagedInvocation invocation, List<ManagedStatement> output)
        {
            if (call.Kind != CallKind.Tail || ownReturnBuffer is null || signature.Return is not null
                || invocation.Method.Method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: true }
                || !invocation.Method.DeclaringType.Equals(returnType)
                || invocation.Receiver is not AddressValue receiver || !receiver.Target.Equals(ownReturnBuffer)) return false;
            // 构造器写入调用者提供的 x8 根；保留此前的初始化，完整性仍由返回缓冲区证明检查。
            output.Add(new ManagedCall(call.Address, invocation, null, false));
            output.Add(new ManagedReturn(call.Address, ownReturnBuffer));
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
            if (ManagedAbi.SharedValue(ownReturnBuffer.Type) || ownReturnBuffer.Type is GenericParameterRef { NativeAggregate: not null }) leaves.Add(ownReturnBuffer);
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
