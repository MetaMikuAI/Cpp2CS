using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class StructIndirectRules
{
    internal static bool IndirectStruct(this RecoveryScope ctx, AbiValue value) => value.Passing == Passing.Indirect && (ctx.types.Kind(value.Type) == TypeKind.Struct || ManagedAbi.SharedValue(value.Type));
    [ParameterBinding(20)]
    internal static bool PrepareIndirectArgument(this RecoveryScope ctx, AbiValue parameter, int index)
    {
        if (!ctx.IndirectStruct(parameter))
            return false;
        var register = parameter.Pieces.Single().Register;
        var root = new AddressValue(new ArgumentValue(index, parameter.Type, 0));
        ctx.State.Signature.indirectRoots.Add(register, root);
        ctx.State.Signature.arguments[register] = new(index, root.Type, 64);
        return true;
    }

    internal static void PrepareReturnBuffer(this RecoveryScope ctx, AbiValue? value)
    {
        if (value is null || !ctx.IndirectStruct(value))
            return;
        ctx.State.Signature.ownReturnBuffer = ctx.StructLocal(value.Type, 0);
        var root = new AddressValue(ctx.State.Signature.ownReturnBuffer);
        var register = value.Pieces.Single().Register;
        ctx.State.Signature.indirectRoots.Add(register, root);
        ctx.State.Signature.arguments[register] = new(-2, root.Type, 64);
    }

    // 尾部 memcpy 完整写入本方法返回根时，保留有类型的结构体读取与复制。
    [CallRule(21)]
    internal static RecoveryResult<bool> CopyStructReturn(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (call is not { Kind: CallKind.Tail, Op: { Kind: OpKind.Import, Operand: "memcpy" }, Arguments: [var destination, var source, Const count] } || ctx.State.Signature.ownReturnBuffer is null || ctx.types.Kind(ctx.State.Signature.returnType) != TypeKind.Struct || ctx.types.Size(ctx.State.Signature.returnType) <= 0 || count.Value != (ulong)ctx.types.Size(ctx.State.Signature.returnType))
            return false;
        if (!ctx.Values.StructAddress(destination, ctx.State.Signature.returnType).TryGet(out var target, out var failure))
            return failure;
        if (!target.Equals(new AddressValue(ctx.State.Signature.ownReturnBuffer)))
            return false;
        if (!ctx.Values.StructAddress(source, ctx.State.Signature.returnType).TryGet(out var address, out failure))
            return failure;
        if (ManagedValues.Walk(address).Contains(ctx.State.Signature.ownReturnBuffer))
            return false;
        output.Add(new ManagedAssignment(call.Address, ctx.State.Signature.ownReturnBuffer, new IndirectValue(address, ctx.State.Signature.returnType)));
        output.Add(new ManagedReturn(call.Address, ctx.State.Signature.ownReturnBuffer));
        return true;
    }

    [ArgumentRule(20)]
    internal static RecoveryResult<ManagedValue?> IndirectStructArgument(this LoweringScope ctx, AbiValue parameter, ArgumentSite site) => !ctx.Values.IndirectStruct(parameter) ? (ManagedValue?)null : site.Argument(new AbiValue(new ByRefRef(parameter.Type), Passing.Registers, parameter.Pieces), site.Name).Bind(expression => ctx.Values.StructAddress(expression, parameter.Type)).Map<ManagedValue?>(address => new IndirectValue(address, parameter.Type));
    [InvocationOutputRule(10)]
    internal static RecoveryResult<bool> IndirectInvocation(this LoweringScope ctx, Call call, AbiSignature signature, Dictionary<Storage, Expr> registers, ManagedInvocation invocation, List<ManagedStatement> output)
    {
        if (signature.Return is not { } returned || !ctx.Values.IndirectStruct(returned))
            return false;
        if (!registers.TryGetValue(returned.Pieces.Single().Register, out var expression))
            return RecoveryDiagnostics.Fail(call.Address, "调用 缺少返回缓冲区", rule: "IndirectInvocation");
        if (!ctx.Values.StructAddress(expression, returned.Type).TryGet(out var address, out var failure))
            return failure;
        var result = ctx.Values.CallStructLocal(call, returned.Type);
        output.Add(new ManagedCall(call.Address, invocation, result, false));
        output.Add(new ManagedStore(call.Address, new IndirectValue(address, returned.Type), result));
        if (call.Kind is CallKind.Tail or CallKind.TailIndirect)
        {
            if (ctx.State.Signature.ownReturnBuffer is null || !address.Equals(new AddressValue(ctx.State.Signature.ownReturnBuffer)) || !returned.Type.Equals(ctx.State.Signature.returnType))
                return RecoveryDiagnostics.Fail(call.Address, "尾调用缓冲区不是本方法返回根", rule: "IndirectInvocation");
            output.Add(new ManagedReturn(call.Address, ctx.State.Signature.ownReturnBuffer));
        }

        return true;
    }

    [InvocationOutputRule(20)]
    internal static RecoveryResult<bool> ConstructReturnBuffer(this LoweringScope ctx, Call call, AbiSignature signature, Dictionary<Storage, Expr> registers, ManagedInvocation invocation, List<ManagedStatement> output)
    {
        if (call.Kind != CallKind.Tail || ctx.State.Signature.ownReturnBuffer is null || signature.Return is not null || invocation.Method.Method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: true } || !invocation.Method.DeclaringType.Equals(ctx.State.Signature.returnType) || invocation.Receiver is not AddressValue receiver || !receiver.Target.Equals(ctx.State.Signature.ownReturnBuffer))
            return false;
        // 构造器写入调用者提供的 x8 根；保留此前的初始化，完整性仍由返回缓冲区证明检查。
        output.Add(new ManagedCall(call.Address, invocation, null, false));
        output.Add(new ManagedReturn(call.Address, ctx.State.Signature.ownReturnBuffer));
        return true;
    }

    /// <summary>返回缓冲区没有隐含默认值。按 CFG 前驱交集证明每条正常返回路径都定义了全部叶子。</summary>
    [BodyProof(10)]
    internal static void ProveReturnBuffer(this RecoveryScope ctx, ManagedBody body)
    {
        if (ctx.State.Signature.ownReturnBuffer is null)
            return;
        var address = new AddressValue(ctx.State.Signature.ownReturnBuffer);
        var leaves = ctx.StructPaths(ctx.State.Signature.ownReturnBuffer.Type).Where(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null)).Select(p => ctx.PathValue(address, p.Path)).ToHashSet();
        if (ManagedAbi.SharedValue(ctx.State.Signature.ownReturnBuffer.Type) || ctx.State.Signature.ownReturnBuffer.Type is GenericParameterRef { NativeAggregate: not null })
            leaves.Add(ctx.State.Signature.ownReturnBuffer);
        var blocksByAddress = body.Blocks.ToDictionary(b => b.Address);
        IEnumerable<ulong> Successors(ManagedBlock block) => block.Statements.LastOrDefault() is { } last ? ManagedValues.Edges(last).Select(e => e.Target) : [];
        var predecessors = body.Blocks.SelectMany(b => Successors(b).Select(s => (From: b.Address, To: s))).ToLookup(e => e.To, e => e.From);
        var outputs = body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<ManagedValue>(leaves));
        HashSet<ManagedValue> Input(ManagedBlock block)
        {
            if (block == body.Blocks[0])
                return [];
            var sources = predecessors[block.Address].Where(blocksByAddress.ContainsKey).ToArray();
            if (sources.Length == 0)
                return [];
            var state = new HashSet<ManagedValue>(outputs[sources[0]]);
            foreach (var source in sources.Skip(1))
                state.IntersectWith(outputs[source]);
            return state;
        }

        void Apply(HashSet<ManagedValue> state, ManagedStatement statement)
        {
            if (statement is ManagedAssignment assignment && assignment.Target.Equals(ctx.State.Signature.ownReturnBuffer))
                state.UnionWith(leaves);
            if (statement is ManagedCall { Result: { } result } && result.Equals(ctx.State.Signature.ownReturnBuffer))
                state.UnionWith(leaves);
            if (statement is ManagedStore store)
            {
                if (leaves.Contains(store.Target))
                    state.Add(store.Target);
                if (store.Target is IndirectValue i && i.Address.Equals(address))
                    state.UnionWith(leaves);
            }
        }

        bool changed;
        do
        {
            changed = false;
            foreach (var block in body.Blocks)
            {
                var state = Input(block);
                foreach (var statement in block.Statements)
                    Apply(state, statement);
                if (!outputs[block.Address].SetEquals(state))
                {
                    outputs[block.Address] = state;
                    changed = true;
                }
            }
        }
        while (changed);
        foreach (var block in body.Blocks)
        {
            var state = Input(block);
            foreach (var statement in block.Statements)
            {
                Apply(state, statement);
                if (statement is ManagedReturn && !state.IsSupersetOf(leaves))
                    ctx.Hole(statement.Address, $"返回缓冲区仍有 {leaves.Count - state.Count} 个叶子未在所有路径定义", rule: "ProveReturnBuffer");
            }
        }
    }
}
