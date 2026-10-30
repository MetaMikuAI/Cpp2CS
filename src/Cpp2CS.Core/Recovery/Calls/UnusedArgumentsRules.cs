using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class UnusedArgumentsRules
{
    internal static bool DirectInputProof(this RecoveryScope ctx, Call call, MethodRef callee, bool receiver = false) => call is { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target } // 非虚方法的 callvirt 只负责判空；普通参数仍可按固定目标证明未用，接收者不能据此替换。
    && (!ctx.State.Runtime.virtualCalls.Contains(call) || !receiver && !callee.Method.IsVirtual) && ctx.facts.EntriesAt(target.Value).Any(e => e.Method is MethodRef candidate && candidate.Method == callee.Method);
    internal static bool UnusedParameter(this RecoveryScope ctx, Call call, Storage register) => call.Target is Const target && ctx.owner.rewriter.UnusedInput(target.Value, register);
    internal static bool UnusedInput(this RecoveryScope ctx, Call call, MethodRef callee, AbiValue parameter) => parameter is { Passing: Passing.Registers, Pieces: [var piece] } && ctx.DirectInputProof(call, callee, receiver: true) && ctx.UnusedParameter(call, piece.Register);
    internal static bool MissingInput(this RecoveryScope ctx, Expr expression) => expression is Unknown or Use { Variable.Version: < 0 } || expression is Use { Variable.Version: 0 } input && !ctx.State.Signature.arguments.ContainsKey(input.Variable.Storage) || expression is Use use && ctx.State.Runtime.runtime.Contains(use.Variable);
    internal static void PrepareUnusedReceiverPhis(this RecoveryScope ctx)
    {
        var changed = false;
        foreach (var block in ctx.blocks.Where(b => b.Predecessors.Count > 1 && !b.IsLandingPad))
            foreach (var call in block.Statements.OfType<Call>().ToArray())
            {
                if (ctx.Resolve(call) is not { } callee || ctx.owner.abi.Classify(callee, out _)?.This is not { Pieces: [var piece] } self || ctx.types.Kind(self.Type) != TypeKind.Reference || !ctx.UnusedInput(call, callee, self))
                    continue;
                var index = Array.IndexOf(call.Sources, piece.Register);
                if (index < 0 || !ctx.MissingInput(call.Arguments[index]))
                    continue;
                var receivers = block.Predecessors.Select(parent => CheckedOnPath(parent, self.Type)).ToArray();
                if (receivers.Any(v => v is null))
                    continue;
                var target = new Variable(Storage.Temp(ctx.State.Structs.Locals.Next()), 1);
                ctx.Rewriter.Insert(block, 0, new Phi(block.Start, target, receivers.Select(v => v!).ToArray()));
                var args = call.Arguments.ToArray();
                args[index] = new Use(target, piece.Width);
                var replacement = call with
                {
                    Arguments = args
                };
                ctx.Rewriter.Replace(block, block.Statements.IndexOf(call), replacement);
                changed = true;
            }

        if (!changed)
            return;
        ctx.definitions = ctx.IndexDefinitions();
        ctx.InferTypes();
        Variable? CheckedOnPath(Block block, TypeRef type)
        {
            var seen = new HashSet<Block>();
            while (seen.Add(block))
            {
                foreach (var statement in block.Statements.AsEnumerable().Reverse())
                    if (statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [Use receiver] } && ctx.State.Types.known.TryGetValue(receiver.Variable, out var actual) && ctx.types.IsAssignable(actual, type))
                        return receiver.Variable;
                if (block.Predecessors.ToArray() is not [var parent] || parent.Handler == block || !parent.NormalSuccessors.Contains(block))
                    return null;
                block = parent;
            }

            return null;
        }
    }

    // 编译器可以省略未用输入。仅填补缺失输入或不能表示成目标标量的残值，保留已有求值。
    [ArgumentRule(30)]
    internal static RecoveryResult<ManagedValue?> UnusedArgument(this LoweringScope ctx, AbiValue parameter, ArgumentSite site)
    {
        if (parameter.Passing != Passing.Registers || parameter.Pieces is not [var piece] || !site.Registers.TryGetValue(piece.Register, out var expression))
            return (ManagedValue?)null;
        var kind = ctx.types.Kind(parameter.Type);
        if (ctx.Values.MissingInput(expression) && kind is TypeKind.Reference or TypeKind.Int or TypeKind.Bool && ctx.Values.DirectInputProof(site.Call, site.Callee) && ctx.Values.UnusedParameter(site.Call, piece.Register))
        {
            var declared = site.Callee.Method.Parameters[site.Index];
            var bits = kind == TypeKind.Reference || !declared.HasDefault || declared.DefaultValue is null ? 0UL : declared.DefaultValue is ulong unsigned ? unsigned : unchecked((ulong)System.Convert.ToInt64(declared.DefaultValue));
            return new ConstantValue(bits & Expr.Mask(piece.Width), parameter.Type, piece.Width);
        }

        if (kind is not (TypeKind.Reference or TypeKind.Int or TypeKind.Bool) || expression is not (Use or Const) || expression is Use use && ctx.State.Lowering.inlined.Contains(use.Variable) || !ctx.Values.DirectInputProof(site.Call, site.Callee))
            return (ManagedValue?)null;
        if (!ctx.Values.Recover(expression, null).TryGet(out var value, out var failure))
            return failure;
        if (value is ConstantValue { Bits: 0 } || value is Fragment || ctx.types.IsAssignable(value.Type, parameter.Type) || ctx.types.Kind(value.Type) is not (TypeKind.Reference or TypeKind.Int or TypeKind.Bool) || ctx.Values.Coerce(value, parameter.Type, site.Call.Address).TryGet(out _, out _) || !ctx.Values.UnusedParameter(site.Call, piece.Register))
            return (ManagedValue?)null;
        return new ConstantValue(0, parameter.Type, piece.Width);
    }

    internal static RecoveryResult<ManagedValue?> UnusedReceiver(this RecoveryScope ctx, Call call, MethodRef callee, AbiValue self, Expr expression)
    {
        if (ctx.types.Kind(self.Type) != TypeKind.Reference)
            return (ManagedValue?)null;
        if (!ctx.MissingInput(expression) && ctx.TypeOfValue(expression) is { } actual && ctx.types.IsAssignable(actual, self.Type))
            return (ManagedValue?)null;
        if (!ctx.UnusedInput(call, callee, self))
            return (ManagedValue?)null;
        if (ctx.State.Signature.arguments.Values.FirstOrDefault(a => a.Index == -1 && ctx.types.IsAssignable(a.Type, self.Type)) is { } current)
            return new ArgumentValue(-1, current.Type, current.Width);
        var block = ctx.blocks.FirstOrDefault(b => b.Statements.Any(s => ReferenceEquals(s, call)));
        if (block is null)
            return (ManagedValue?)null;
        var callBlock = block;
        var position = block.Statements.FindIndex(s => ReferenceEquals(s, call));
        var seen = new HashSet<Block>();
        while (seen.Add(block))
        {
            foreach (var statement in block.Statements.Take(position).Reverse())
                if (statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [Use checkedValue] } && ctx.State.Types.known.TryGetValue(checkedValue.Variable, out var type) && ctx.types.IsAssignable(type, self.Type))
                    return ctx.RecoverAs(checkedValue, self.Type, call.Address).Map<ManagedValue?>(value => value);
            if (block.Predecessors.ToArray() is not [var parent] || parent.Handler == block || !parent.NormalSuccessors.Contains(block))
                break;
            block = parent;
            position = block.Statements.Count;
        }

        // 被调方不读取 this；可复用支配调用的同类型值，不额外引入字段读取或判空。
        var dominators = ctx.Dominators;
        foreach (var prior in ctx.blocks.Where(b => dominators.Dominates(b.Index, callBlock.Index)))
            foreach (var define in prior.Statements.Take(prior == callBlock ? callBlock.Statements.IndexOf(call) : prior.Statements.Count).OfType<Define>())
                if (ctx.State.Types.known.TryGetValue(define.Target, out var type) && ctx.types.IsAssignable(type, self.Type))
                    return ctx.RecoverAs(new Use(define.Target, define.Value.Width), self.Type, call.Address).Map<ManagedValue?>(value => value);
        return (ManagedValue?)null;
    }
}
