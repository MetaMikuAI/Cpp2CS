using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Lifting;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private bool DirectInputProof(Call call, MethodRef callee) =>
            call is { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target }
            && !callee.Method.IsVirtual && facts.EntriesAt(target.Value).Any(e => e.Method is MethodRef candidate && candidate.Method == callee.Method);

        private bool UnusedParameter(Call call, Storage register) =>
            call.Target is Const target && owner.rewriter.UnusedInput(target.Value, register);

        private bool UnusedInput(Call call, MethodRef callee, AbiValue parameter) =>
            parameter is { Passing: Passing.Registers, Pieces: [var piece] }
            && DirectInputProof(call, callee) && UnusedParameter(call, piece.Register);

        private static bool MissingInput(Expr expression) => expression is Unknown or Use { Variable.Version: < 0 };

        // 编译器可以省略未用输入。仅填补 Unknown 或不能表示成引用的残值，保留已有求值。
        [ArgumentRule(30)]
        private ManagedValue? UnusedArgument(AbiValue parameter, ArgumentSite site)
        {
            if (parameter.Passing != Passing.Registers || parameter.Pieces is not [var piece]
                || !site.Registers.TryGetValue(piece.Register, out var expression)) return null;
            var kind = types.Kind(parameter.Type);
            if (MissingInput(expression) && kind is TypeKind.Reference or TypeKind.Int or TypeKind.Bool
                && UnusedInput(site.Call, site.Callee, parameter))
            {
                var declared = site.Callee.Method.Parameters[site.Index];
                var bits = kind == TypeKind.Reference || !declared.HasDefault || declared.DefaultValue is null ? 0UL
                    : declared.DefaultValue is ulong unsigned ? unsigned : unchecked((ulong)System.Convert.ToInt64(declared.DefaultValue));
                return new ConstantValue(bits & Expr.Mask(piece.Width), parameter.Type, piece.Width);
            }
            if (kind != TypeKind.Reference
                || expression is not (Use or Const) || expression is Use use && inlined.Contains(use.Variable)
                || !DirectInputProof(site.Call, site.Callee)) return null;
            var value = Recover(expression, null);
            if (value is ConstantValue { Bits: 0 } || value is Fragment || types.IsAssignable(value.Type, parameter.Type)
                || types.Kind(value.Type) is not (TypeKind.Reference or TypeKind.Int or TypeKind.Bool)
                || !UnusedParameter(site.Call, piece.Register)) return null;
            return new ConstantValue(0, parameter.Type, piece.Width);
        }

        // 无实例读取的直接调用可复用当前 this 或必经路径上的同类型 SSA 值。
        private ManagedValue? UnusedReceiver(Call call, MethodRef callee, AbiValue self, Expr expression)
        {
            if (types.Kind(self.Type) != TypeKind.Reference) return null;
            if (!MissingInput(expression) && (TypeOfValue(expression) is not { } actual || types.IsAssignable(actual, self.Type))) return null;
            if (!UnusedInput(call, callee, self)) return null;
            if (arguments.Values.FirstOrDefault(a => a.Index == -1 && types.IsAssignable(a.Type, self.Type)) is { } current)
                return new ArgumentValue(-1, current.Type, current.Width);
            var block = blocks.FirstOrDefault(b => b.Statements.Any(s => ReferenceEquals(s, call)));
            if (block is null) return null;
            var callBlock = block;
            var position = block.Statements.FindIndex(s => ReferenceEquals(s, call));
            var seen = new HashSet<Block>();
            while (seen.Add(block))
            {
                foreach (var statement in block.Statements.Take(position).Reverse())
                    if (statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [Use checkedValue] }
                        && known.TryGetValue(checkedValue.Variable, out var type) && types.IsAssignable(type, self.Type))
                        return RecoverAs(checkedValue, self.Type, call.Address);
                if (block.Predecessors.ToArray() is not [var parent] || parent.Handler == block || !parent.NormalSuccessors.Contains(block)) break;
                block = parent;
                position = block.Statements.Count;
            }
            // 被调方不读取 this；可复用支配调用的同类型值，不额外引入字段读取或判空。
            var dominators = Ssa.Dominators.Compute(function);
            foreach (var prior in blocks.Where(b => dominators.Dominates(b.Index, callBlock.Index)))
                foreach (var define in prior.Statements.Take(prior == callBlock ? callBlock.Statements.IndexOf(call) : prior.Statements.Count).OfType<Define>())
                    if (known.TryGetValue(define.Target, out var type) && types.IsAssignable(type, self.Type))
                        return RecoverAs(new Use(define.Target, define.Value.Width), self.Type, call.Address);
            return null;
        }
    }
}
