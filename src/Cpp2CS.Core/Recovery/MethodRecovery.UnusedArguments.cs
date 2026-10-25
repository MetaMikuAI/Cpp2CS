using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Lifting;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private readonly Dictionary<MethodRef, HashSet<Storage>?> nativeInputs = new();

    private bool UnusedParameter(MethodRef method, Storage register)
    {
        if (!nativeInputs.TryGetValue(method, out var reads))
        {
            var signature = abi.Classify(method, out _)!;
            Expr? returned = signature.Return is not { } value ? null
                : new Intrinsic("diagnostic_return", value.Pieces.Select(p => (Expr)new Read(p.Register, p.Width)).ToArray(), 64);
            reads = NativeInputs.Reads(lifter.Lift(method.Method.Address, returned, simplify: false));
            nativeInputs.Add(method, reads);
        }
        return reads is not null && !reads.Contains(register);
    }

    private sealed partial class Context
    {
        // 编译器可以不设置未用参数的寄存器；仅为无法表示成引用实参的残值补 null。
        // 原有调用结果和读取仍在原处求值，不能把有副作用的表达式当作未用实参删掉。
        [ArgumentRule(30)]
        private ManagedValue? UnusedReferenceArgument(AbiValue parameter, ArgumentSite site)
        {
            var method = site.Callee.Method;
            if (types.Kind(parameter.Type) != TypeKind.Reference || parameter.Passing != Passing.Registers || parameter.Pieces is not [var piece]
                || site.Call is not { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target }
                || target.Value != method.Address || method.Address == 0 || method.IsVirtual
                || method.GenericParameters.Count != 0 || method.Owner.GenericParameters.Count != 0
                || !site.Registers.TryGetValue(piece.Register, out var expression)
                || expression is not (Use or Const) || expression is Use use && inlined.Contains(use.Variable)) return null;
            var value = Recover(expression, null);
            if (value is ConstantValue { Bits: 0 } || value is Fragment || types.IsAssignable(value.Type, parameter.Type)
                || types.Kind(value.Type) is not (TypeKind.Reference or TypeKind.Int or TypeKind.Bool)
                || !owner.UnusedParameter(site.Callee, piece.Register)) return null;
            return new ConstantValue(0, parameter.Type, piece.Width);
        }
    }
}
