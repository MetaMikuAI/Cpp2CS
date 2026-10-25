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
        private static bool DirectInputProof(Call call, MethodRef callee) =>
            call is { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target }
            && target.Value == callee.Method.Address && callee.Method.Address != 0 && !callee.Method.IsVirtual
            && callee.Method.GenericParameters.Count == 0 && callee.Method.Owner.GenericParameters.Count == 0;

        private bool UnusedInput(Call call, MethodRef callee, AbiValue parameter) =>
            parameter is { Passing: Passing.Registers, Pieces: [var piece] }
            && DirectInputProof(call, callee) && owner.UnusedParameter(callee, piece.Register);

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
                || !owner.UnusedParameter(site.Callee, piece.Register)) return null;
            return new ConstantValue(0, parameter.Type, piece.Width);
        }

        // 无实例读取的直接调用可复用当前 this；不能凭空补 null，使 C# 调用引入空引用异常。
        private ManagedValue? UnusedReceiver(Call call, MethodRef callee, AbiValue self, Expr expression) =>
            MissingInput(expression) && types.Kind(self.Type) == TypeKind.Reference && UnusedInput(call, callee, self)
                && arguments.Values.FirstOrDefault(a => a.Index == -1 && types.IsAssignable(a.Type, self.Type)) is { } current
                ? new ArgumentValue(-1, current.Type, current.Width) : null;
    }
}
