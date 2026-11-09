using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Values;
using Cpp2CS.Recovery.Calls;

namespace Cpp2CS.Recovery.Typing;

public sealed record OperationTypes(TypeRef? Result, IReadOnlyList<TypeRef?> Inputs);
public enum ArgumentSupply { Content, This, Default }

public sealed partial class TypeOracle
{
    /// <summary>运算的结果与各操作数的托管类型，供约束收集和下降共用。</summary>
    public OperationTypes OperationTypes(OpSym op, TypeRef? expected)
    {
        var natural = TypeOf(op);
        switch (op.Op.Kind)
        {
            case OperatorKind.Compare:
                var hint = TypeOf(op.Args[0]) ?? TypeOf(op.Args[1]);
                if (hint is not null && types.Kind(hint) == TypeKind.Struct && op.Args[1].Width == op.Args[0].Width
                    && types.Size(hint) * 8 == op.Args[0].Width && Innermost(hint).Type is var scalar
                    && (types.Kind(scalar) is TypeKind.Int or TypeKind.Bool || ManagedTypes.IsReferenceType(scalar))) hint = scalar;
                return new(types.Boolean, [hint, hint]);
            case OperatorKind.And or OperatorKind.Or: return new(types.Boolean, [types.Boolean, types.Boolean]);
            case OperatorKind.Not: return new(types.Boolean, [types.Boolean]);
            case OperatorKind.Select:
                var selected = Defined(op) ?? expected ?? types.Integer(op.Width is 8 or 16 or 32 or 64 ? op.Width : 64, true);
                return new(selected, [types.Boolean, selected, selected]);
            case OperatorKind.Binary when op.Width == 1 && op.Op.Binary is BinOp.And or BinOp.Or or BinOp.Xor:
                return new(types.Boolean, [types.Boolean, types.Boolean]);
            // 浮点运算的类型由运算决定：期望同宽整数时是结果的位重解释，运算本身仍是浮点的。
            case OperatorKind.Binary when natural is not null && types.Kind(natural) is TypeKind.Float or TypeKind.Double:
                return new(natural, [natural, natural]);
            case OperatorKind.Binary:
                var binary = expected is not null && types.Kind(expected) == TypeKind.Int && types.ValueWidth(expected) == op.Width
                    ? expected : natural ?? Unconstrained(op.Width);
                return new(binary, [binary, op.Op.Binary is BinOp.Shl or BinOp.LShr or BinOp.AShr ? types.Int32 : binary]);
            case OperatorKind.Unary:
                var unary = natural ?? (expected is not null && types.Kind(expected) == TypeKind.Int && types.ValueWidth(expected) == op.Width
                    ? expected : Unconstrained(op.Width));
                return new(unary, [unary]);
            case OperatorKind.Convert:
                var result = natural ?? (expected is not null && types.ValueWidth(expected) == op.Width ? expected : null);
                var width = op.Args[0].Width;
                var source = op.Op.Conversion switch
                {
                    ConvKind.SignExtend when width is not (8 or 16 or 32 or 64) => op.Width > 32 ? types.Int64 : types.Int32,
                    ConvKind.FloatToFloat or ConvKind.FloatToSInt or ConvKind.FloatToUInt => width == 32 ? types.Single : types.Double,
                    ConvKind.SIntToFloat or ConvKind.SignExtend when width is 8 or 16 or 32 or 64 => TypeOf(op.Args[0]) is { } t && types.Kind(t) == TypeKind.Int ? t : types.Integer(width, true),
                    ConvKind.UIntToFloat when width is 8 or 16 or 32 or 64 => types.Integer(width, false),
                    _ => TypeOf(op.Args[0]),
                };
                return new(result, [source]);
            default: return new(natural, op.Args.Select(TypeOf).ToArray());
        }
    }

    /// <summary>调用中实参的类型；受约束调用的接收者是约束类型的托管地址。</summary>
    public static TypeRef ArgumentType(Call call, MethodRef callee, int index) => index < 0 && ConstraintOf(call) is { } constraint
        ? new ByRefRef(constraint) : ArgumentType(callee, index);

    public static TypeRef? ConstraintOf(Call call) => call.Op is { Kind: OpKind.InvokeConstrainedGeneric or OpKind.CallConstrained, Operand: ValueTuple<TypeRef, MethodRef> constrained } ? constrained.Item1 : null;

    public static TypeRef ArgumentType(MethodRef callee, int index) => index < 0
        ? callee.Method.Owner.IsValueType ? new ByRefRef(callee.DeclaringType) : callee.DeclaringType
        : callee.Concrete(callee.Method.Parameters[index].Type);

    /// <summary>原生被调方不读取的按值槽，只有无法按签名解释时才用类型正确的无关值。</summary>
    public ArgumentSupply Supply(CallShape shape, MachineValue value, TypeRef type, Sym content)
    {
        if (value.Transfer != Transfer.Value || value.Pieces.Length == 0 || !value.Pieces.All(p => shape.Unused.Contains(p.Register))) return ArgumentSupply.Content;
        if (Interpretable(content, type, [])) return ArgumentSupply.Content;
        if (value.Index < 0 && !method.Method.IsStatic && Parameter(-1) is { } self && (self.Equals(type) || types.IsAssignable(self, type))) return ArgumentSupply.This;
        return ManagedTypes.IsReferenceType(type) || types.Kind(type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Pointer or TypeKind.Struct
            ? ArgumentSupply.Default : ArgumentSupply.Content;
    }

    /// <summary>值的每条路径都能按类型解释。φ 的下界略过没有类型的来源（寄存器里的残值），这里逐路径核对。</summary>
    private bool Interpretable(Sym content, TypeRef type, HashSet<Sym> seen)
    {
        content = SymTable.Resolve(content);
        if (!seen.Add(content) || content is UndefSym) return true;
        if (content is PhiSym { Projection: null } phi) return phi.Sources.All(s => s is null || Interpretable(s, type, seen));
        return TypeOf(content) is { } actual && (actual.Equals(type) || types.IsAssignable(actual, type));
    }

    public (Sym Owner, TypeRef Type)? ClassIdentity(Sym left, Sym right)
    {
        foreach (var (a, b) in new[] { (left, right), (right, left) })
            if (ClassOwner(a) is { } owner && SymTable.Resolve(b) is EntitySym { Symbol: { Kind: SymbolKind.Class, Value: DefinitionRef type } }
                && (type.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) != 0) return (owner, type);
        return null;
    }

    /// <summary>跳转表目标中唯一一次读取的比例下标。</summary>
    public Sym? TableIndex(Sym target)
    {
        var stack = new Stack<Sym>();
        stack.Push(target);
        Sym? found = null;
        while (stack.TryPop(out var next))
        {
            switch (SymTable.Resolve(next))
            {
                case ReadSym read:
                    if (found is not null) return null;
                    var (root, _, index, _) = Decompose(read.Address);
                    index ??= root is ConstSym || ReferenceEquals(root, SymTable.Resolve(read.Address)) ? null : root;
                    if (index is null) return null;
                    found = index;
                    break;
                case SliceSym slice: stack.Push(slice.Base); break;
                case ConcatSym concat: foreach (var part in concat.Parts) stack.Push(part); break;
                case OpSym op: foreach (var arg in op.Args) stack.Push(arg); break;
            }
        }
        return found;
    }
}
