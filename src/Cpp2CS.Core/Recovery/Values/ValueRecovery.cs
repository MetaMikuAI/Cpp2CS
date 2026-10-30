using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Recovery;

internal static class ValueRecovery
{
    internal static TypeRef? TypeOfValue(this RecoveryScope ctx, Expr e)
    {
        return ctx.Recover(e, null).TryGet(out var value, out _) ? value.Type : null;
    }

    internal static RecoveryResult<LocalValue> LocalOf(this RecoveryScope ctx, Variable v)
    {
        if (ctx.CheckPoison(v) is { } poison)
            return poison;
        if (ctx.State.Runtime.runtime.Contains(v))
            return RecoveryDiagnostics.Fail(0, $"运行时引用 {v} 作为托管值", rule: "LocalOf");
        if (!ctx.State.Types.known.TryGetValue(v, out var type))
            return new RecoveryFailure(0, $"变量 {v} 的类型未确定", Unresolved: v, Code: "recovery.variable-type");
        var width = ctx.LocalWidth(v);
        switch (ctx.types.Kind(type))
        {
            case TypeKind.Float or TypeKind.Double when ctx.types.Bits(type) != width:
                return RecoveryDiagnostics.Fail(0, $"浮点 变量 {v} 的类型 {type} 与定义位宽 {width} 不一致", rule: "LocalOf");
            case TypeKind.Int when ctx.types.Bits(type) != width && type is not GenericParameterRef:
            case TypeKind.Bool when width is not (1 or 8):
                if (width is not (1 or 8 or 16 or 32 or 64))
                    return RecoveryDiagnostics.Fail(0, $"变量 {v} 的位宽 {width}", rule: "LocalOf");
                type = ctx.IntegerOf(width, ManagedTypes.IsSigned(type));
                break;
            case TypeKind.Pointer when type is ByRefRef:
                break;
            case TypeKind.Pointer when width == 64 && ManagedTypes.IsNativePointer(type):
                break;
            case TypeKind.Struct or TypeKind.Pointer or TypeKind.Void or null:
                return RecoveryDiagnostics.Fail(0, $"变量 {v} 的类型 {type} 尚未支持", rule: "LocalOf");
        }

        return new LocalValue(v, type, width);
    }

    internal static int LocalWidth(this RecoveryScope ctx, Variable v)
    {
        if (ctx.values.TryGetValue(v, out var value))
            return value.Width;
        if (ctx.results.TryGetValue(v, out var result))
            return ctx.State.Types.known.TryGetValue(v, out var t) ? Math.Max(ctx.types.Bits(t), 8) : result.Call.Results[result.Index].Width;
        if (ctx.phis.TryGetValue(v, out var phi))
        {
            if (ctx.State.Types.known.TryGetValue(v, out var reference) && ctx.types.Kind(reference) == TypeKind.Reference)
                return 64;
            // 各来源位宽的最大值；常量来源只要求容得下它的值。环上的来源（正在计算的 φ）跳过。
            if (!ctx.State.Types.phiInProgress.Add(v))
                return 0;
            try
            {
                var width = 0;
                foreach (var source in phi.Sources)
                {
                    if (ctx.values.TryGetValue(source, out var c) && c is Const constant)
                        width = Math.Max(width, constant.Value == 0 ? 1 : 64 - System.Numerics.BitOperations.LeadingZeroCount(constant.Value));
                    else if (source.Version == 0 && ctx.State.Signature.arguments.TryGetValue(source.Storage, out var argument))
                        width = Math.Max(width, argument.Width);
                    else
                        width = Math.Max(width, ctx.LocalWidth(source));
                }

                if (width == 0)
                    width = ctx.State.Types.known.TryGetValue(v, out var t) ? Math.Max(ctx.types.Bits(t), 8) : 64;
                // 结构体 ABI 返回片可含高位填充；终端整数 φ 只保留所有实际读取需要的低位。
                if (ctx.State.Types.known.TryGetValue(v, out var integer) && ctx.types.Kind(integer) is TypeKind.Int or TypeKind.Bool && !ctx.phiUses.GetValueOrDefault(v, []).Any() && phi.Sources.Any(s => ctx.results.TryGetValue(s, out var r) && ctx.Resolve(r.Call) is { } callee && ctx.owner.abi.Classify(callee, out _)?.Return is { } returned && ctx.RegisterStruct(returned)))
                {
                    var reads = ctx.blocks.SelectMany(b => b.Statements).Where(s => s is not Phi).SelectMany(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>()).Where(u => u.Variable == v).ToArray();
                    if (reads.Length > 0)
                        width = Math.Min(width, reads.Max(u => u.Width));
                }

                return width switch
                {
                    1 => 1,
                    <= 8 => 8,
                    <= 16 => 16,
                    <= 32 => 32,
                    _ => 64
                };
            }
            finally
            {
                ctx.State.Types.phiInProgress.Remove(v);
            }
        }

        return v.Width;
    }

    internal static RecoveryResult<ManagedValue> RecoverAs(this RecoveryScope ctx, Expr e, TypeRef target, ulong address)
    {
        if (ctx.types.Kind(target) == TypeKind.Reference && e is Use { Width: 64 } && (ctx.State.Runtime.nullPaths ??= new NullPathFacts(ctx.function)).IsNull(e, address))
            return new ConstantValue(0, target, 64);
        if (ctx.types.Kind(target) == TypeKind.Reference && e is Use { Width: 64 } referenceValue && ctx.TypeOfValue(e) is { } sourceType && ctx.types.Kind(sourceType) == TypeKind.Reference && !ctx.types.IsAssignable(sourceType, target) && ctx.CheckedReference(referenceValue, target, address))
            return ctx.Recover(e, sourceType).Map<ManagedValue>(value => new IsInstValue(value, target));
        return target is ByRefRef reference ? ctx.StructAddress(e, reference.Element) : ctx.Recover(e, target).Bind(value => ctx.Coerce(value, target, address));
    }

    internal static RecoveryResult<ManagedValue> Coerce(this RecoveryScope ctx, ManagedValue value, TypeRef target, ulong address)
    {
        if (target is GenericParameterRef { NativeScalar: not null })
        {
            if (value.Type.Equals(target))
                return value;
            if (value is ConstantValue { Bits: 0 })
                return new ConstantValue(0, target, ctx.types.Bits(target));
            return RecoveryDiagnostics.Fail(address, $"泛型复制 {value.Type} 不能转换为 {target}", rule: "Coerce");
        }

        if (value.Type is GenericParameterRef { NativeScalar: not null })
            return RecoveryDiagnostics.Fail(address, $"泛型复制 不能将 {value.Type} 当作 {target}", rule: "Coerce");
        // 窄于片的整数目标只取低位（如寄存器结构体的首叶子作为 int 实参；高位是填充）。
        if (value is Fragment fragment)
        {
            var projected = ctx.types.Kind(target) is TypeKind.Int && ctx.types.Bits(target) < fragment.Width ? ctx.Slice(fragment, 0, ctx.types.Bits(target)) : ctx.Pack(fragment);
            if (!projected.TryGet(out value, out var failure))
                return failure;
        }

        if (value is Fragment remaining && !ctx.Pack(remaining).TryGet(out value, out var packFailure))
            return packFailure;
        // 打包寄存器中的浮点叶子已经有托管类型；来回的同宽位重解释是恒等值。
        if (value is ConversionValue { Kind: ConvKind.Bitcast } bitcast && bitcast.Operand.Type.Equals(target))
            return bitcast.Operand;
        // 已是目标类型的值（如寄存器结构体的 IntPtr 叶子 Playable.m_Handle.m_Handle）原样使用。
        if (value.Type.Equals(target) && ctx.types.Kind(target) == TypeKind.Pointer && target is DefinitionRef)
            return value;
        var kind = ctx.types.Kind(target);
        var width = kind is TypeKind.Bool ? 8 : ctx.types.Bits(target);
        switch (kind)
        {
            case TypeKind.Pointer when ManagedTypes.IsNativePointer(target):
                if (target is PointerRef && value is AddressValue { Target: LocalValue local }
                    && (ctx.types.Kind(local.Type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double || ManagedTypes.IsNativePointer(local.Type)))
                    return new ConversionValue(ConvKind.Bitcast, value, target, 64);
                if (value is ConstantValue { Bits: 0, Width: 64 })
                    return new ConstantValue(0, target, 64);
                if (value.Width == 64 && ManagedTypes.IsNativePointer(value.Type))
                    return value.Type.Equals(target) ? value : new ConversionValue(ConvKind.Bitcast, value, target, 64);
                return RecoveryDiagnostics.Fail(address, $"指针 {value.Type} 不能转换为 {target}", rule: "Coerce");
            case TypeKind.Reference:
                if (value is ConstantValue { Bits: 0 })
                    return new ConstantValue(0, target, 64);
                if (value.Type is GenericParameterRef { IsReferenceConstrained: false } generic && !target.Equals(generic) && ctx.types.IsAssignable(generic, target))
                    return new BoxValue(value, generic, target);
                if (ctx.types.Kind(value.Type) == TypeKind.Reference && ctx.types.IsAssignable(value.Type, target))
                    return value;
                return RecoveryDiagnostics.Fail(address, $"类型 {value.Type} 不能赋给 {target}", rule: "Coerce");
            case TypeKind.Bool or TypeKind.Int:
                if (value is ConstantValue c)
                    return new ConstantValue(c.Bits & Expr.Mask(width), target, width);
                switch (ctx.types.Kind(value.Type))
                {
                    case TypeKind.Bool or TypeKind.Int:
                        if (value.Width == width)
                            return value;
                        return new ConversionValue(value.Width > width ? ConvKind.Truncate : ConvKind.ZeroExtend, value, target, width);
                    case TypeKind.Float or TypeKind.Double when value.Width == width:
                        return new ConversionValue(ConvKind.Bitcast, value, target, width);
                }

                return RecoveryDiagnostics.Fail(address, $"类型 {value.Type} 不能作为整数 {target}", rule: "Coerce");
            case TypeKind.Float or TypeKind.Double:
                if (value is ConstantValue f && f.Width == width)
                    return new ConstantValue(f.Bits, target, width);
                if (ctx.types.Kind(value.Type) == kind && value.Width == width)
                    return value;
                if (ctx.types.Kind(value.Type) == TypeKind.Int && value.Width == width)
                    return new ConversionValue(ConvKind.Bitcast, value, target, width);
                return RecoveryDiagnostics.Fail(address, $"类型 {value.Type} 不能作为浮点 {target}", rule: "Coerce");
            default:
                return RecoveryDiagnostics.Fail(address, $"类型 目标类型 {target} 尚未支持", rule: "Coerce");
        }
    }

    internal static DefinitionRef IntegerOf(this RecoveryScope ctx, int width, bool signed) => width == 1 ? ctx.types.Boolean : ctx.types.Integer(width, signed);
    internal static RecoveryResult<ManagedValue> Recover(this RecoveryScope ctx, Expr e, TypeRef? hint)
    {
        RecoveryFailure failure;
        switch (e)
        {
            case Intrinsic { Name: "pinned_array_start", Arguments: [var array] }:
                if (!ctx.Recover(array, null).TryGet(out var pinned, out failure))
                    return failure;
                return pinned.Type is ArrayRef { IsVector: true } arrayType ? new PinnedArrayValue(pinned, arrayType) : RecoveryDiagnostics.Fail(0, "固定地址 来源不是一维数组", rule: "Recover");
            case Intrinsic { Name: "managed_field_address" or "managed_generic_buffer" or "managed_generic_argument" } address:
                return ctx.SharedAddress(address);
            case TypedFrame f:
                return new AddressValue(f.Region.Local);
            case Const c:
                {
                    if (hint is GenericParameterRef { NativeScalar: not null } && c.Value != 0)
                        return RecoveryDiagnostics.Fail(0, "泛型复制 只接受默认值常量", rule: "Recover");
                    if (hint is not null)
                    {
                        var kind = ctx.types.Kind(hint);
                        if (kind == TypeKind.Reference && c.Value == 0)
                            return new ConstantValue(0, hint, 64);
                        if (ManagedTypes.IsNativePointer(hint) && c.Value == 0 && c.Width == 64)
                            return new ConstantValue(0, hint, 64);
                        if (kind is TypeKind.Int or TypeKind.Float or TypeKind.Double && ctx.types.Bits(hint) == c.Width)
                            return new ConstantValue(c.Value, hint, c.Width);
                        if (kind == TypeKind.Bool && c.Width is 1 or 8)
                            return new ConstantValue(c.Value, hint, c.Width);
                    }

                    if (c.Width is not (1 or 8 or 16 or 32 or 64))
                        return RecoveryDiagnostics.Fail(0, $"常量 位宽 {c.Width}", rule: "Recover");
                    return new ConstantValue(c.Value, ctx.IntegerOf(c.Width, true), c.Width);
                }

            case Use u:
                return ctx.Variable(u.Variable, u.Width);
            case Extract extract:
                return ctx.Recover(extract.Operand, null).Bind(value => ctx.Slice(value, extract.Low, extract.Width));
            case Insert insert:
                return ctx.InsertedFragment(insert);
            case Load load:
                return ctx.Location(load.Address, load.Width).Bind(value => hint is not null
                    && ctx.types.Kind(hint) is TypeKind.Float or TypeKind.Double
                    && value is IndirectValue && value.Width == ctx.types.Bits(hint)
                    ? ctx.Coerce(value, hint, 0) : value);
            case Symbol { Kind: SymbolKind.String, Value: string text }:
                return new StringValue(text, ctx.types.String);
            case Binary b:
                return ctx.Binary(b);
            case Unary { Op: UnOp.Neg or UnOp.Not } u:
                {
                    if (!ctx.Recover(u.Operand, hint).TryGet(out var operand, out failure))
                        return failure;
                    if (operand is Fragment f && !ctx.Pack(f).TryGet(out operand, out failure))
                        return failure;
                    if (operand.Type is GenericParameterRef { NativeScalar: not null } || ctx.types.Kind(operand.Type) is not (TypeKind.Int or TypeKind.Bool))
                        return RecoveryDiagnostics.Fail(0, $"运算 {u.Op} 的操作数类型 {operand.Type}", rule: "Recover");
                    return new UnaryValue(u.Op, operand, ctx.IntegerOf(u.Width, ManagedTypes.IsSigned(operand.Type)), u.Width);
                }

            case Unary { Op: UnOp.FNeg or UnOp.FAbs or UnOp.FSqrt or UnOp.FFloor or UnOp.FCeil or UnOp.FTrunc or UnOp.FRoundEven } u:
                return ctx.FloatingNegation(u);
            case Compare c:
                return ctx.Comparison(c);
            case Convert c:
                return ctx.Conversion(c, hint);
            // 精确类型检查后的引用选择；值类型仍保留装箱对象。
            case Ir.Select { Condition: Compare { Cond: Cond.Eq } test, False: Const { Value: 0 } } s when RuntimeRules.SealedOperands(test) is var (klass, sealedType) && ctx.State.Runtime.objectClasses.TryGetValue(klass, out var tested) && s.True == tested:
                return ctx.Recover(tested, ctx.types.Object).Map<ManagedValue>(value => new IsInstValue(value, sealedType, sealedType.Definition.IsValueType ? ctx.types.Object : null));
            case Ir.Select s:
                {
                    if (!ctx.Recover(s.Condition, ctx.types.Boolean).TryGet(out var condition, out failure))
                        return failure;
                    // 常量臂没有独立类型；先从另一臂取得引用或浮点类型，避免把 null 当成 long。
                    if (hint is null && s.True is Const && s.False is not Const)
                        hint = ctx.TypeOfValue(s.False);
                    if (!ctx.Recover(s.True, hint).TryGet(out var whenTrue, out failure))
                        return failure;
                    // 同布局结构体片逐叶子选择；条件只能读取稳定值，不能因拆片重复访存或分配。
                    if (whenTrue is Fragment first && first.Width == s.Width && ManagedValues.Walk(condition).All(v => v is ArgumentValue or LocalValue or ConstantValue or ConversionValue or BinaryValue or ComparisonValue or UnaryValue or BooleanValue or NegatedValue) && ctx.Recover(s.False, hint).TryGet(out var alternative, out _) && alternative is Fragment second && second.Width == s.Width && first.Parts.Select(p => (p.Low, p.Value.Type, p.Value.Width)).SequenceEqual(second.Parts.Select(p => (p.Low, p.Value.Type, p.Value.Width))))
                        return new Fragment(first.Parts.Zip(second.Parts, (a, b) => new Part(a.Low, new ChoiceValue(condition, a.Value, b.Value, a.Value.Type, a.Value.Width))).ToArray(), first.Type, s.Width);
                    if (whenTrue is Fragment f && !ctx.Pack(f).TryGet(out whenTrue, out failure))
                        return failure;
                    if (!ctx.Recover(s.False, whenTrue.Type).Bind(value => ctx.Coerce(value, whenTrue.Type, 0)).TryGet(out var whenFalse, out failure))
                        return failure;
                    if (whenTrue.Width != s.Width || whenFalse.Width != s.Width)
                        return RecoveryDiagnostics.Fail(0, "选择 两侧位宽不一致", rule: "Recover");
                    return new ChoiceValue(condition, whenTrue, whenFalse, whenTrue.Type, s.Width);
                }

            case Logical l:
                return ctx.Recover(l.Left, ctx.types.Boolean).Bind(ValueRecovery.Truth).Bind(left => ctx.Recover(l.Right, ctx.types.Boolean).Bind(ValueRecovery.Truth).Map<ManagedValue>(right => new BooleanValue(l.IsAnd, left, right, ctx.types.Boolean)));
            case Not n:
                return ctx.Recover(n.Operand, ctx.types.Boolean).Bind(ValueRecovery.Truth).Map<ManagedValue>(value => new NegatedValue(value, ctx.types.Boolean));
            default:
                return RecoveryDiagnostics.Fail(0, $"表达式 {e.GetType().Name} 尚未支持", rule: "Recover");
        }
    }

    internal static RecoveryResult<ManagedValue> Truth(ManagedValue value) => value.Width == 1 ? value : RecoveryDiagnostics.Fail(0, "条件 不是一位的布尔值", rule: "Truth");
    internal static RecoveryResult<ManagedValue> Variable(this RecoveryScope ctx, Variable v, int width)
    {
        if (ctx.State.Exceptions.collectingExceptionDemand)
            ctx.State.Exceptions.exceptionDemand.Add(v);
        // SSA 的负版本是未定义/被调用破坏的值，不能因 phi 反向推断出类型就读零初始化局部。
        if (ctx.State.Exceptions.exceptionLayout is { Succeeded: true } && v.Version < 0)
            return RecoveryDiagnostics.Fail(0, $"异常区域 读取未定义 SSA 值 {v}", rule: "Variable");
        if (ctx.CheckPoison(v) is { } poison)
            return poison;
        if (ctx.State.Arrays.arrayOffsets.TryGetValue(v, out var offset))
            return ctx.Recover(Fold.Convert(ConvKind.Truncate, offset, width), null);
        if (ctx.State.Exceptions.exceptionValues.TryGetValue(v, out var exception))
            return exception;
        if (width == 64 && v.Version == 0 && ctx.State.Signature.indirectRoots.TryGetValue(v.Storage, out var root))
            return root;
        if (!ctx.RegisterPiece(v, width).TryGet(out var piece, out var failure))
            return failure;
        if (piece is not null)
            return piece;
        if (!ctx.StructPhiPiece(v, width).TryGet(out var merged, out failure))
            return failure;
        if (merged is not null)
            return merged;
        if (!ctx.FragmentVariable(v, width).TryGet(out var fragment, out failure))
            return failure;
        if (fragment is not null)
            return fragment;
        ManagedValue value;
        bool signed;
        if (v.Version == 0)
        {
            if (!ctx.State.Signature.arguments.TryGetValue(v.Storage, out var argument))
                return RecoveryDiagnostics.Fail(0, $"入口 读取了参数之外的入口寄存器 {v}", rule: "Variable");
            value = new ArgumentValue(argument.Index, argument.Type, argument.Width);
            signed = ManagedTypes.IsSigned(argument.Type);
        }
        else if (ctx.State.Lowering.inlined.Contains(v))
        {
            var hint = ctx.State.Types.known.GetValueOrDefault(v);
            if (!ctx.Recover(ctx.values[v], hint is not null && ctx.types.Kind(hint) is TypeKind.Float or TypeKind.Double ? hint : null).TryGet(out value, out failure))
                return failure;
            signed = false;
        }
        else
        {
            if (!ctx.LocalOf(v).TryGet(out var local, out failure))
                return failure;
            value = local;
            signed = false;
        }

        if (value is Fragment inlineFragment)
            return width < value.Width ? ctx.Slice(inlineFragment, 0, width) : ctx.ResizeFragment(inlineFragment, width);
        if (width == value.Width)
            return value;
        if (value.Type is GenericParameterRef { NativeScalar: not null } && width >= ctx.types.Bits(value.Type))
            return new ConversionValue(ConvKind.ZeroExtend, value, value.Type, width);
        if (ctx.types.Kind(value.Type) is not (TypeKind.Int or TypeKind.Bool))
            return RecoveryDiagnostics.Fail(0, $"位宽 {value.Type} 以 {width} 位读取", rule: "Variable");
        if (width is not (1 or 8 or 16 or 32 or 64))
            return RecoveryDiagnostics.Fail(0, $"位宽 {width} 的整数转换尚未支持", rule: "Variable");
        return new ConversionValue(width < value.Width ? ConvKind.Truncate : signed ? ConvKind.SignExtend : ConvKind.ZeroExtend, value, ctx.IntegerOf(width, ManagedTypes.IsSigned(value.Type)), width);
    }

    internal static RecoveryResult<ManagedValue> Binary(this RecoveryScope ctx, Binary b)
    {
        // C++ bool 传参取低一位；布局见证为 bool 的 T 在托管侧仍是同一个 T 值。
        RecoveryFailure failure;
        if (b is { Op: BinOp.And, Right: Const { Value: 1 } })
        {
            if (!ctx.Recover(b.Left, null).TryGet(out var boolean, out failure))
                return failure;
            if (boolean.Type is GenericParameterRef { NativeScalar: { } scalar } && ctx.types.Kind(scalar) == TypeKind.Bool)
                return new ConversionValue(ConvKind.ZeroExtend, boolean, boolean.Type, b.Width);
        }

        if (b is { Op: BinOp.Ror, Width: 32 or 64 })
        {
            var shift = new Binary(BinOp.And, b.Right, Expr.C((ulong)b.Width - 1, b.Right.Width), b.Right.Width);
            var opposite = new Binary(BinOp.And, new Unary(UnOp.Neg, shift, shift.Width), Expr.C((ulong)b.Width - 1, shift.Width), shift.Width);
            return ctx.Recover(new Binary(BinOp.Or, new Binary(BinOp.LShr, b.Left, shift, b.Width), new Binary(BinOp.Shl, b.Left, opposite, b.Width), b.Width), null);
        }

        if (b.Op is BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv or BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber)
        {
            if (b.Width is not (32 or 64))
                return RecoveryDiagnostics.Fail(0, $"运算 {b.Op} 的浮点宽度 {b.Width} 尚未支持", rule: "Binary");
            var floating = b.Width == 32 ? ctx.types.Single : ctx.types.Double;
            if (!ctx.Recover(b.Left, floating).Bind(value => ctx.Coerce(value, floating, 0)).TryGet(out var fl, out failure))
                return failure;
            if (!ctx.Recover(b.Right, floating).Bind(value => ctx.Coerce(value, floating, 0)).TryGet(out var fr, out failure))
                return failure;
            return new BinaryValue(b.Op, fl, fr, floating, b.Width);
        }

        if (b.Op is not (BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr or BinOp.SDiv or BinOp.UDiv))
            return RecoveryDiagnostics.Fail(0, $"运算 {b.Op} 尚未支持", rule: "Binary");
        ManagedValue left, right;
        if (b.Left is Const && b.Right is not Const)
        {
            if (!ctx.Recover(b.Right, null).TryGet(out right, out failure))
                return failure;
            if (!ctx.Recover(b.Left, right.Type).TryGet(out left, out failure))
                return failure;
        }
        else
        {
            if (!ctx.Recover(b.Left, null).TryGet(out left, out failure))
                return failure;
            if (!ctx.Recover(b.Right, b.Op is BinOp.Shl or BinOp.LShr or BinOp.AShr ? null : left.Type).TryGet(out right, out failure))
                return failure;
        }

        if (!ctx.FrameShift(b.Op, left, right, b.Width).TryGet(out var projected, out failure))
            return failure;
        if (projected is not null)
            return projected;
        if (b.Op == BinOp.Add && b.Width == 64 && left.Type is PointerRef && ctx.types.Kind(right.Type) == TypeKind.Int)
            return new PointerOffsetValue(left, right);
        if (b.Op == BinOp.Add && b.Width == 64 && right.Type is PointerRef && ctx.types.Kind(left.Type) == TypeKind.Int)
            return new PointerOffsetValue(right, left);
        // 掩码清除的填充位来自指令语义；保留的位仍须来自已知叶子。
        if (b.Op == BinOp.And && left is Fragment masked && right is ConstantValue { Bits: var mask })
        {
            if (!ctx.MaskFragment(masked, mask, b.Width).TryGet(out var kept, out failure))
                return failure;
            if (kept is not null)
                return kept;
        }

        if (left is Fragment lf && !ctx.Pack(lf).TryGet(out left, out failure))
            return failure;
        if (right is Fragment rf && !ctx.Pack(rf).TryGet(out right, out failure))
            return failure;
        if (left.Type is GenericParameterRef { NativeScalar: not null } || right.Type is GenericParameterRef { NativeScalar: not null })
            return RecoveryDiagnostics.Fail(0, "泛型复制 不支持原生数值比较", rule: "Binary");
        foreach (var operand in new[]
        {
            left,
            right
        }

        )
            if (operand.Type is GenericParameterRef { NativeScalar: not null } || ctx.types.Kind(operand.Type) is not (TypeKind.Int or TypeKind.Bool))
                return RecoveryDiagnostics.Fail(0, $"运算 {b.Op} 的操作数类型 {operand.Type}", rule: "Binary");
        return new BinaryValue(b.Op, left, right, ctx.IntegerOf(b.Width, b.Op == BinOp.SDiv || b.Op != BinOp.UDiv && ManagedTypes.IsSigned(left.Type)), b.Width);
    }

    internal static RecoveryResult<Fragment?> MaskFragment(this RecoveryScope ctx, Fragment fragment, ulong mask, int width)
    {
        ulong Bits(int low, int bits) => mask & (Expr.Mask(bits) << low);
        var parts = new List<Part>();
        var cursor = 0;
        foreach (var part in fragment.Parts.OrderBy(p => p.Low).Append(new Part(width, new ConstantValue(0, ctx.types.Int32, 0))))
        {
            // 填充必须整段被清；逐字节表示可覆盖 bool 与 int 之间的三字节间隔。
            if (part.Low > cursor)
            {
                var gap = part.Low - cursor;
                if (Bits(cursor, gap) != 0 || gap % 8 != 0)
                    return (Fragment?)null;
                for (var low = cursor; low < part.Low; low += 8)
                    parts.Add(new Part(low, new ConstantValue(0, ctx.types.Byte, 8)));
            }

            if (part.Low >= width)
                break;
            var leafMask = Bits(part.Low, part.Value.Width) >> part.Low;
            if (leafMask == Expr.Mask(part.Value.Width))
                parts.Add(part);
            else if (leafMask == 0)
                parts.Add(new Part(part.Low, new ConstantValue(0, ctx.types.Integer(part.Value.Width, false), part.Value.Width)));
            else
            {
                if (ctx.types.Kind(part.Value.Type) is not (TypeKind.Int or TypeKind.Bool))
                    return (Fragment?)null;
                var integer = ctx.types.Integer(part.Value.Width, false);
                if (!ctx.Coerce(part.Value, integer, 0).TryGet(out var converted, out var failure))
                    return failure;
                parts.Add(new Part(part.Low, new BinaryValue(BinOp.And, converted, new ConstantValue(leafMask, integer, part.Value.Width), integer, part.Value.Width)));
            }

            cursor = part.Low + part.Value.Width;
        }

        return new Fragment(parts, fragment.Type, width);
    }

    internal static RecoveryResult<ManagedValue> Comparison(this RecoveryScope ctx, Compare c)
    {
        RecoveryFailure failure;
        if (c.Cond is Cond.Eq or Cond.Ne && RuntimeRules.SealedOperands(c) is var (klass, sealedType) && ctx.State.Runtime.objectClasses.TryGetValue(klass, out var checkedObject))
            return ctx.Recover(checkedObject, ctx.types.Object).Map<ManagedValue>(value => new ComparisonValue(c.Cond == Cond.Eq ? Cond.Ne : Cond.Eq,
                new IsInstValue(value, sealedType, ctx.types.Object), new ConstantValue(0, ctx.types.Object, 64), ctx.types.Boolean));
        ManagedValue left, right;
        if (c.Left is Const && c.Right is not Const)
        {
            if (!ctx.Recover(c.Right, null).TryGet(out right, out failure))
                return failure;
            if (!ctx.Recover(c.Left, right.Type).TryGet(out left, out failure))
                return failure;
        }
        else
        {
            if (!ctx.Recover(c.Left, null).TryGet(out left, out failure))
                return failure;
            if (!ctx.Recover(c.Right, left.Type).TryGet(out right, out failure))
                return failure;
        }

        if (left is Fragment lf && !ctx.Pack(lf).TryGet(out left, out failure))
            return failure;
        if (right is Fragment rf && !ctx.Pack(rf).TryGet(out right, out failure))
            return failure;
        var reference = ctx.types.Kind(left.Type) == TypeKind.Reference || ctx.types.Kind(right.Type) == TypeKind.Reference;
        if (left.Type is GenericParameterRef { NativeScalar: not null } || right.Type is GenericParameterRef { NativeScalar: not null })
            return RecoveryDiagnostics.Fail(0, "泛型复制 不支持原生数值比较", rule: "Comparison");
        if (reference)
        {
            if (c.Cond is not (Cond.Eq or Cond.Ne))
                return RecoveryDiagnostics.Fail(0, $"比较 引用的 {c.Cond}", rule: "Comparison");
            if (ctx.types.Kind(left.Type) != TypeKind.Reference && left is not ConstantValue { Bits: 0 } || ctx.types.Kind(right.Type) != TypeKind.Reference && right is not ConstantValue { Bits: 0 })
                return RecoveryDiagnostics.Fail(0, "比较 引用与非引用", rule: "Comparison");
        }
        else if (left.Width != right.Width)
            return RecoveryDiagnostics.Fail(0, "比较 位宽不一致", rule: "Comparison");
        return new ComparisonValue(c.Cond, left, right, ctx.types.Boolean);
    }

    internal static RecoveryResult<ManagedValue> Conversion(this RecoveryScope ctx, Convert c, TypeRef? hint)
    {
        if (c.Kind == ConvKind.ZeroExtend && c.Operand is Use { Width: not (1 or 8 or 16 or 32 or 64) } narrow && Fold.ScalarExtract(new Extract(new Use(narrow.Variable, narrow.Variable.Width), 0, narrow.Width), c.Width) is { } extended)
            return ctx.Recover(extended, hint);
        if (c.Kind == ConvKind.ZeroExtend && c.Operand is Extract { Width: not (8 or 16 or 32 or 64) } extract && Fold.ScalarExtract(extract, c.Width) is { } scalar)
            return ctx.Recover(scalar, hint);
        if (!ctx.Recover(c.Operand, null).TryGet(out var operand, out var failure))
            return failure;
        if (operand.Type is GenericParameterRef { NativeScalar: not null })
        {
            if (c.Kind is ConvKind.ZeroExtend or ConvKind.Truncate && c.Width >= ctx.types.Bits(operand.Type))
                return new ConversionValue(c.Kind, operand, operand.Type, c.Width);
            return RecoveryDiagnostics.Fail(0, $"泛型复制 不支持 {c.Kind} 到 {c.Width} 位", rule: "Conversion");
        }

        if (operand is Fragment f)
        {
            if (c.Kind == ConvKind.Truncate)
                return ctx.Slice(f, 0, c.Width);
            if (c.Kind == ConvKind.ZeroExtend)
                return ctx.ResizeFragment(f, c.Width);
            if (!ctx.Pack(f).TryGet(out operand, out failure))
                return failure;
        }

        // 写入向量寄存器低位的值（S/D 读写清零高位）：只有低位是托管值，高位不属于任何叶子（如 HFA 实参的各片来自各自的 float 字段）。
        if (c.Kind == ConvKind.ZeroExtend && c.Width == 128 && (ctx.StructOrigin(c.Operand) || ctx.types.Kind(operand.Type) is TypeKind.Float or TypeKind.Double or TypeKind.Int or TypeKind.Bool))
            return ctx.ResizeFragment(new Fragment([new Part(0, operand)], ctx.types.UInt64, operand.Width), 128);
        switch (c.Kind)
        {
            case ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate:
                if (operand.Width == c.Width)
                    return operand;
                // 栈溢出的浮点寄存器按位保存为整数，扩展/截断作用于位型，不能当作数值转换。
                if (ctx.types.Kind(operand.Type) is TypeKind.Float or TypeKind.Double)
                    if (!ctx.Coerce(operand, ctx.types.Integer(operand.Width, false), 0).TryGet(out operand, out failure))
                        return failure;
                if (ctx.types.Kind(operand.Type) is not (TypeKind.Int or TypeKind.Bool))
                    return RecoveryDiagnostics.Fail(0, $"转换 {c.Kind} 的操作数类型 {operand.Type}", rule: "Conversion");
                if (c.Width is not (8 or 16 or 32 or 64))
                    return RecoveryDiagnostics.Fail(0, $"转换 位宽 {c.Width}", rule: "Conversion");
                return operand.Width == c.Width ? operand : new ConversionValue(c.Kind, operand, ctx.types.Integer(c.Width, c.Kind == ConvKind.SignExtend || c.Kind == ConvKind.Truncate && ManagedTypes.IsSigned(operand.Type)), c.Width);
            case ConvKind.SIntToFloat or ConvKind.UIntToFloat:
                return new ConversionValue(c.Kind, operand, c.Width == 32 ? ctx.types.Single : ctx.types.Double, c.Width);
            case ConvKind.FloatToFloat:
                return new ConversionValue(c.Kind, operand, c.Width == 32 ? ctx.types.Single : ctx.types.Double, c.Width);
            case ConvKind.FloatToSInt or ConvKind.FloatToUInt when c.Width is 32 or 64 && operand.Width is 32 or 64:
                return new ConversionValue(c.Kind, operand, ctx.types.Integer(c.Width, c.Kind == ConvKind.FloatToSInt), c.Width);
            case ConvKind.Bitcast:
                if (operand.Width != c.Width)
                    return RecoveryDiagnostics.Fail(0, "转换 位重解释的宽度不一致", rule: "Conversion");
                var floatHint = hint is not null && ctx.types.Kind(hint) is TypeKind.Float or TypeKind.Double;
                if (floatHint && operand.Type.Equals(hint))
                    return operand;
                var toFloat = ctx.types.Kind(operand.Type) is TypeKind.Int or TypeKind.Bool ? true : false;
                if (operand is ConstantValue k)
                    return new ConstantValue(k.Bits, floatHint ? hint! : c.Width == 32 ? ctx.types.Single : ctx.types.Double, c.Width);
                return new ConversionValue(c.Kind, operand, toFloat ? c.Width == 32 ? ctx.types.Single : ctx.types.Double : ctx.types.Integer(c.Width, false), c.Width);
            default:
                return RecoveryDiagnostics.Fail(0, $"转换 {c.Kind} 尚未支持（浮点转整数的饱和语义）", rule: "Conversion");
        }
    }
}
