using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class StructRegistersRules
{
    internal static bool RegisterStruct(this RecoveryScope ctx, AbiValue value) => ctx.types.Kind(value.Type) == TypeKind.Struct && value.Passing == Passing.Registers && value.Pieces.All(p => p.Register.Bank is Bank.Gpr or Bank.Vec);
    [ParameterBinding(10)]
    internal static bool PrepareStructArgument(this RecoveryScope ctx, AbiValue parameter, int index)
    {
        if (ctx.types.Kind(parameter.Type) != TypeKind.Struct)
            return false;
        var pieces = parameter.Pieces;
        if (!ctx.RegisterStruct(parameter))
        {
            if (parameter.Passing != Passing.Stack || ctx.owner.abi.Hfa(parameter.Type) is not { } hfa || ctx.owner.abi.Classify(ctx.method, out _) is not { } signature || ctx.owner.abi.StackArguments(signature).Parameters.FirstOrDefault(p => p.Index == index) is not { Indirect: false } stack)
                return false;
            pieces = Enumerable.Range(0, hfa.Count).Select(i => new AbiPiece(Storage.Slot(stack.Offset + i * hfa.Width / 8), hfa.Width, i * hfa.Width / 8)).ToArray();
        }

        foreach (var piece in pieces)
        {
            ctx.State.Signature.structArguments[piece.Register] = (new ArgumentValue(index, parameter.Type, 0), piece);
            ctx.State.Signature.arguments[piece.Register] = new(index, parameter.Type, piece.Width);
        }

        return true;
    }

    [ArgumentRule(5)]
    internal static ManagedValue? TypeHandleArgument(this LoweringScope ctx, AbiValue parameter, ArgumentSite site) => parameter.Type.Equals(ctx.types.RuntimeTypeHandle) && parameter.Passing == Passing.Registers && parameter.Pieces is [{ Width: 64, Offset: 0 } piece] && site.Registers.TryGetValue(piece.Register, out var value) && ctx.Values.Expand(value) is Symbol { Kind: SymbolKind.Type, Value: TypeRef type } ? new TypeHandleValue(type, ctx.types.RuntimeTypeHandle, 64) : null;
    [ArgumentRule(10)]
    internal static RecoveryResult<ManagedValue?> RegisterStructArgument(this LoweringScope ctx, AbiValue parameter, ArgumentSite site) => !ctx.Values.RegisterStruct(parameter) ? (ManagedValue?)null : ctx.Values.Compose(parameter, p => site.Registers.TryGetValue(p.Register, out var e) ? e : RecoveryDiagnostics.Fail(site.Call.Address, $"调用 缺少结构体片 {p.Register}", rule: "RegisterStructArgument")).Map<ManagedValue?>(value => value);
    [ResultRule(10)]
    internal static LocalValue? RegisterStructResult(this LoweringScope ctx, Call call, AbiValue returned) => ctx.Values.RegisterStruct(returned) ? ctx.Values.CallStructLocal(call, returned.Type) : null;
    internal static LocalValue CallStructLocal(this RecoveryScope ctx, Call call, TypeRef type)
    {
        if (!ctx.State.Structs.structResults.TryGetValue(call, out var local))
            ctx.State.Structs.structResults.Add(call, local = ctx.StructLocal(type, 0));
        return local;
    }

    [InvocationOutputRule(30)]
    internal static bool ProjectTailHfa(this LoweringScope ctx, Call call, AbiSignature signature, Dictionary<Storage, Expr> registers, ManagedInvocation invocation, List<ManagedStatement> output)
    {
        if (call.Kind is not (CallKind.Tail or CallKind.TailIndirect) || signature.Return is not { } source
            || source.Type.Equals(ctx.State.Signature.returnType) || !ctx.Values.RegisterStruct(source)
            || new ManagedAbi(ctx.facts.Layouts).ClassifyReturn(ctx.State.Signature.returnType, out _) is not { Passing: Passing.Registers } target
            || source.Pieces.Any(p => p.Register.Bank != Bank.Vec) || target.Pieces.Length == 0
            || target.Pieces.Any(p => !source.Pieces.Any(s => s.Register == p.Register && s.Width == p.Width)))
            return false;
        // HFA 的各叶子独占浮点返回寄存器；调用者只观察自己返回签名中的寄存器。
        var sourcePaths = ctx.Values.StructPaths(source.Type).Where(p => ctx.types.Kind(p.Type) is TypeKind.Float or TypeKind.Double).ToArray();
        if (source.Pieces.Any(p => sourcePaths.Count(s => s.Offset == p.Offset && ctx.types.Bits(s.Type) == p.Width) != 1))
            return false;
        var local = ctx.Values.CallStructLocal(call, source.Type);
        ManagedValue Read(AbiPiece piece) => ctx.Values.PathValue(local, sourcePaths.Single(p => p.Offset == piece.Offset && ctx.types.Bits(p.Type) == piece.Width).Path);
        ManagedValue result;
        if (ctx.types.Kind(target.Type) is TypeKind.Float or TypeKind.Double)
            result = Read(source.Pieces.Single(p => p.Register == target.Pieces[0].Register));
        else
        {
            var paths = ctx.Values.StructPaths(target.Type).Where(p => ctx.types.Kind(p.Type) is TypeKind.Float or TypeKind.Double).ToArray();
            if (paths.Length != target.Pieces.Length || paths.Any(p => target.Pieces.Count(t => t.Offset == p.Offset && t.Width == ctx.types.Bits(p.Type)) != 1))
                return false;
            result = new ComposedValue(target.Type, paths.Select(p =>
            {
                var register = target.Pieces.Single(t => t.Offset == p.Offset).Register;
                return ((IReadOnlyList<FieldRef>)p.Path, Read(source.Pieces.Single(s => s.Register == register)));
            }).ToArray());
        }
        output.Add(new ManagedCall(call.Address, invocation, local, false));
        output.Add(new ManagedReturn(call.Address, result));
        return true;
    }

    internal static RecoveryResult<ManagedValue?> RegisterPiece(this RecoveryScope ctx, Variable variable, int width)
    {
        ManagedValue root;
        AbiPiece piece;
        if (variable.Version == 0 && ctx.State.Signature.structArguments.TryGetValue(variable.Storage, out var argument))
            (root, piece) = (argument.Root, argument.Piece);
        else if (ctx.results.TryGetValue(variable, out var result) && ctx.Resolve(result.Call) is { } callee && ctx.owner.abi.Classify(callee, out _)?.Return is { } returned && ctx.RegisterStruct(returned) && returned.Pieces.FirstOrDefault(p => p.Register == result.Call.Results[result.Index]) is { } found)
            (root, piece) = (ctx.CallStructLocal(result.Call, returned.Type), found);
        else
            return (ManagedValue?)null;
        var fragment = ctx.StructPiece(root, piece);
        if (width == fragment.Width)
            return fragment;
        if (width < fragment.Width)
            return ctx.Slice(fragment, 0, width).Map<ManagedValue?>(value => value);
        // 寄存器高位并非托管值的一部分；保留“没有叶子”的范围，只有明确截取叶子才可使用。
        return fragment is Fragment f ? ctx.ResizeFragment(f, width).Map<ManagedValue?>(value => value) : new Fragment([new Part(0, fragment)], ctx.types.UInt64, width);
    }

    internal static ManagedValue StructPiece(this RecoveryScope ctx, ManagedValue root, AbiPiece piece)
    {
        if (root.Type is GenericParameterRef { NativeAggregate: not null })
            return new AggregatePiece(root, piece.Offset, piece.Width);
        var paths = ctx.ScalarStructPaths(root.Type).Where(p => p.Offset >= piece.Offset && p.Offset + ctx.types.Size(p.Type) <= piece.Offset + piece.Width / 8).ToArray();
        var parts = paths.Select(p => new Part((p.Offset - piece.Offset) * 8, ctx.PathValue(root, p.Path))).ToArray();
        return parts is [var one] && one.Low == 0 && one.Value.Width == piece.Width ? one.Value : new Fragment(parts, ctx.types.UInt64, piece.Width);
    }

    internal static RecoveryResult<ManagedValue> Compose(this RecoveryScope ctx, AbiValue value, Func<AbiPiece, RecoveryResult<Expr>> expression)
    {
        if (!ctx.RegisterStruct(value))
            return RecoveryDiagnostics.Fail(0, $"结构体 {value.Type} 的寄存器形态尚未支持", rule: "Compose");
        // 已知空布局没有可观察的实例字段，返回寄存器中的填充不参与值重组。
        if (value.Type is DefinitionRef empty && ctx.facts.Layouts.Of(empty) is { Fields.Count: 0 })
            return new ComposedValue(value.Type, []);
        var pieces = new List<(AbiPiece Piece, ManagedValue Value)>();
        foreach (var piece in value.Pieces)
        {
            // ABI 片只读取声明的低位；间接调用的保守寄存器外壳可能仍是 128 位。
            if (!expression(piece).Bind(e => ctx.Recover(e.Width > piece.Width ? Fold.Convert(ConvKind.Truncate, e, piece.Width) : e, null)).TryGet(out var recovered, out var failure))
                return failure;
            pieces.Add((piece, recovered));
        }

        if (value.Type is GenericParameterRef { NativeAggregate: not null })
        {
            var parts = new List<(AbiPiece Piece, ManagedValue Value)>();
            foreach (var piece in pieces)
            {
                if (!ctx.Slice(piece.Value, 0, piece.Piece.Width).TryGet(out var sliced, out var failure))
                    return failure;
                parts.Add((piece.Piece, sliced));
            }

            if (parts.All(p => p.Value is AggregatePiece part && part.Offset == p.Piece.Offset && part.Width == p.Piece.Width) && parts.Select(p => ((AggregatePiece)p.Value).Root).Distinct().ToArray() is [var root] && root.Type.Equals(value.Type))
                return root;
            if (parts.All(p => p.Value is ConstantValue { Bits: 0 }))
                return new ComposedValue(value.Type, []);
            return RecoveryDiagnostics.Fail(0, "泛型聚合片未能完整重建同一个值", rule: "Compose");
        }

        var leaves = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        foreach (var path in ctx.ScalarStructPaths(value.Type))
        {
            var size = ctx.types.Size(path.Type);
            var matches = pieces.Where(p => path.Offset >= p.Piece.Offset && path.Offset + size <= p.Piece.Offset + p.Piece.Width / 8).ToArray();
            if (matches.Length != 1)
                return RecoveryDiagnostics.Fail(0, $"结构体 叶子 {path.Path.Last()} 不能唯一对应 ABI 片", rule: "Compose");
            var match = matches[0];
            if (!ctx.Slice(match.Value, (path.Offset - match.Piece.Offset) * 8, size * 8).Bind(v => ctx.Coerce(v, path.Type, 0)).TryGet(out var leaf, out var failure))
                return failure;
            leaves.Add((path.Path, leaf));
        }

        // 参数/调用结果是不可变值根；逐叶子同源时直接整体传递，避免制造无必要的私有字段访问。
        foreach (var root in ctx.State.Signature.structArguments.Values.Select(p => (ManagedValue)p.Root).Concat(ctx.State.Structs.structResults.Values).Distinct())
            if (root.Type.Equals(value.Type) && leaves.All(l => l.Value.Equals(ctx.PathValue(root, l.Path))))
                return root;
        // 叶子全是零：default(T)（initobj），不逐叶子写（可能是私有字段，如 CancellationToken._source）。
        if (leaves.All(l => l.Value is ConstantValue { Bits: 0 }))
            return new ComposedValue(value.Type, []);
        // 叶子全部读自同一个结构体位置（如 this.cancellationToken 的唯一私有字段 _source）：整体传递这个位置的值，不逐叶子读私有字段。
        if (leaves.Count > 0 && StructRegistersRules.StructRoot(leaves[0].Value, leaves[0].Path) is { } location && location.Type.Equals(value.Type) && leaves.All(l => l.Value.Equals(ctx.PathValue(location, l.Path))))
            return location is LocalValue or ArgumentValue ? location : new IndirectValue(new AddressValue(location), value.Type);
        return new ComposedValue(value.Type, leaves);
    }

    /// <summary>叶子值 = PathValue(根, path) 时的根（逐层剥去字段与取址）。</summary>
    internal static ManagedValue? StructRoot(ManagedValue leaf, IReadOnlyList<FieldRef> path)
    {
        var value = leaf;
        for (var i = path.Count - 1; i >= 0; i--)
        {
            if (value is not FieldValue field || !field.Field.Equals(path[i]))
                return null;
            value = field.Receiver is AddressValue address ? address.Target : field.Receiver;
        }

        return value;
    }

    internal static bool StructOrigin(this RecoveryScope ctx, Expr expression)
    {
        var seen = new HashSet<Variable>();
        bool Visit(Expr e)
        {
            if (e is Use u && seen.Add(u.Variable))
            {
                if (u.Variable.Version == 0 && ctx.State.Signature.structArguments.ContainsKey(u.Variable.Storage))
                    return true;
                if (ctx.results.TryGetValue(u.Variable, out var result) && ctx.Resolve(result.Call) is { } callee && ctx.owner.abi.Classify(callee, out _)?.Return is { } r && ctx.RegisterStruct(r))
                    return true;
                return ctx.values.TryGetValue(u.Variable, out var value) && Visit(value);
            }

            if (e is Load load)
            {
                return ctx.Location(load.Address, load.Width).TryGet(out var value, out _) && value is FieldValue { Field.DeclaringType: DefinitionRef { Definition.IsValueType: true } } or Fragment;
            }

            return e is Ir.Convert c && Visit(c.Operand);
        }

        return Visit(expression);
    }

    internal static RecoveryResult<ManagedValue> StructReturn(this RecoveryScope ctx, Expr expression)
    {
        var value = ctx.owner.abi.Classify(ctx.method, out _)!.Return!;
        if (ctx.IndirectStruct(value))
            return ctx.State.Signature.ownReturnBuffer is { } buffer ? buffer : RecoveryDiagnostics.Fail(0, "返回值 x8 根未建立", rule: "StructReturn");
        var parts = expression is Intrinsic { Name: "diagnostic_return" } i ? i.Arguments : [expression];
        if (parts.Length != value.Pieces.Length)
            return RecoveryDiagnostics.Fail(0, "结构体 返回值片数不符", rule: "StructReturn");
        return ctx.Compose(value, p => parts[Array.IndexOf(value.Pieces, p)]);
    }
}
