using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<Storage, (ArgumentValue Root, AbiPiece Piece)> structArguments = new();
        private readonly Dictionary<Call, LocalValue> structResults = new(ReferenceEqualityComparer.Instance);
        private sealed record AggregatePiece(ManagedValue Root, int Offset, int Width) : ManagedValue(Root.Type, Width);

        private bool RegisterStruct(AbiValue value) => types.Kind(value.Type) == TypeKind.Struct
            && value.Passing == Passing.Registers && value.Pieces.All(p => p.Register.Bank is Bank.Gpr or Bank.Vec);

        [ParameterBinding(10)]
        private bool PrepareStructArgument(AbiValue parameter, int index)
        {
            if (!RegisterStruct(parameter)) return false;
            foreach (var piece in parameter.Pieces)
            {
                structArguments[piece.Register] = (new ArgumentValue(index, parameter.Type, 0), piece);
                arguments[piece.Register] = new(index, parameter.Type, piece.Width);
            }
            return true;
        }

        [ArgumentRule(5)]
        private ManagedValue? TypeHandleArgument(AbiValue parameter, ArgumentSite site) =>
            parameter.Type.Equals(types.RuntimeTypeHandle) && parameter.Passing == Passing.Registers
            && parameter.Pieces is [{ Width: 64, Offset: 0 } piece] && site.Registers.TryGetValue(piece.Register, out var value)
            && Expand(value) is Symbol { Kind: SymbolKind.Type, Value: TypeRef type }
                ? new TypeHandleValue(type, types.RuntimeTypeHandle, 64) : null;

        [ArgumentRule(10)]
        private RecoveryResult<ManagedValue?> RegisterStructArgument(AbiValue parameter, ArgumentSite site) => !RegisterStruct(parameter) ? (ManagedValue?)null
            : Compose(parameter, p => site.Registers.TryGetValue(p.Register, out var e) ? e : Fail(site.Call.Address, $"调用 缺少结构体片 {p.Register}")).Map<ManagedValue?>(value => value);

        [ResultRule(10)]
        private LocalValue? RegisterStructResult(Call call, AbiValue returned) => RegisterStruct(returned) ? CallStructLocal(call, returned.Type) : null;

        private LocalValue CallStructLocal(Call call, TypeRef type)
        {
            if (!structResults.TryGetValue(call, out var local)) structResults.Add(call, local = StructLocal(type, 0));
            return local;
        }

        private RecoveryResult<ManagedValue?> RegisterPiece(Variable variable, int width)
        {
            ManagedValue root;
            AbiPiece piece;
            if (variable.Version == 0 && structArguments.TryGetValue(variable.Storage, out var argument))
                (root, piece) = (argument.Root, argument.Piece);
            else if (results.TryGetValue(variable, out var result) && Resolve(result.Call) is { } callee
                && owner.abi.Classify(callee, out _)?.Return is { } returned && RegisterStruct(returned)
                && returned.Pieces.FirstOrDefault(p => p.Register == result.Call.Results[result.Index]) is { } found)
                (root, piece) = (CallStructLocal(result.Call, returned.Type), found);
            else return (ManagedValue?)null;
            var fragment = StructPiece(root, piece);
            if (width == fragment.Width) return fragment;
            if (width < fragment.Width) return Slice(fragment, 0, width).Map<ManagedValue?>(value => value);
            // 寄存器高位并非托管值的一部分；保留“没有叶子”的范围，只有明确截取叶子才可使用。
            return fragment is Fragment f ? ResizeFragment(f, width).Map<ManagedValue?>(value => value) : new Fragment([new Part(0, fragment)], types.UInt64, width);
        }

        private ManagedValue StructPiece(ManagedValue root, AbiPiece piece)
        {
            if (root.Type is GenericParameterRef { NativeAggregate: not null }) return new AggregatePiece(root, piece.Offset, piece.Width);
            var paths = StructPaths(root.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)
                && p.Offset >= piece.Offset && p.Offset + types.Size(p.Type) <= piece.Offset + piece.Width / 8).ToArray();
            var parts = paths.Select(p => new Part((p.Offset - piece.Offset) * 8, PathValue(root, p.Path))).ToArray();
            return parts is [var one] && one.Low == 0 && one.Value.Width == piece.Width ? one.Value
                : new Fragment(parts, types.UInt64, piece.Width);
        }

        private RecoveryResult<ManagedValue> Compose(AbiValue value, Func<AbiPiece, RecoveryResult<Expr>> expression)
        {
            if (!RegisterStruct(value)) return Fail(0, $"结构体 {value.Type} 的寄存器形态尚未支持");
            var pieces = new List<(AbiPiece Piece, ManagedValue Value)>();
            foreach (var piece in value.Pieces)
            {
                // ABI 片只读取声明的低位；间接调用的保守寄存器外壳可能仍是 128 位。
                if (!expression(piece).Bind(e => Recover(e.Width > piece.Width ? Fold.Convert(ConvKind.Truncate, e, piece.Width) : e, null))
                    .TryGet(out var recovered, out var failure)) return failure;
                pieces.Add((piece, recovered));
            }
            if (value.Type is GenericParameterRef { NativeAggregate: not null })
            {
                var parts = new List<(AbiPiece Piece, ManagedValue Value)>();
                foreach (var piece in pieces)
                {
                    if (!Slice(piece.Value, 0, piece.Piece.Width).TryGet(out var sliced, out var failure)) return failure;
                    parts.Add((piece.Piece, sliced));
                }
                if (parts.All(p => p.Value is AggregatePiece part && part.Offset == p.Piece.Offset && part.Width == p.Piece.Width)
                    && parts.Select(p => ((AggregatePiece)p.Value).Root).Distinct().ToArray() is [var root]
                    && root.Type.Equals(value.Type)) return root;
                if (parts.All(p => p.Value is ConstantValue { Bits: 0 })) return new ComposedValue(value.Type, []);
                return Fail(0, "泛型聚合片未能完整重建同一个值");
            }
            var leaves = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
            foreach (var path in StructPaths(value.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)))
            {
                var size = types.Size(path.Type);
                var matches = pieces.Where(p => path.Offset >= p.Piece.Offset && path.Offset + size <= p.Piece.Offset + p.Piece.Width / 8).ToArray();
                if (matches.Length != 1) return Fail(0, $"结构体 叶子 {path.Path.Last()} 不能唯一对应 ABI 片");
                var match = matches[0];
                if (!Slice(match.Value, (path.Offset - match.Piece.Offset) * 8, size * 8).Bind(v => Coerce(v, path.Type, 0)).TryGet(out var leaf, out var failure)) return failure;
                leaves.Add((path.Path, leaf));
            }
            // 参数/调用结果是不可变值根；逐叶子同源时直接整体传递，避免制造无必要的私有字段访问。
            foreach (var root in structArguments.Values.Select(p => (ManagedValue)p.Root).Concat(structResults.Values).Distinct())
                if (root.Type.Equals(value.Type) && leaves.All(l => l.Value.Equals(PathValue(root, l.Path)))) return root;
            // 叶子全是零：default(T)（initobj），不逐叶子写（可能是私有字段，如 CancellationToken._source）。
            if (leaves.All(l => l.Value is ConstantValue { Bits: 0 })) return new ComposedValue(value.Type, []);
            // 叶子全部读自同一个结构体位置（如 this.cancellationToken 的唯一私有字段 _source）：整体传递这个位置的值，不逐叶子读私有字段。
            if (leaves.Count > 0 && StructRoot(leaves[0].Value, leaves[0].Path) is { } location && location.Type.Equals(value.Type)
                && leaves.All(l => l.Value.Equals(PathValue(location, l.Path))))
                return location is LocalValue or ArgumentValue ? location : new IndirectValue(new AddressValue(location), value.Type);
            return new ComposedValue(value.Type, leaves);
        }

        /// <summary>叶子值 = PathValue(根, path) 时的根（逐层剥去字段与取址）。</summary>
        private static ManagedValue? StructRoot(ManagedValue leaf, IReadOnlyList<FieldRef> path)
        {
            var value = leaf;
            for (var i = path.Count - 1; i >= 0; i--)
            {
                if (value is not FieldValue field || !field.Field.Equals(path[i])) return null;
                value = field.Receiver is AddressValue address ? address.Target : field.Receiver;
            }
            return value;
        }

        private bool StructOrigin(Expr expression)
        {
            var seen = new HashSet<Variable>();
            bool Visit(Expr e)
            {
                if (e is Use u && seen.Add(u.Variable))
                {
                    if (u.Variable.Version == 0 && structArguments.ContainsKey(u.Variable.Storage)) return true;
                    if (results.TryGetValue(u.Variable, out var result) && Resolve(result.Call) is { } callee
                        && owner.abi.Classify(callee, out _)?.Return is { } r && RegisterStruct(r)) return true;
                    return values.TryGetValue(u.Variable, out var value) && Visit(value);
                }
                if (e is Load load)
                {
                    return Location(load.Address, load.Width).TryGet(out var value, out _)
                        && value is FieldValue { Field.DeclaringType: DefinitionRef { Definition.IsValueType: true } } or Fragment;
                }
                return e is Ir.Convert c && Visit(c.Operand);
            }
            return Visit(expression);
        }

        private RecoveryResult<ManagedValue> StructReturn(Expr expression)
        {
            var value = owner.abi.Classify(method, out _)!.Return!;
            if (IndirectStruct(value)) return ownReturnBuffer is { } buffer ? buffer : Fail(0, "返回值 x8 根未建立");
            var parts = expression is Intrinsic { Name: "diagnostic_return" } i ? i.Arguments : [expression];
            if (parts.Length != value.Pieces.Length) return Fail(0, "结构体 返回值片数不符");
            return Compose(value, p => parts[Array.IndexOf(value.Pieces, p)]);
        }
    }
}
