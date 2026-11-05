using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

internal sealed record TypeUsePlan(TypeSolveState State, IReadOnlySet<ReadSym> Materialized);

/// <summary>从 ABI、位置与值的用途收集约束和读取落点；不生成托管节点，也不调用下降器或构造模板。</summary>
internal sealed class TypeUseAnalysis(MethodAnalysis analysis, TypeOracle oracle)
{
    private readonly ValueModel values = analysis.Values;
    private ManagedTypes Types => oracle.Types;
    private readonly Queue<(Sym Value, TypeRef? Type, Stmt? User)> pending = [];
    private readonly HashSet<(Sym Value, TypeRef? Type, Stmt? User)> visited = [];
    private readonly HashSet<ReadSym> materialized = [];

    public TypeUsePlan Run()
    {
        while (true)
        {
            visited.Clear();
            materialized.Clear();
            foreach (var statement in analysis.Function.Blocks.SelectMany(b => b.Statements)) Roots(statement);
            while (pending.TryDequeue(out var use)) Visit(use.Value, use.Type, use.User);
            var state = oracle.Solve();
            if (state != TypeSolveState.Changed) return new(state, materialized.ToHashSet());
        }
    }

    private void Use(Sym value, TypeRef? type, Stmt? user)
    {
        value = SymTable.Resolve(value);
        if (visited.Add((value, type, user))) pending.Enqueue((value, type, user));
    }

    private void Roots(Stmt statement)
    {
        var operands = values.Operands(statement);
        switch (statement)
        {
            case Store store:
                if (oracle.StoreGroupOf(store) is { } group)
                {
                    if (ReferenceEquals(group.Members[0], store)) Store(group.Target, group.Value, store);
                }
                else if (oracle.Locate(operands[0], store.Value.Width) is { } location) Store(location, operands[1], store);
                else if (oracle.Split(operands[0], store.Value.Width) is { } parts)
                    foreach (var part in parts) Store(part.Leaf, values.Syms.Slice(operands[1], part.Bit, part.Width), store);
                break;
            case Branch:
                Use(operands[0], Types.Boolean, statement);
                break;
            case Return ret when !ManagedTypes.IsVoid(oracle.ReturnType) && ret.Pieces.Length > 0:
                Use(values.ReturnContent(ret, operands, analysis.Signature.Return is { } r
                    ? MethodEnvironment.ValueWidth(r) : Types.ValueWidth(oracle.ReturnType)), oracle.ReturnType, ret);
                break;
            case IndirectJump { Targets.Length: > 0 } when oracle.TableIndex(operands[0]) is { } index:
                Use(index, Types.Int32, statement);
                break;
            case Call call:
                Call(call, operands);
                break;
        }
    }

    private void Store(Location location, Sym value, Stmt user)
    {
        Location(location, user);
        var type = oracle.TypeOf(value) is { } source && oracle.Inside(location.Type, source) is not null ? source : location.Type;
        Use(value, type, user);
    }

    private void Call(Call call, IReadOnlyList<Sym> operands)
    {
        var arguments = operands.Skip(1).Take(call.Arguments.Length).ToArray();
        var shape = analysis.Environment.Shape(call);
        if (call.Op is { } op && shape.IsRuntime)
        {
            foreach (var input in RuntimeOps.Of(op.Kind)?.Inputs?.Invoke(call, arguments.Take(call.OriginalArgumentCount).ToArray(), oracle) ?? [])
            {
                if (input.Kind == RuntimeInputKind.Value) Use(input.Value, input.Type, call);
                else if (input.Kind == RuntimeInputKind.Pointee && values.CellContent(call, input.Pointee, arguments, false) is { } content)
                    Use(content, input.Type, call);
                else if (input.Type is { } type && oracle.Locate(input.Value, Types.StorageBits(type)) is { } location) Location(location, call);
            }
            return;
        }
        if (shape.Signature is not { } signature || oracle.Callee(call) is not { } callee) return;
        var contents = signature.Arguments.Select(p => values.ArgumentContent(call, p, arguments)).ToArray();
        var construction = callee.Method.Name == ".ctor" && !callee.Method.IsStatic && contents.Length > 0
            && SymTable.Resolve(contents[0]) is ResultSym { Site.Op.Kind: OpKind.NewObject };
        foreach (var (parameter, content) in signature.Arguments.Zip(contents))
        {
            var type = TypeOracle.ArgumentType(call, callee, parameter.Index);
            if (construction && parameter.Index < 0) continue;
            if (construction && parameter.Index == 1 && DelegateFacts.IsDelegate(callee.DeclaringType)
                && oracle.DelegateTargetOf(content, contents[Array.FindIndex(signature.Arguments, p => p.Index == 0)]) is { } target)
            {
                Delegate(target);
                continue;
            }
            if (parameter.Index < 0 && call.Op?.Kind == OpKind.CallDelegate && call.DelegateReceiver is not null)
            {
                Use(operands[1 + call.Arguments.Length], type, call);
                continue;
            }
            // 未使用的 ABI 槽没有类型用途，也不应迫使无关读取落地。
            if (oracle.Supply(shape, parameter, type, content) != ArgumentSupply.Content) continue;
            if (parameter.Transfer == Transfer.Value) Use(content, type, call);
            else
            {
                var element = type is ByRefRef byRef ? byRef.Element : type;
                if (values.CellContent(call, parameter, arguments, false) is { } before) Use(before, element, call);
                if (oracle.Locate(content, parameter.Size < 0 ? -1 : Math.Max(8, parameter.Size * 8)) is { } location) Location(location, call);
                else Use(content, type is ByRefRef ? type : new ByRefRef(type), call);
            }
        }

        void Delegate(DelegateTarget target)
        {
            if (target is not SelectedDelegateTarget selected) return;
            Use(selected.Condition, Types.Boolean, call);
            Delegate(selected.True);
            Delegate(selected.False);
        }
    }

    private void Location(Location location, Stmt? user)
    {
        if (location.Base is { } root && location.Kind != LocationKind.Local)
        {
            var type = oracle.TypeOf(root);
            type ??= location.Kind switch
            {
                LocationKind.StringLength or LocationKind.StringChar => Types.String,
                LocationKind.Instance when location.Path.Count > 0 => location.Path[0].DeclaringType,
                LocationKind.Reference => new ByRefRef(location.Path.Count > 0 ? location.Path[0].DeclaringType : location.Type),
                _ => null,
            };
            Use(root, type, user);
        }
        if (location.Index is { } index)
        {
            index = TypeOracle.ArrayIndex(index);
            Use(index, index.Width == 32 ? Types.Int32 : Types.Int64, user);
        }
        if (location.ByteOffset is { } offset) Use(offset, Types.Int64, user);
    }

    private void Read(ReadSym read, Stmt? user)
    {
        if (!ReferenceEquals(read.Site, user)) materialized.Add(read);
        if (oracle.Locate(read.Address, read.Width) is { } location) Location(location, user);
        else if (oracle.NarrowRead(read) is { } narrow) Location(narrow.Leaf, user);
    }

    private void Visit(Sym value, TypeRef? expected, Stmt? user)
    {
        if (oracle.AddressArm(value, expected) is { } addressed) { Location(addressed, user); return; }
        if (expected is DefinitionRef structure && Types.Kind(expected) == TypeKind.Struct
            && (value is ConcatSym || oracle.BitRepresentation(value)) && oracle.Aggregate(value, structure) is { } aggregate)
        {
            if (aggregate.Whole is { } whole && !ReferenceEquals(whole, value)) { Use(whole, structure, user); return; }
            if (aggregate.Whole is null)
            {
                foreach (var field in aggregate.Fields) Use(field.Value, field.Projection.Type, user);
                return;
            }
        }
        switch (value)
        {
            case ReadSym read:
                Read(read, user);
                break;
            case PhiSym phi:
                if (oracle.ProjectedField(phi) is var (whole, type, _, _)) { Use(whole, type, user); break; }
                if (oracle.ProjectedScalar(phi) is var (scalar, scalarType, _)) { Use(scalar, scalarType, user); break; }
                if (expected is not null) oracle.Use(phi, expected);
                var phiType = oracle.TypeOf(phi) ?? expected ?? oracle.Unconstrained(phi.Width);
                foreach (var source in phi.Sources.OfType<Sym>()) Use(source, phiType, null);
                break;
            case OpSym op when oracle.PinnedArray(op) is var (array, arrayType):
                // fixed 不读取长度也不判空，长度的读取保持在原处，空数组引用在那里抛出。
                Use(array, arrayType, user);
                Use(op.Args[0], Types.Boolean, user);
                break;
            case OpSym op:
                if (op.Op.Kind == OperatorKind.Compare && op.Op.Cond is Cond.Eq or Cond.Ne
                    && oracle.ClassIdentity(op.Args[0], op.Args[1]) is var (owner, _)) { Use(owner, Types.Object, user); break; }
                var typing = oracle.OperationTypes(op, expected);
                for (var i = 0; i < op.Args.Length; i++) Use(op.Args[i], typing.Inputs[i], user);
                break;
            case SliceSym slice:
                if (oracle.UntypedWidePhiPiece(slice) is { } widePiece) { Use(widePiece, expected, user); break; }
                if (oracle.EnclosingScalar(slice) is { } enclosing) { Use(enclosing.Value, enclosing.Type, user); break; }
                if (slice.Base is ReadSym merged && oracle.Part(merged, slice.Low, slice.Width) is { } part)
                {
                    if (!ReferenceEquals(merged.Site, user)) materialized.Add(merged);
                    Location(part, user);
                    break;
                }
                if (oracle.FieldPieces(slice) is { } pieces)
                {
                    foreach (var (_, piece) in pieces) Use(piece, oracle.TypeOf(piece) ?? oracle.Unconstrained(piece.Width), user);
                    break;
                }
                Use(slice.Base, oracle.TypeOf(slice.Base) ?? oracle.Unconstrained(slice.Base.Width), user);
                break;
            case ConcatSym concat:
                if (oracle.CompositeRead(concat) is { } joined) { Use(joined, expected, user); break; }
                foreach (var piece in concat.Parts)
                    Use(piece, oracle.TypeOf(piece) ?? oracle.Unconstrained(piece.Width) ?? expected, user);
                break;
        }
    }
}
