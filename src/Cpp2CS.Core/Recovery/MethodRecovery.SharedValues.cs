using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<ulong, LocalValue> sharedBuffers = [];
        private readonly Dictionary<Storage, ArgumentValue> sharedIncoming = [];

        [ParameterBinding(15)]
        private bool PrepareSharedArgument(AbiValue parameter, int index)
        {
            if (parameter.Passing != Passing.Shared) return false;
            sharedIncoming.Add(parameter.Pieces.Single().Register, new(index, parameter.Type, 0));
            return true;
        }

        // fully shared 的 T 只经有类型的存储复制；不为它猜测寄存器宽度或对象布局。
        private void NormalizeSharedValues()
        {
            var original = function.Blocks.SelectMany(b => b.Statements).ToArray();
            if (!original.OfType<Define>().Any(d => ExprMap.Walk(d.Value).Any(e => e is Load
                { Address: Binary { Left: Symbol { Kind: SymbolKind.Class, Value: GenericParameterRef }, Right: Const { Value: RuntimeLayout.ClassStackSlotSize } } }))) return;
            var defs = original.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            foreach (var init in original.OfType<Call>().Where(c => c is { Op.Kind: OpKind.InitClass, Arguments.Length: 1, Defines.Length: 1 }))
                defs[init.Defines[0]] = init.Arguments[0];
            var joins = original.OfType<Phi>().ToDictionary(p => p.Target);
            var singleStores = original.OfType<Store>().Where(s => s.Target is FrameAddress).GroupBy(s => ((FrameAddress)s.Target).Offset)
                .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
            var positions = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i)))
                .ToDictionary(p => p.Statement, (IEqualityComparer<Stmt>)ReferenceEqualityComparer.Instance);
            var dominators = Ssa.Dominators.Compute(function);
            Expr ExpandValue(Expr e, int depth = 0) => depth > 24 ? e : ExprMap.Map(e,
                p => p is Use u && defs.TryGetValue(u.Variable, out var value) ? ExpandValue(value, depth + 1) : null);
            Expr Scalar(Expr e)
            {
                e = ExpandValue(e);
                while (e is Convert c) e = c.Operand;
                return e;
            }
            Variable? Incoming(Expr value, Block block, int index)
            {
                value = ExpandValue(value);
                if (value is Load { Width: 64, Address: FrameAddress slot } && singleStores.TryGetValue(slot.Offset, out var saved)
                    && saved.Value.Width == 64 && positions[saved] is var at && dominators.Dominates(at.Block.Index, block.Index)
                    && (at.Block != block || at.Index < index)) value = ExpandValue(saved.Value);
                return value is Use { Width: 64, Variable.Version: 0 } use ? use.Variable : null;
            }
            TypeRef? SizeType(Expr e, int depth = 0)
            {
                if (depth > 24) return null;
                e = ExpandValue(e);
                while (e is Convert c) e = c.Operand;
                if (e is Load { Address: FrameAddress slot } && singleStores.TryGetValue(slot.Offset, out var stored)) return SizeType(stored.Value, depth + 1);
                return e is Load { Width: 32, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: GenericParameterRef type }, Right: Const { Value: RuntimeLayout.ClassStackSlotSize } } }
                    ? type : null;
            }
            TypeRef? AddressType(Expr e, int depth = 0) => depth > 24 ? null : ExpandValue(e) switch
            {
                Intrinsic { Name: "managed_generic_buffer" or "managed_generic_argument", Arguments: [Symbol { Value: TypeRef type }, _] } => type,
                Intrinsic { Name: "managed_field_address", Arguments: [_, Symbol { Value: FieldRef field }] } => FieldType(field),
                Use { Variable: { Version: 0 } variable } when indirectRoots.TryGetValue(variable.Storage, out var root) && root.Type is ByRefRef reference => reference.Element,
                Use { Variable: { Version: 0 } variable } when arguments.TryGetValue(variable.Storage, out var argument) && argument.Type is ByRefRef reference => reference.Element,
                Load { Address: FrameAddress frame } when singleStores.TryGetValue(frame.Offset, out var store) => AddressType(store.Value, depth + 1),
                Use u when joins.TryGetValue(u.Variable, out var phi) && phi.Sources.Length > 0
                    && phi.Sources.Select(v => AddressType(new Use(v, v.Width), depth + 1)).Distinct().ToArray() is [TypeRef type] => type,
                _ => null,
            };
            Dictionary<long, Store> InvokerStores(Block block, int index)
            {
                var stores = new Dictionary<long, Store>();
                var seen = new HashSet<Block>();
                while (seen.Count < 32 && seen.Add(block))
                {
                    foreach (var statement in block.Statements.Take(index).Reverse())
                    {
                        if (statement is Call || statement is Store { Target: not FrameAddress }) return stores;
                        if (statement is Store { Target: FrameAddress slot } store) stores.TryAdd(slot.Offset, store);
                    }
                    if (block.Predecessors.ToArray() is not [var parent] || parent.Handler == block
                        || parent.NormalSuccessors.ToArray() is not [var next] || next != block) break;
                    block = parent;
                    index = block.Statements.Count;
                }
                return stores;
            }
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Define define || ExpandValue(define.Value) is not Binary
                        { Op: BinOp.Sub, Left: FrameAddress or Intrinsic { Name: "managed_generic_buffer" or "managed_box_scratch" },
                          Right: Binary { Op: BinOp.And, Left: Binary { Op: BinOp.Add, Left: var size, Right: Const { Value: 15 } }, Right: Const { Value: 0x1fffffff0 } } }) continue;
                    var scratch = Scalar(size) is Binary { Op: BinOp.Add, Width: 32, Left: var payload, Right: Const { Value: RuntimeLayout.ObjectHeaderSize } }
                        && SizeType(payload) is { };
                    var type = SizeType(scratch ? ((Binary)Scalar(size)).Left : size);
                    if (type is null) continue;
                    var buffer = new Intrinsic(scratch ? "managed_box_scratch" : "managed_generic_buffer", [new Symbol(SymbolKind.Type, type), Expr.C(define.Address, 64)], 64);
                    if (!scratch) sharedBuffers[define.Address] = StructLocal(type, 0);
                    block.Statements[i] = define with { Value = buffer };
                    defs[define.Target] = buffer;
                }
            if (sharedBuffers.Count == 0) return;

            // 完全共享入参：值类型直接使用传入地址，引用类型使用寄存器的栈副本地址。
            foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Define define || ExpandValue(define.Value) is not Select
                    { Condition: Compare { Cond: Cond.Slt, Left: var bits, Right: Const { Value: 0 } },
                      True: var selected, False: FrameAddress slot }
                    || Incoming(selected, block, i) is not { } incoming
                    || Scalar(bits) is not Load { Width: 32, Address: Binary { Op: BinOp.Add,
                        Left: Symbol { Kind: SymbolKind.Class, Value: GenericParameterRef generic }, Right: Const { Value: 0x28 } } }
                    || !sharedIncoming.TryGetValue(incoming.Storage, out var argument) || !argument.Type.Equals(generic)
                    || !singleStores.TryGetValue(slot.Offset, out var saved) || saved.Value is not Use { Width: 64 } copy || copy.Variable != incoming) continue;
                var address = new Intrinsic("managed_generic_argument", [new Symbol(SymbolKind.Type, generic), Expr.C((ulong)incoming.Storage.Index, 64)], 64);
                block.Statements[i] = define with { Value = address };
                defs[define.Target] = address;
            }

            // invoker 对引用 T 传对象、对值 T 传地址；两条路径在托管侧都是同一个 T 值。
            foreach (var block in function.Blocks.ToArray())
            {
                if (block.Statements.LastOrDefault() is not Branch branch || ExpandValue(branch.Condition) is not Compare
                    { Cond: Cond.Ne, Left: Binary { Op: BinOp.And, Left: var bits, Right: Const { Value: 0x80000000 } }, Right: Const { Value: 0 } }
                    || Scalar(bits) is not Load { Width: 32, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef generic }, Right: Const { Value: 0x28 } } }
                    || block.NormalSuccessors.ToArray() is not [var join, var reference]
                    || join.Start != branch.Target || reference.Start != branch.Fallthrough || reference.Successors.ToArray() is not [var next] || next != join
                    || reference.Statements.OfType<Define>().ToArray() is not [var load]
                    || ExpandValue(load.Value) is not Load { Width: 64, Address: var buffer } || !Equals(AddressType(buffer), generic)
                    || reference.Statements.Any(s => s is not (Define or Jump or Nop))) continue;
                var direct = MachineFunction.PredecessorIndex(block, 0);
                var indirect = MachineFunction.PredecessorIndex(reference, 0);
                if (!join.Statements.OfType<Phi>().All(p => p.Sources[direct] == p.Sources[indirect]
                    || p.Sources[indirect] == load.Target && ExpandValue(new Use(p.Sources[direct], 64)) == buffer)) continue;
                block.Statements[^1] = new Jump(branch.Address, join.Start);
                MachineFunction.RemoveEdgeAt(block, 1);
            }
            function.Renumber();
            NormalizeStackCanary(ExpandValue);
            Ssa.Propagate.Run(function, Ssa.Dominators.Compute(function));
            defs = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            joins = function.Blocks.SelectMany(b => b.Statements).OfType<Phi>().ToDictionary(p => p.Target);

            foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: null, Kind: CallKind.Direct, Target: Const target } call) continue;
                bool UnusedResultsExcept(Stmt? allowed) => function.Blocks.SelectMany(b => b.Statements)
                    .Where(s => !ReferenceEquals(s, allowed)).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk)
                    .OfType<Use>().All(u => !call.Defines.Contains(u.Variable));
                if (call.Arguments is [var obj, Symbol { Kind: SymbolKind.Class, Value: GenericParameterRef type }, var temporary, ..]
                    && Equals(AddressType(temporary), type) && call.Defines.FirstOrDefault() is { } pointer
                    && i + 1 < block.Statements.Count && block.Statements[i + 1] is Call
                    { Op: { Kind: OpKind.Import, Operand: "memcpy" }, Arguments: [var destination, Use copied, var count] } copy
                    && copied.Variable == pointer && Equals(SizeType(count), type) && Equals(AddressType(destination), type)
                    && UnusedResultsExcept(copy) && SharedRuntimeHelpers.UnboxAny(facts, target.Value))
                {
                    block.Statements[i] = call with { Op = new(OpKind.UnboxGenericValue, type), Arguments = [destination, obj],
                        Sources = [], Defines = [], Results = [], Target = Expr.C(0, 64) };
                    block.Statements[i + 1] = copy.Defines is [var result]
                        ? new Define(copy.Address, result, destination) : new Nop(copy.Address, "拆箱值复制");
                    sharedSites.Add(call.Address); sharedSites.Add(copy.Address);
                }
                else if (call.Arguments is [Symbol { Kind: SymbolKind.Class, Value: GenericParameterRef constraint },
                    Symbol { Kind: SymbolKind.Constrained, Value: ValueTuple<TypeRef, MethodRef> dispatch }, var scratch, var receiver, Const { Value: 0 }, FrameAddress returned, ..]
                    && Equals(dispatch.Item1, constraint) && Equals(AddressType(receiver), constraint)
                    && ExpandValue(scratch) is Intrinsic { Name: "managed_box_scratch", Arguments: [Symbol { Value: TypeRef scratchType }, _] }
                    && Equals(scratchType, constraint) && dispatch.Item2.Method is { IsStatic: false, Parameters.Count: 0 }
                    && Concrete(dispatch.Item2, dispatch.Item2.Method.ReturnType) is { } resultType && ManagedTypes.IsReferenceType(resultType)
                    && UnusedResultsExcept(null) && SharedRuntimeHelpers.ConstrainedInvoke(facts, target.Value))
                {
                    var result = StructLocal(resultType, 64).Variable;
                    block.Statements[i] = call with { Op = new(OpKind.InvokeConstrainedGeneric, dispatch.Item2),
                        Arguments = [new Symbol(SymbolKind.Type, constraint), receiver], Sources = [], Defines = [result], Results = [], Target = Expr.C(0, 64) };
                    block.Statements.Insert(++i, new Store(call.Address, returned, new Use(result, 64)));
                    sharedSites.Add(call.Address);
                }
            }

            // 不同分支选择不同的 MethodInfo/实参后汇入同一个 invoker；调用分别留在原分支上。
            foreach (var block in function.Blocks.ToArray())
            {
                var calls = block.Statements.OfType<Call>().Where(c => c.Kind == CallKind.Indirect && c.Arguments.Length >= 5).ToArray();
                if (function.Range.ExceptionRegions.Length != 0 || calls is not [var call] || call.Arguments[1] is not Use methodUse || call.Arguments[3] is not FrameAddress array
                    || block.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == methodUse.Variable) is not { } methodPhi
                    || block.Predecessors.Any(p => p.NormalSuccessors.ToArray() is not [var next] || next != block)) continue;
                var before = block.Statements.Take(block.Statements.IndexOf(call)).ToArray();
                if (before.Any(s => s is not (Phi or Define or Nop or Store { Target: FrameAddress }))) continue;
                var stores = before.OfType<Store>().GroupBy(s => ((FrameAddress)s.Target).Offset).ToDictionary(g => g.Key, g => g.Last());
                var replacements = new List<(Block Block, Call Call)>();
                for (var side = 0; side < block.Predecessors.Count; side++)
                {
                    Expr OnEdge(Expr expression) => ExprMap.Map(expression, e => e is Use use
                        && block.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == use.Variable) is { } phi ? new Use(phi.Sources[side], use.Width) : null);
                    Expr Identity(Expr expression) => ExpandValue(OnEdge(ExpandValue(expression)));
                    // 地址合流归约后，方法指针可能已经在各前驱加载；逐边同时核对三者的身份。
                    if (GenericInvokerIdentity.Match(Identity(call.Target), Identity(call.Arguments[0]), Identity(call.Arguments[1])) is not { } callee) break;
                    var returned = Concrete(callee, callee.Method.ReturnType);
                    if (!Equals(AddressType(call.Arguments[4]), returned)) break;
                    var args = new List<Expr> { OnEdge(call.Arguments[2]) };
                    for (var p = 0; p < callee.Method.Parameters.Count; p++)
                    {
                        if (!stores.TryGetValue(array.Offset + p * 8, out var store)) break;
                        var type = Concrete(callee, callee.Method.Parameters[p].Type);
                        if (!ManagedTypes.IsReferenceType(type)) break;
                        args.Add(OnEdge(store.Value));
                    }
                    if (args.Count != callee.Method.Parameters.Count + 1) break;
                    args.Add(call.Arguments[4]);
                    replacements.Add((block.Predecessors[side], call with { Op = new(OpKind.InvokeGeneric, callee), Arguments = args.ToArray(),
                        Sources = [], Defines = [], Results = [], Target = Expr.C(0, 64) }));
                }
                if (replacements.Count != block.Predecessors.Count) continue;
                foreach (var (predecessor, replacement) in replacements)
                    predecessor.Statements.Insert(predecessor.Statements.LastOrDefault() is Jump ? predecessor.Statements.Count - 1 : predecessor.Statements.Count, replacement);
                block.Statements.Remove(call);
                foreach (var store in stores.Values.Where(s => ((FrameAddress)s.Target).Offset >= array.Offset
                    && ((FrameAddress)s.Target).Offset < array.Offset + 8 * replacements.Max(p => ((MethodRef)p.Call.Op!.Operand!).Method.Parameters.Count))) block.Statements.Remove(store);
                sharedSites.Add(call.Address);
            }

            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call call) continue;
                    Call Operation(OpKind kind, TypeRef type, params Expr[] args) => call with
                    { Op = new(kind, type), Arguments = args, Sources = [], Results = [], Defines = [], Target = Expr.C(0, 64) };
                    if (call is { Op.Kind: OpKind.Import, Op.Operand: "memset", Arguments: [var dest, Const { Value: 0 }, var size] }
                        && SizeType(size) is { } cleared && Equals(AddressType(dest), cleared))
                        block.Statements[i] = Operation(OpKind.ClearGenericValue, cleared, dest);
                    else if (call is { Op.Kind: OpKind.Import, Op.Operand: "memcpy", Arguments: [var to, var from, var bytes] }
                        && SizeType(bytes) is { } copied && Equals(AddressType(to), copied) && Equals(AddressType(from), copied))
                        block.Statements[i] = Operation(OpKind.CopyGenericValue, copied, to, from);
                    else if (call is { Op: null, Target: Const target, Arguments: [var obj, Symbol { Kind: SymbolKind.Field, Value: FieldRef field } symbol, var value, var count, ..] }
                        && owner.SharedFieldSetter(target.Value) == -1 && SizeType(count) is { } stored
                        && Equals(FieldType(field), stored) && Equals(AddressType(value), stored))
                        block.Statements[i] = Operation(OpKind.CopyGenericValue, stored, FieldAddress(obj, symbol), value);
                    else if (call.Kind == CallKind.Indirect && call.Arguments.Length >= 5 && call.Arguments[3] is FrameAddress array
                        && GenericInvokerIdentity.Match(ExpandValue(call.Target), ExpandValue(call.Arguments[0]), ExpandValue(call.Arguments[1])) is { } callee)
                    {
                        var returned = Concrete(callee, callee.Method.ReturnType);
                        if (!ManagedTypes.IsVoid(returned) && !Equals(AddressType(call.Arguments[4]), returned)
                            && !(call.Arguments[4] is FrameAddress && types.Size(returned) > 0)) continue;
                        var stores = InvokerStores(block, i);
                        var args = new List<Expr> { call.Arguments[2] };
                        var consumed = new List<Store>();
                        for (var p = 0; p < callee.Method.Parameters.Count; p++)
                        {
                            if (!stores.TryGetValue(array.Offset + p * 8, out var store)) break;
                            var type = Concrete(callee, callee.Method.Parameters[p].Type);
                            var storedType = type is ByRefRef reference ? reference.Element : type;
                            if (!ManagedTypes.IsReferenceType(type) && !Equals(AddressType(store.Value), storedType)
                                && !(store.Value is FrameAddress && types.Size(storedType) > 0)) break;
                            args.Add(store.Value); consumed.Add(store);
                        }
                        if (consumed.Count != callee.Method.Parameters.Count) continue;
                        args.Add(ManagedTypes.IsVoid(returned) ? Expr.C(0, 64) : call.Arguments[4]);
                        block.Statements[i] = call with { Op = new(OpKind.InvokeGeneric, callee), Arguments = args.ToArray(),
                            Sources = [], Results = [], Defines = [], Target = Expr.C(0, 64) };
                        // 参数数组只供这次 invoker 读取；同址后续写入仍保留。
                        foreach (var store in consumed)
                        {
                            var ownerBlock = function.Blocks.Single(b => b.Statements.Contains(store));
                            ownerBlock.Statements[ownerBlock.Statements.IndexOf(store)] = new Nop(store.Address, "invoker 参数");
                        }
                    }
                    if (!ReferenceEquals(block.Statements[i], call))
                    {
                        sharedSites.Add(call.Address);
                        // memcpy/memset 返回目标地址；托管值复制不能丢失仍被使用的指针定义。
                        if (call is { Op: { Kind: OpKind.Import, Operand: "memcpy" or "memset" }, Defines: [var result] })
                        {
                            block.Statements.Insert(++i, new Define(call.Address, result, call.Arguments[0]));
                            defs[result] = call.Arguments[0];
                        }
                    }
                }
            NormalizeStackCanary(ExpandValue);
            PromotePrivateFrameSlots();
            Ssa.Propagate.RemoveDead(function);
            var remaining = function.Blocks.SelectMany(b => b.Statements).Select(s => s.Address).ToHashSet();
            foreach (var define in original.OfType<Define>())
                if (!remaining.Contains(define.Address) && ExprMap.Walk(ExpandValue(define.Value)).OfType<Load>()
                    .Any(l => l.Address is Binary { Left: Symbol { Kind: SymbolKind.Class or SymbolKind.Method } })) sharedSites.Add(define.Address);
        }

        private void NormalizeStackCanary(Func<Expr, int, Expr> expand)
        {
            StackCanaryRecognition.Run(function, expand, new ManagedCallFrames(facts, owner.abi).ArgumentSize);
        }

        private RecoveryResult<ManagedValue> SharedValue(Expr address, TypeRef type)
        {
            if (!Recover(AddressExpression(address), null).TryGet(out var value, out var failure)) return failure;
            if (value.Type is not ByRefRef reference || !reference.Element.Equals(type)) return Fail(0, $"共享存储 {type} 的地址类型不匹配");
            return value is AddressValue direct ? direct.Target : new IndirectValue(value, type);
        }

        [CallRule(9)]
        private RecoveryResult<bool> LowerSharedValues(Call call, List<ManagedStatement> output)
        {
            if (call.Op is { Kind: OpKind.UnboxGenericValue, Operand: TypeRef unboxed })
            {
                if (!SharedValue(call.Arguments[0], unboxed).TryGet(out var target, out var failure)) return failure;
                if (!RecoverAs(call.Arguments[1], types.Object, call.Address).TryGet(out var value, out failure)) return failure;
                var cast = new UnboxValue(value, unboxed, Math.Max(0, types.Bits(unboxed)));
                output.Add(target is LocalValue local ? new ManagedAssignment(call.Address, local, cast) : new ManagedStore(call.Address, target, cast));
                return true;
            }
            if (call is { Op: { Kind: OpKind.InvokeConstrainedGeneric, Operand: MethodRef contract },
                Arguments: [Symbol { Value: TypeRef constraint }, var address], Defines: [var defined] })
            {
                if (!SharedValue(address, constraint).TryGet(out var constrainedValue, out var failure)) return failure;
                if (!Local(defined).TryGet(out var constrainedResult, out failure)) return failure;
                output.Add(new ManagedCall(call.Address, new(contract, new AddressValue(constrainedValue), [], true) { Constraint = constraint }, constrainedResult, false));
                return true;
            }
            if (call.Op is { Kind: OpKind.CopyGenericValue or OpKind.ClearGenericValue, Operand: TypeRef type })
            {
                if (!SharedValue(call.Arguments[0], type).TryGet(out var target, out var failure)) return failure;
                ManagedValue value = new ComposedValue(type, []);
                if (call.Op.Kind != OpKind.ClearGenericValue && !SharedValue(call.Arguments[1], type).TryGet(out value, out failure)) return failure;
                output.Add(target is LocalValue local ? new ManagedAssignment(call.Address, local, value) : new ManagedStore(call.Address, target, value));
                return true;
            }
            if (call.Op is not { Kind: OpKind.InvokeGeneric, Operand: MethodRef callee }) return false;
            var parameters = new List<ManagedValue>();
            foreach (var parameter in callee.Method.Parameters)
            {
                var parameterType = Concrete(callee, parameter.Type);
                var recovered = ManagedTypes.IsReferenceType(parameterType) || parameterType is ByRefRef
                    ? RecoverAs(call.Arguments[parameters.Count + 1], parameterType, call.Address)
                    : SharedValue(call.Arguments[parameters.Count + 1], parameterType);
                if (!recovered.TryGet(out var value, out var failure)) return failure;
                parameters.Add(value);
            }
            if (constructed.TryGetValue(call, out var created))
            {
                if (Assign(call.Address, created, () => new NewObjectValue(callee, parameters), output) is { } failure) return failure;
                return true;
            }
            var returned = Concrete(callee, callee.Method.ReturnType);
            LocalValue? result = null;
            if (!ManagedTypes.IsVoid(returned))
            {
                if (!SharedValue(call.Arguments[^1], returned).TryGet(out var value, out var failure)) return failure;
                if (value is not LocalValue local) return Fail(call.Address, "共享返回存储不是局部变量");
                result = local;
            }
            ManagedValue? receiver = null;
            if (!callee.Method.IsStatic && !RecoverAs(call.Arguments[0], callee.DeclaringType, call.Address).TryGet(out receiver, out var receiverFailure)) return receiverFailure;
            output.Add(new ManagedCall(call.Address, new(callee, receiver, parameters,
                callee.DeclaringType is DefinitionRef declaring && DelegateFacts.IsDelegate(declaring)), result, false));
            return true;
        }
    }
}
