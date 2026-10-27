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
            var singleStores = original.OfType<Store>().Where(s => s.Target is FrameAddress).GroupBy(s => ((FrameAddress)s.Target).Offset)
                .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
            Expr ExpandValue(Expr e, int depth = 0) => depth > 24 ? e : ExprMap.Map(e,
                p => p is Use u && defs.TryGetValue(u.Variable, out var value) ? ExpandValue(value, depth + 1) : null);
            Expr Scalar(Expr e)
            {
                e = ExpandValue(e);
                while (e is Convert c) e = c.Operand;
                return e;
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
                Load { Address: FrameAddress frame } when singleStores.TryGetValue(frame.Offset, out var store) => AddressType(store.Value, depth + 1),
                _ => null,
            };
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Define define || ExpandValue(define.Value) is not Binary
                        { Op: BinOp.Sub, Left: FrameAddress or Intrinsic { Name: "managed_generic_buffer" }, Right: Binary { Op: BinOp.And, Left: Binary { Op: BinOp.Add, Left: var size, Right: Const { Value: 15 } }, Right: Const { Value: 0x1fffffff0 } } }
                        || SizeType(size) is not { } type) continue;
                    var buffer = new Intrinsic("managed_generic_buffer", [new Symbol(SymbolKind.Type, type), Expr.C(define.Address, 64)], 64);
                    sharedBuffers[define.Address] = StructLocal(type, 0);
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
                      True: Use { Variable: { Version: 0 } incoming }, False: FrameAddress slot }
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
            Ssa.Propagate.Run(function, Ssa.Dominators.Compute(function));
            defs = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);

            // 不同分支选择不同的 MethodInfo/实参后汇入同一个 invoker；调用分别留在原分支上。
            foreach (var block in function.Blocks.ToArray())
            {
                var calls = block.Statements.OfType<Call>().Where(c => c.Kind == CallKind.Indirect && c.Arguments.Length >= 5).ToArray();
                if (function.Range.ExceptionRegions.Length != 0 || calls is not [var call] || call.Arguments[1] is not Use methodUse || call.Arguments[3] is not FrameAddress array
                    || block.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == methodUse.Variable) is not { } methodPhi
                    || ExpandValue(call.Target) is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Use targetUse, Right: Const { Value: RuntimeLayout.MethodInvoker } } }
                    || targetUse.Variable != methodUse.Variable || ExpandValue(call.Arguments[0]) is not Load { Width: 64, Address: Use pointerUse }
                    || pointerUse.Variable != methodUse.Variable || block.Predecessors.Any(p => p.NormalSuccessors.ToArray() is not [var next] || next != block)) continue;
                var before = block.Statements.Take(block.Statements.IndexOf(call)).ToArray();
                if (before.Any(s => s is not (Phi or Define or Nop or Store { Target: FrameAddress }))) continue;
                var stores = before.OfType<Store>().GroupBy(s => ((FrameAddress)s.Target).Offset).ToDictionary(g => g.Key, g => g.Last());
                var replacements = new List<(Block Block, Call Call)>();
                for (var side = 0; side < block.Predecessors.Count; side++)
                {
                    if (ExpandValue(new Use(methodPhi.Sources[side], 64)) is not Symbol { Kind: SymbolKind.Method, Value: MethodRef callee }) break;
                    var returned = Concrete(callee, callee.Method.ReturnType);
                    if (!Equals(AddressType(call.Arguments[4]), returned)) break;
                    Expr OnEdge(Expr expression) => ExprMap.Map(expression, e => e is Use use
                        && block.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == use.Variable) is { } phi ? new Use(phi.Sources[side], use.Width) : null);
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
                    else if (call.Kind == CallKind.Indirect && ExpandValue(call.Target) is Load
                        { Width: 64, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Method, Value: MethodRef callee } methodInfo, Right: Const { Value: RuntimeLayout.MethodInvoker } } }
                        && call.Arguments.Length >= 5 && ExpandValue(call.Arguments[0]) is Load { Width: 64 } pointer && pointer.Address == methodInfo
                        && ExpandValue(call.Arguments[1]) == methodInfo && call.Arguments[3] is FrameAddress array)
                    {
                        var returned = Concrete(callee, callee.Method.ReturnType);
                        if (!ManagedTypes.IsVoid(returned) && !Equals(AddressType(call.Arguments[4]), returned)) continue;
                        var stores = block.Statements.Take(i).OfType<Store>().Where(s => s.Target is FrameAddress)
                            .GroupBy(s => ((FrameAddress)s.Target).Offset).ToDictionary(g => g.Key, g => g.Last());
                        var args = new List<Expr> { call.Arguments[2] };
                        var consumed = new List<Store>();
                        for (var p = 0; p < callee.Method.Parameters.Count; p++)
                        {
                            if (!stores.TryGetValue(array.Offset + p * 8, out var store)) break;
                            var type = Concrete(callee, callee.Method.Parameters[p].Type);
                            if (!ManagedTypes.IsReferenceType(type) && !Equals(AddressType(store.Value), type)) break;
                            args.Add(store.Value); consumed.Add(store);
                        }
                        if (consumed.Count != callee.Method.Parameters.Count) continue;
                        args.Add(ManagedTypes.IsVoid(returned) ? Expr.C(0, 64) : call.Arguments[4]);
                        block.Statements[i] = call with { Op = new(OpKind.InvokeGeneric, callee), Arguments = args.ToArray(),
                            Sources = [], Results = [], Defines = [], Target = Expr.C(0, 64) };
                        // 参数数组只供这次 invoker 读取；同址后续写入仍保留。
                        foreach (var store in consumed) block.Statements[block.Statements.IndexOf(store)] = new Nop(store.Address, "invoker 参数");
                    }
                    if (!ReferenceEquals(block.Statements[i], call)) sharedSites.Add(call.Address);
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
            bool Canary(Expr e) => expand(e, 0) is Load { Width: 64, Address: Binary { Op: BinOp.Add,
                Left: Intrinsic { Name: "sysreg_tpidr_el0" }, Right: Const { Value: 0x28 } } };
            foreach (var block in function.Blocks.ToArray())
            {
                if (block.Statements.LastOrDefault() is not Branch branch || expand(branch.Condition, 0) is not Compare
                    { Cond: Cond.Ne, Left: var left, Right: Load { Width: 64, Address: FrameAddress slot } }
                    || !Canary(left) || block.NormalSuccessors.ToArray() is not [var fail, var normal]
                    || !fail.Statements.OfType<Call>().Any(c => c.Op is { Kind: OpKind.Import, Operand: "__stack_chk_fail" })) continue;
                var stores = function.Blocks.SelectMany(b => b.Statements).OfType<Store>().Where(s => s.Target == slot).ToArray();
                if (stores is not [var saved] || !Canary(saved.Value)) continue;
                block.Statements[^1] = new Jump(branch.Address, normal.Start);
                MachineFunction.RemoveEdgeAt(block, 0);
                foreach (var ownerBlock in function.Blocks) ownerBlock.Statements.Remove(saved);
            }
            function.Problems.AddRange(Ssa.Lowering.Cleanup(function));
        }

        private ManagedValue SharedValue(Expr address, TypeRef type)
        {
            var value = Recover(AddressExpression(address), null);
            if (value.Type is not ByRefRef reference || !reference.Element.Equals(type)) throw Fail(0, $"共享存储 {type} 的地址类型不匹配");
            return value is AddressValue direct ? direct.Target : new IndirectValue(value, type);
        }

        [CallRule(9)]
        private bool LowerSharedValues(Call call, List<ManagedStatement> output)
        {
            if (call.Op is { Kind: OpKind.CopyGenericValue or OpKind.ClearGenericValue, Operand: TypeRef type })
            {
                var target = SharedValue(call.Arguments[0], type);
                var value = call.Op.Kind == OpKind.ClearGenericValue ? new ComposedValue(type, []) : SharedValue(call.Arguments[1], type);
                output.Add(target is LocalValue local ? new ManagedAssignment(call.Address, local, value) : new ManagedStore(call.Address, target, value));
                return true;
            }
            if (call.Op is not { Kind: OpKind.InvokeGeneric, Operand: MethodRef callee }) return false;
            var parameters = callee.Method.Parameters.Select((p, i) => Concrete(callee, p.Type) is var type && ManagedTypes.IsReferenceType(type)
                ? RecoverAs(call.Arguments[i + 1], type, call.Address) : SharedValue(call.Arguments[i + 1], type)).ToArray();
            var returned = Concrete(callee, callee.Method.ReturnType);
            var result = ManagedTypes.IsVoid(returned) ? null : (SharedValue(call.Arguments[^1], returned) as LocalValue
                ?? throw Fail(call.Address, "共享返回存储不是局部变量"));
            output.Add(new ManagedCall(call.Address, new(callee, callee.Method.IsStatic ? null : RecoverAs(call.Arguments[0], callee.DeclaringType, call.Address), parameters,
                callee.DeclaringType is DefinitionRef declaring && DelegateFacts.IsDelegate(declaring)), result, false));
            return true;
        }
    }
}
