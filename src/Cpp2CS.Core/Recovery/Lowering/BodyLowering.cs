using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class BodyLowering
{
    internal static RecoveryResult<ManagedBody> Build(this RecoveryScope ctx)
    {
        if (ctx.State.Exceptions.exceptionLayout is { Succeeded: true })
            return ctx.BuildExceptionBody();
        var managedBlocks = new List<ManagedBlock>();
        foreach (var block in ctx.blocks)
        {
            var statements = new List<ManagedStatement>();
            RecoveryHole? terminatorHole = null;
            foreach (var statement in block.Statements)
            {
                if (ctx.State.Lowering.dropped.Contains(statement))
                    continue;
                var failure = ctx.ledger.TryGetDiagnosis(statement, out var diagnosed) ? RecoveryDiagnostics.Derived(diagnosed, $"{diagnosed.Reason.Split(' ')[0]} 语句已诊断") : ctx.Translate(block, statement, statements);
                if (failure is { } e)
                {
                    var cause = ctx.Record(e, statement.Address, statement);
                    var terminal = statement is Branch or Jump or Return or IndirectJump or Trap or Call { Kind: CallKind.Tail or CallKind.TailIndirect } or Call { Op.Kind: OpKind.Throw or OpKind.ThrowNew or OpKind.Rethrow or OpKind.ResumeUnwind or OpKind.Terminate };
                    if (terminal)
                        terminatorHole = cause;
                    // 部分方法体：洞留在原处，终结语句的洞结束本块。
                    statements.Add(new ManagedHole(statement.Address, e.Message, terminal));
                }
            }

            if (statements.LastOrDefault() is not (ManagedReturn or ManagedJump or ManagedBranch or ManagedSwitch or ManagedThrow or ManagedCall { Tail: true } or ManagedHole { Terminal: true }))
            {
                var successors = block.NormalSuccessors.ToArray();
                if (successors.Length == 0 && statements.LastOrDefault() is ManagedCall { Result: null } noReturn && ManagedTypes.IsVoid(noReturn.Invocation.Method.Method.ReturnType) && block.Statements.LastOrDefault() is Call { Target: Const target } && ctx.owner.lifter.NoReturn.IsNoReturn(target.Value) && ManagedTypes.IsVoid(ctx.State.Signature.returnType))
                    statements[^1] = noReturn with
                    {
                        Tail = true
                    };
                else if (successors.Length == 1)
                {
                    if (ctx.Edge(block, 0, successors[0].Start).TryGet(out var edge, out var failure))
                        statements.Add(new ManagedJump(block.End, edge));
                    else
                    {
                        ctx.Record(failure, block.End);
                        statements.Add(new ManagedHole(block.End, failure.Message, true));
                    }
                }
                else if (terminatorHole is { } cause)
                {
                    ctx.Record(RecoveryDiagnostics.Derived(cause, "控制流 终结语句未恢复"), block.Start);
                    statements.Add(new ManagedHole(block.End, "控制流 终结语句未恢复", true));
                }
                else
                {
                    ctx.Hole(block.Start, "控制流 基本块没有唯一终结方式", rule: "Build");
                    statements.Add(new ManagedHole(block.End, "控制流 基本块没有唯一终结方式", true));
                }
            }

            // 循环入口前的空块没有原生指令；其标签必须与实际循环入口区分，回边仍指向原生地址。
            var label = block == ctx.function.EntryBlock && block.End == block.Start ? NameSupply.EntryLabel : block.Start;
            managedBlocks.Add(new(label, statements));
        }

        return new ManagedBody(ctx.method, managedBlocks);
    }

    internal static RecoveryResult<LocalValue> Local(this RecoveryScope ctx, Variable v) => ctx.LocalOf(v);
    internal static RecoveryResult<ManagedEdge> Edge(this RecoveryScope ctx, Block from, int successor, ulong target)
    {
        var to = from.NormalSuccessors.ElementAtOrDefault(successor);
        if (to is null || to.Start != target)
            throw new InvalidOperationException($"CFG 中缺少第 {successor} 条边 {from.Start:x} → {target:x}");
        var incoming = MachineFunction.PredecessorIndex(from, successor);
        var copies = new List<ManagedCopy>();
        foreach (var group in ctx.State.Structs.structPhis.Where(g => g.Block == to))
            copies.Add(new(group.Local, group.Incoming(incoming)));
        foreach (var phi in to.Statements.OfType<Phi>())
        {
            if (ctx.State.Structs.structPhiMembers.ContainsKey(phi.Target) || ctx.State.Exceptions.exceptionLayout is { Succeeded: true } && !ctx.State.Exceptions.exceptionDemand.Contains(phi.Target) || ctx.State.Runtime.runtime.Contains(phi.Target) || ctx.State.Exceptions.exceptionValues.ContainsKey(phi.Target))
                continue;
            if (ctx.State.Structs.fragmentLocals.TryGetValue(phi.Target, out var fragmentTarget))
            {
                if (!ctx.Variable(phi.Sources[incoming], fragmentTarget.Width).TryGet(out var fragmentSource, out var fragmentFailure))
                    return fragmentFailure;
                foreach (var part in fragmentTarget.Parts)
                {
                    if (!ctx.Slice(fragmentSource, part.Low, part.Value.Width).Bind(v => ctx.Coerce(v, part.Value.Type, phi.Address)).TryGet(out var value, out fragmentFailure))
                        return fragmentFailure;
                    copies.Add(new((LocalValue)part.Value, value));
                }

                continue;
            }

            if (!ctx.Local(phi.Target).TryGet(out var local, out var failure))
                return failure;
            var source = phi.Sources[incoming];
            var attempt = Copy();
            if (attempt.TryGet(out var copied, out failure))
                copies.Add(new(local, copied));
            else
            {
                if (ctx.State.Exceptions.collectingExceptionDemand)
                    return failure;
                ctx.Record(failure, phi.Address);
                copies.Add(new(local, new HoleValue(failure.Message, local.Type, local.Width)));
            }

            RecoveryResult<ManagedValue> Copy()
            {
                if (ctx.CheckPoison(source) is { } poison)
                    return poison;
                if (source.Version == 0 && !ctx.State.Signature.arguments.ContainsKey(source.Storage))
                    return RecoveryDiagnostics.Fail(phi.Address, $"汇合 未定义的来源 {source}", rule: "Edge");
                RecoveryResult<ManagedValue> read = ctx.values.TryGetValue(source, out var c) && c is Const constant ? new ConstantValue(constant.Value & Expr.Mask(local.Width), local.Type, local.Width) : ctx.Variable(source, local.Width);
                if (!read.TryGet(out var value, out var error))
                    return error;
                if (value is Fragment fragment && !ctx.Pack(fragment).TryGet(out value, out error))
                    return error;
                if (value.Width != local.Width)
                    return RecoveryDiagnostics.Fail(phi.Address, $"汇合 来源 {source} 的位宽与 φ 不一致", rule: "Edge");
                return ctx.types.Kind(local.Type) == TypeKind.Reference ? ctx.Coerce(value, local.Type, phi.Address) : value;
            }
        }

        return new ManagedEdge(target, copies);
    }

    internal static RecoveryFailure? Rules(IEnumerable<RecoveryResult<bool>> candidates, out bool handled)
    {
        handled = false;
        foreach (var candidate in candidates)
        {
            if (!candidate.TryGet(out handled, out var failure))
                return failure;
            if (handled)
                break;
        }

        return null;
    }

    internal static RecoveryResult<T?> FirstValue<T>(IEnumerable<RecoveryResult<T?>> candidates)
        where T : class
    {
        foreach (var candidate in candidates)
        {
            if (!candidate.TryGet(out var value, out var failure))
                return failure;
            if (value is not null)
                return value;
        }

        return (T?)null;
    }

    internal static RecoveryFailure? Emit<T>(RecoveryResult<T> result, List<ManagedStatement> output)
        where T : ManagedStatement
    {
        if (!result.TryGet(out var statement, out var failure))
            return failure;
        output.Add(statement);
        return null;
    }

    internal static RecoveryFailure? Assign(this RecoveryScope ctx, ulong address, Variable target, Func<RecoveryResult<ManagedValue>> value, List<ManagedStatement> output) => BodyLowering.Emit(ctx.Local(target).Bind(local => value().Map(v => new ManagedAssignment(address, local, v))), output);
    internal static RecoveryFailure? Translate(this RecoveryScope ctx, Block block, Stmt statement, List<ManagedStatement> output)
    {
        if (BodyLowering.Rules(RuleRegistry.Statements.Select(rule => rule(ctx.Lowering, block, statement, output)), out var handled) is { } ruleFailure)
            return ruleFailure;
        if (handled)
            return null;
        switch (statement)
        {
            case Define define:
                {
                    if (ctx.State.Runtime.objectClasses.TryGetValue(define.Target, out var obj))
                        return BodyLowering.Emit(ctx.Recover(obj, ctx.types.Object).Bind(value => ctx.Check(define.Address, new ComparisonValue(Cond.Eq, value, new ConstantValue(0, ctx.types.Object, 64), ctx.types.Boolean), "System.NullReferenceException")), output);
                    if (ctx.State.Runtime.runtime.Contains(define.Target) || ctx.State.Lowering.inlined.Contains(define.Target))
                        return null;
                    if (BodyLowering.Rules(RuleRegistry.Defines.Select(rule => rule(ctx.Lowering, define, output)), out handled) is { } failed)
                        return failed;
                    if (handled)
                        return null;
                    if (!ctx.Local(define.Target).TryGet(out var local, out var failure))
                        return failure;
                    if (!ctx.Recover(define.Value, local.Type).TryGet(out var value, out failure))
                        return failure;
                    if ((value.Width != local.Width || value is Fragment) && !ctx.Coerce(value, local.Type, define.Address).TryGet(out value, out failure))
                        return failure;
                    output.Add(new ManagedAssignment(define.Address, local, value));
                    return null;
                }

            case Phi or Nop:
                return null;
            case Store store:
                {
                    if (BodyLowering.Rules(RuleRegistry.Stores.Select(rule => rule(ctx.Lowering, store, output)), out handled) is { } failed)
                        return failed;
                    if (handled)
                        return null;
                    if (!ctx.Location(store.Target, store.Value.Width).TryGet(out var target, out var failure))
                        return failure;
                    if (BodyLowering.Rules(RuleRegistry.StoreTargets.Select(rule => rule(ctx.Lowering, store, target, output)), out handled) is { } rejected)
                        return rejected;
                    if (handled)
                        return null;
                    return BodyLowering.Emit(ctx.RecoverAs(store.Value, target.Type, store.Address).Map(value => new ManagedStore(store.Address, target, value)), output);
                }

            case Call call:
                return ctx.TranslateCall(call, output);
            case Branch branch:
                return BodyLowering.Emit(ctx.Recover(branch.Condition, ctx.types.Boolean).Bind(ValueRecovery.Truth).Bind(condition => ctx.Edge(block, 0, branch.Target).Bind(taken => ctx.Edge(block, 1, branch.Fallthrough).Map(fallthrough => new ManagedBranch(branch.Address, condition, taken, fallthrough)))), output);
            case Jump jump:
                return BodyLowering.Emit(ctx.Edge(block, 0, jump.Target).Map(edge => new ManagedJump(jump.Address, edge)), output);
            case Return ret:
                if (ctx.State.Signature.returnHole is { } cause)
                    return RecoveryDiagnostics.Derived(cause, "返回 返回值类型尚未支持");
                if (ManagedTypes.IsVoid(ctx.State.Signature.returnType))
                {
                    output.Add(new ManagedReturn(ret.Address, null));
                    return null;
                }

                if (ctx.State.Signature.ownReturnBuffer is not null)
                {
                    output.Add(new ManagedReturn(ret.Address, ctx.State.Signature.ownReturnBuffer));
                    return null;
                }

                if (ret.Value is not { } returned)
                    return RecoveryDiagnostics.Fail(ret.Address, "返回 非 void 方法缺少返回值", rule: "Translate");
                return BodyLowering.Emit((ctx.types.Kind(ctx.State.Signature.returnType) == TypeKind.Struct ? ctx.StructReturn(returned) : ctx.RecoverAs(returned, ctx.State.Signature.returnType, ret.Address)).Map(value => new ManagedReturn(ret.Address, value)), output);
            default:
                return RecoveryDiagnostics.Fail(statement.Address, $"语句 {statement.GetType().Name} 尚未支持", rule: "Translate");
        }
    }

    internal static RecoveryFailure? TranslateCall(this RecoveryScope ctx, Call call, List<ManagedStatement> output)
    {
        if (BodyLowering.Rules(RuleRegistry.Calls.Select(rule => rule(ctx.Lowering, call, output)), out var handled) is { } ruleFailure)
            return ruleFailure;
        if (handled)
            return null;
        var address = call.Address;
        var ignored = ctx.IsWriteBarrier(call) || call.Op?.Kind is OpKind.InitClass or OpKind.InitMethodRgctx or OpKind.InterfaceInvokeData || ctx.State.Runtime.genericResolvers.Contains(call);
        if (ignored)
        {
            if (call.Kind == CallKind.Tail)
            {
                if (!ManagedTypes.IsVoid(ctx.State.Signature.returnType))
                    return RecoveryDiagnostics.Fail(address, "返回 尾调用写屏障的方法不是 void", rule: "TranslateCall");
                output.Add(new ManagedReturn(address, null));
            }

            return null;
        }

        switch (call.Op)
        {
            case { Kind: OpKind.CompareExchangeReference }:
                return ctx.CompareExchangeReference(call, output);
            case { Kind: OpKind.RunClassConstructor, Operand: TypeRef type }:
                if (ctx.owner.runClassConstructor is not { } run)
                    return RecoveryDiagnostics.Fail(address, "类初始化 核心库缺少 RuntimeHelpers.RunClassConstructor", rule: "TranslateCall");
                output.Add(new ManagedCall(address, new ManagedInvocation(run, null, [new TypeHandleValue(type, ctx.types.RuntimeTypeHandle, ctx.types.Size(ctx.types.RuntimeTypeHandle) * 8)], false), null, false));
                return null;
            case { Kind: OpKind.MemoryBarrier }:
                if (ctx.owner.memoryBarrier is not { } barrier)
                    return RecoveryDiagnostics.Fail(address, "运行时操作 核心库缺少 Thread.MemoryBarrier", rule: "TranslateCall");
                output.Add(new ManagedCall(address, new ManagedInvocation(barrier, null, [], false), null, false));
                return null;
            case { Kind: OpKind.NullCheck }:
                {
                    if (!ctx.Recover(call.Arguments[0], ctx.types.Object).TryGet(out var operand, out var failure))
                        return failure;
                    var zeroType = call.Arguments[0] is Use u && ctx.results.TryGetValue(u.Variable, out var checkedResult) && ctx.State.Runtime.typeChecks.ContainsKey(checkedResult.Call) ? operand.Type : ctx.types.Object;
                    return BodyLowering.Emit(ctx.Check(address, new ComparisonValue(Cond.Eq, operand, new ConstantValue(0, zeroType, 64), ctx.types.Boolean), "System.NullReferenceException"), output);
                }

            case { Kind: OpKind.BoundsCheck } when call.Arguments is [var index, var length]:
                return BodyLowering.Emit(ctx.Recover(index, ctx.types.Int32).Bind(i => ctx.Recover(length, i.Type).Bind(value => ctx.Coerce(value, i.Type, address)).Bind(n => ctx.Check(address, new ComparisonValue(Cond.Uge, i, n, ctx.types.Boolean), "System.IndexOutOfRangeException"))), output);
            case { Kind: OpKind.ThrowIf, Operand: string exception }:
                return BodyLowering.Emit(ctx.Recover(call.Arguments[0], ctx.types.Boolean).Bind(ValueRecovery.Truth).Bind(condition => ctx.Check(address, condition, exception)), output);
            case { Kind: OpKind.ThrowNew, Operand: string exception }:
                if (ctx.owner.ExceptionConstructor(exception) is not { } throwConstructor)
                    return RecoveryDiagnostics.Fail(address, $"异常 {exception} 没有无参构造函数", rule: "TranslateCall");
                output.Add(new ManagedThrow(address, new NewObjectValue(throwConstructor, [])));
                return null;
            case { Kind: OpKind.NewException, Operand: string exception } when call.Defines.FirstOrDefault() is { } created:
                return ctx.Assign(address, created, () => ctx.owner.ExceptionConstructor(exception) is { } constructor ? new NewObjectValue(constructor, []) : RecoveryDiagnostics.Fail(address, $"异常 {exception} 没有无参构造函数", rule: "TranslateCall"), output);
            case { Kind: OpKind.Throw or OpKind.ThrowManaged or OpKind.Rethrow }:
                return BodyLowering.Emit(ctx.Recover(call.Arguments[0], null).Map(value => new ManagedThrow(address, value)), output);
            case { Kind: OpKind.NewObject } when ctx.State.Construction.inlineConstructors.TryGetValue(call, out var constructor):
                {
                    var arguments = new List<ManagedValue>();
                    var cursor = 0;
                    foreach (var parameter in constructor.Parameters)
                    {
                        var pieces = constructor.Arguments.Skip(cursor).Take(parameter.Pieces.Length).ToArray();
                        cursor += pieces.Length;
                        var recovered = ctx.RegisterStruct(parameter)
                            ? ctx.Compose(parameter, piece => pieces[Array.IndexOf(parameter.Pieces, piece)])
                            : ctx.RecoverAs(pieces[0], parameter.Type, address);
                        if (!recovered.TryGet(out var value, out var failure))
                            return failure;
                        arguments.Add(value);
                    }

                    return ctx.Assign(address, call.Defines[0], () => new NewObjectValue(constructor.Method, arguments) { Transparent = true }, output);
                }

            case { Kind: OpKind.NewArray, Operand: ArrayRef array }:
                {
                    if (!ctx.Index(call.Arguments[1]).TryGet(out var length, out var failure))
                        return failure;
                    var value = new NewArrayValue(array, length);
                    if (call.Kind == CallKind.Tail)
                        return BodyLowering.Emit(ctx.Coerce(value, ctx.State.Signature.returnType, address).Map(result => new ManagedReturn(address, result)), output);
                    if (call.Defines.FirstOrDefault() is { } createdArray)
                        return ctx.Assign(address, createdArray, () => value, output);
                    output.Add(new ManagedAssignment(address, ctx.StructLocal(array, 64), value));
                    return null;
                }

            case { Kind: OpKind.Box, Operand: TypeRef type } when call.Defines.FirstOrDefault() is { } created && ctx.State.Construction.boxed.TryGetValue(call, out var content):
                if (ctx.types.Kind(type) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double) || type is DefinitionRef { Definition.FullName: "System.Nullable" })
                    return RecoveryDiagnostics.Fail(address, $"装箱 类型 {type} 尚未支持", rule: "TranslateCall");
                return ctx.Assign(address, created, () => ctx.RecoverAs(content, type, address).Map<ManagedValue>(value => new BoxValue(value, type, ctx.types.Object)), output);
            case { Kind: OpKind.TypeCheck, Operand: TypeRef type } when ctx.State.Runtime.typeChecks.TryGetValue(call, out var obj) && call.Defines.FirstOrDefault() is { } checkedValue:
                return ctx.Assign(address, checkedValue, () => ctx.RecoverAs(obj, ctx.types.Object, address).Bind(value => ctx.Coerce(new ComparisonValue(Cond.Ne, new IsInstValue(value, type), new ConstantValue(0, type, 64), ctx.types.Boolean), ctx.types.UInt64, address)), output);
            case { Kind: OpKind.Unbox, Operand: TypeRef type } when (ctx.types.Kind(type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Struct || type is GenericParameterRef { NativeScalar: not null }) && call.Defines.FirstOrDefault() is { } created:
                return ctx.Assign(address, created, () => ctx.RecoverAs(call.Arguments[0], ctx.types.Object, address).Map<ManagedValue>(value => new UnboxAddressValue(value, type)), output);
            case { Kind: OpKind.IsInst, Operand: TypeRef type } when call.Kind == CallKind.Tail || call.Defines.FirstOrDefault() is not null:
                {
                    if (!ctx.Recover(call.Arguments[0], ctx.types.Object).Bind(value => ctx.Coerce(value, ctx.types.Object, address)).TryGet(out var value, out var failure))
                        return failure;
                    var instance = new IsInstValue(value, type, type is GenericParameterRef { NativeScalar: not null } ? ctx.types.Object : null);
                    return call.Kind == CallKind.Tail ? BodyLowering.Emit(ctx.Coerce(instance, ctx.State.Signature.returnType, address).Map(v => new ManagedReturn(address, v)), output) : ctx.Assign(address, call.Defines[0], () => instance, output);
                }

            case { Kind: OpKind.IsInstArrayElement } when call.Defines.FirstOrDefault() is { } created:
                return ctx.ArrayElementCheck(call, created, output);
            case null or { Kind: OpKind.CallVirtual or OpKind.CallInterface or OpKind.CallDelegate or OpKind.CallGenericVirtual or OpKind.CallMethodPointer }:
                return ctx.Invocation(call, output);
            default:
                return RecoveryDiagnostics.Fail(address, $"运行时操作 {call.Op?.Kind.ToString() ?? call.Kind.ToString()} 尚未支持", rule: "TranslateCall");
        }
    }

    internal static RecoveryResult<ManagedCheck> Check(this RecoveryScope ctx, ulong address, ManagedValue condition, string exception) => ctx.owner.ExceptionConstructor(exception) is { } constructor ? new ManagedCheck(address, condition, constructor) : RecoveryDiagnostics.Fail(address, $"异常 {exception} 没有无参构造函数", rule: "Check");
    internal static RecoveryFailure? Invocation(this RecoveryScope ctx, Call call, List<ManagedStatement> output)
    {
        var address = call.Address;
        if (BodyLowering.Rules(RuleRegistry.Invocations.Select(rule => rule(ctx.Lowering, call, output)), out var handled) is { } ruleFailure)
            return ruleFailure;
        if (handled)
            return null;
        if (call.Op is null && call.Target is Const target && ctx.facts.Code.RegionOf(target.Value) != CodeRegion.Managed)
            return RecoveryDiagnostics.Fail(address, $"调用 运行时函数 0x{target.Value:x}（{ctx.facts.Helpers.At(target.Value)?.Kind.ToString() ?? "未识别"}）", rule: "Invocation");
        if (call.Op is null && call.Kind is not (CallKind.Direct or CallKind.Tail))
            return RecoveryDiagnostics.Fail(address, "调用 来源未知的间接调用", rule: "Invocation");
        if (ctx.Resolve(call) is not { } callee)
            return RecoveryDiagnostics.Fail(address, ctx.CallResolutionFailure(call), rule: "Invocation");
        if (ctx.owner.abi.Classify(callee, out var problem) is not { } signature)
            return RecoveryDiagnostics.Fail(address, $"调用 {callee} 的签名: {problem}", rule: "Invocation");
        var registers = CallResolution.ArgumentsOf(call);
        RecoveryResult<Expr> Argument(AbiValue value, string name)
        {
            if (value.Passing != Passing.Registers || value.Pieces.Length != 1)
                return RecoveryDiagnostics.Fail(address, $"调用 {callee} 的参数 {name} 的传递方式尚未支持", rule: "Invocation");
            if (!registers.TryGetValue(value.Pieces[0].Register, out var e))
                return RecoveryDiagnostics.Fail(address, $"调用 {callee} 缺少参数 {name}", rule: "Invocation");
            return ctx.types.Kind(value.Type) is TypeKind.Float or TypeKind.Double ? ScalarVectorNarrowing.Low(e, value.Pieces[0].Width) : e;
        }

        var definition = callee.Method;
        ManagedValue? receiver = null;
        if (signature.This is { } self)
        {
            if (ctx.State.Frames.stackEnums.TryGetValue(call, out var stackEnum))
            {
                if (!ctx.RecoverAs(stackEnum.Value, stackEnum.Type, address).TryGet(out var value, out var failure))
                    return failure;
                receiver = new BoxValue(value, stackEnum.Type, self.Type);
            }
            else
            {
                RecoveryResult<Expr> argument = call.DelegateReceiver is { } delegateReceiver ? delegateReceiver : Argument(self, "this");
                if (!argument.TryGet(out var expression, out var failure))
                    return failure;
                if (!ctx.UnusedReceiver(call, callee, self, expression).TryGet(out receiver, out failure))
                    return failure;
                if (receiver is null && !ctx.RecoverAs(expression, self.Type, address).TryGet(out receiver, out failure))
                    return failure;
            }
        }

        var parameters = new List<ManagedValue>();
        for (var i = 0; i < signature.Parameters.Length; i++)
        {
            var parameter = signature.Parameters[i];
            var site = new ArgumentSite(call, callee, definition.Parameters[i].Name, registers, Argument)
            {
                Index = i,
                Output = output
            };
            if (!BodyLowering.FirstValue(RuleRegistry.Arguments.Select(rule => rule(ctx.Lowering, parameter, site))).TryGet(out var shaped, out var failure))
                return failure;
            if (shaped is not null)
            {
                parameters.Add(shaped);
                continue;
            }

            if (ctx.types.Kind(parameter.Type) is TypeKind.Struct or null || ctx.types.Kind(parameter.Type) == TypeKind.Pointer && !ManagedTypes.IsNativePointer(parameter.Type) && (parameter.Type is not ByRefRef parameterReference || ctx.types.Kind(parameterReference.Element) is not (TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Reference) && !ManagedTypes.IsNativePointer(parameterReference.Element)))
                return RecoveryDiagnostics.Fail(address, $"调用 {callee} 的参数类型 {parameter.Type} 尚未支持", rule: "Invocation");
            if (!Argument(parameter, definition.Parameters[i].Name).Bind(e => ctx.RecoverAs(e, parameter.Type, address)).TryGet(out var recovered, out failure))
                return failure;
            parameters.Add(recovered);
        }

        var calledReturn = CallResolution.Concrete(callee, definition.ReturnType);
        if (ctx.State.Construction.constructed.TryGetValue(call, out var created))
        {
            var value = ctx.State.Construction.forwardedConstructors.TryGetValue(call, out var own) ? new NewObjectValue(own with { TypeArguments = ((DefinitionRef)ctx.State.Types.known[created]).Arguments }, [])
            {
                Transparent = true
            }

            : new NewObjectValue(callee with { TypeArguments = ((DefinitionRef)ctx.State.Types.known[created]).Arguments }, parameters);
            return ctx.Assign(address, created, () => value, output);
        }

        var copied = call.Op is null && call.Target is Const copyTarget && ctx.facts.EntriesAt(copyTarget.Value).Length == 0 && ctx.facts.Unregistered.At(copyTarget.Value) is null;
        var isVirtual = call.Op is not null || ctx.State.Runtime.virtualCalls.Contains(call) || definition.IsVirtual && (definition.Attributes & System.Reflection.MethodAttributes.Final) != 0 && receiver is not ArgumentValue { Index: -1 };
        var invocation = new ManagedInvocation(callee, receiver, parameters, isVirtual && receiver is not null && receiver.Type is not ByRefRef);
        if (BodyLowering.Rules(RuleRegistry.InvocationOutputs.Select(rule => rule(ctx.Lowering, call, signature, registers, invocation, output)), out handled) is { } rejected)
            return rejected;
        if (handled)
            return null;
        if (call.Kind is CallKind.Tail or CallKind.TailIndirect)
        {
            // 枚举与同宽整数共用返回寄存器；显式保留枚举转换，不能套用于 bool、窄整数或浮点。
            if (!calledReturn.Equals(ctx.State.Signature.returnType) && ctx.types.Kind(calledReturn) == TypeKind.Int && ctx.types.Kind(ctx.State.Signature.returnType) == TypeKind.Int && (calledReturn is DefinitionRef { Definition.IsEnum: true } || ctx.State.Signature.returnType is DefinitionRef { Definition.IsEnum: true }) && ctx.types.Bits(calledReturn) == ctx.types.Bits(ctx.State.Signature.returnType) && ctx.types.Bits(ctx.State.Signature.returnType) is 32 or 64 && signature.Return is { Passing: Passing.Registers, Pieces.Length: 1 })
            {
                var enumResult = ctx.StructLocal(calledReturn, ctx.types.Bits(calledReturn));
                output.Add(new ManagedCall(address, invocation, enumResult, false) { Inlined = copied });
                output.Add(new ManagedReturn(address, new ConversionValue(ConvKind.Bitcast, enumResult, ctx.State.Signature.returnType, ctx.types.Bits(ctx.State.Signature.returnType))));
                return null;
            }

            if (ManagedTypes.IsVoid(ctx.State.Signature.returnType) && signature.Return is { Passing: Passing.Registers } discarded && (ctx.RegisterStruct(discarded) || discarded.Pieces.Length == 1 && ctx.types.Kind(calledReturn) is TypeKind.Bool or TypeKind.Int or TypeKind.Float or TypeKind.Double or TypeKind.Reference))
            {
                output.Add(new ManagedCall(address, invocation, null, false) { Inlined = copied });
                output.Add(new ManagedReturn(address, null));
                return null;
            }

            if (ManagedTypes.IsVoid(ctx.State.Signature.returnType) != ManagedTypes.IsVoid(calledReturn) || !ManagedTypes.IsVoid(ctx.State.Signature.returnType) && !calledReturn.Equals(ctx.State.Signature.returnType) && !ctx.types.IsAssignable(calledReturn, ctx.State.Signature.returnType))
                return RecoveryDiagnostics.Fail(address, $"尾调用 返回类型 {calledReturn} 与 {ctx.State.Signature.returnType} 不符", rule: "Invocation");
            output.Add(new ManagedCall(address, invocation, null, true) { Inlined = copied });
            return null;
        }

        LocalValue? result = null;
        if (signature.Return is { } returned)
        {
            if (!BodyLowering.FirstValue(RuleRegistry.Results.Select(rule => rule(ctx.Lowering, call, returned))).TryGet(out result, out var failure))
                return failure;
            if (result is null)
            {
                var index = Array.IndexOf(call.Results, returned.Pieces[0].Register);
                if (index >= 0 && index < call.Defines.Length && call.Defines[index] is { } defined && !ctx.State.Runtime.runtime.Contains(defined) && !ctx.Local(defined).TryGet(out result, out failure))
                    return failure;
            }
        }

        output.Add(new ManagedCall(address, invocation, result, false) { Inlined = copied });
        return null;
    }
}
