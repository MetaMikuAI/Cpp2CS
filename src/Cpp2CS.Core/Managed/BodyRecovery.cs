using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>将完整 CFG 转为托管语句和边赋值。存在未恢复语句时不返回可输出的方法体。</summary>
public static class BodyRecovery
{
    public static BodyRecoveryResult Recover(RecoverySession session, PreparedMethod prepared, bool recoverAccessors = true, bool recoverConstructors = true)
    {
        var problems = prepared.Problems.Select(p => new RecoveryProblem(prepared.Function.Entry, p)).ToList();
        problems.AddRange(prepared.Function.Problems.Select(p => new RecoveryProblem(prepared.Function.Entry, "CFG: " + p)));
        if (problems.Count > 0) return new(null, problems);
        var values = new ValueRecovery(session, prepared);
        problems.AddRange(values.Stack.Problems);
        problems.AddRange(values.BufferProblems);
        if (values.SignatureProblem is { } signatureProblem) problems.Add(new(prepared.Function.Entry, signatureProblem));
        var returnType = prepared.Method.Method.ReturnType.Substitute(prepared.Method.TypeArguments, prepared.Method.MethodArguments);
        var copies = TypedCopies.Recover(prepared.Function, values, session.Types);
        var blocks = new List<ManagedBlock>();
        LocalValue? Local(Variable variable) => values.Locals.TryGetValue(variable, out var info) ? new(variable, info.Type, info.Width) : null;

        ManagedEdge Edge(Block from, int successor, ulong target)
        {
            var to = from.NormalSuccessors.ElementAtOrDefault(successor);
            if (to is null || to.Start != target) throw new InvalidOperationException($"CFG 中缺少第 {successor} 条边 {from.Start:x} → {target:x}");
            var incoming = MachineFunction.PredecessorIndex(from, successor);
            var copies = new List<ManagedCopy>();
            foreach (var phi in to.Statements.OfType<Phi>())
            {
                if (values.Metadata.IsRuntimeReference(phi.Target)) continue;
                if (Local(phi.Target) is not { } local) { problems.Add(new(phi.Address, "汇合值类型未确定")); continue; }
                if (values.RecoverAs(new Use(phi.Sources[incoming], local.Width), local.Type, out var reason) is not { } value)
                    problems.Add(new(phi.Address, reason!));
                else copies.Add(new(local, value));
            }
            return new(target, copies);
        }

        foreach (var block in prepared.Function.Blocks)
        {
            if (block.IsLandingPad || block.Handler is not null) problems.Add(new(block.Start, "异常区域尚未恢复"));
            var statements = new List<ManagedStatement>();
            foreach (var statement in block.Statements)
            {
                if (copies.TryGetValue(statement, out var replacement))
                {
                    if (replacement is not null) statements.Add(replacement);
                    continue;
                }
                string? problem = null;
                switch (statement)
                {
                    case Define define:
                        if (values.Metadata.IsRuntimeReference(define.Target)) break;
                        if (values.Recover(define.Value, out problem) is { } value && Local(define.Target) is { } local)
                            statements.Add(new ManagedAssignment(define.Address, local, value));
                        else problem ??= "定义的类型未确定";
                        break;
                    case Phi phi:
                        if (values.Metadata.IsRuntimeReference(phi.Target)) break;
                        if (Local(phi.Target) is null) problem = "汇合值类型未确定";
                        break;
                    case Store store:
                        if (values.Location(store.Target, store.Value.Width, out problem) is { } location
                            && values.RecoverAs(store.Value, location.Type, out problem) is { } stored)
                            statements.Add(new ManagedStore(store.Address, location, stored));
                        break;
                    case Call call:
                        if (session.Resolver.Resolve(call) is HelperCallee helperCallee)
                        {
                            if (helperCallee.Helper.Kind == Runtime.HelperKind.ClassInit)
                            {
                                if (ClassInitialization.Invocation(session.Types, call, values.Metadata, out problem) is not { } initialize) break;
                                statements.Add(new ManagedCall(call.Address, initialize, null, false));
                                if (call.Kind == CallKind.Tail)
                                {
                                    if (ManagedTypes.IsVoid(returnType)) statements.Add(new ManagedReturn(call.Address, null));
                                    else problem = "类初始化尾调用不能作为普通托管返回值";
                                }
                                break;
                            }
                            if (values.HelperValue(call, out problem) is not { } helper) break;
                            if (call.Kind == CallKind.Tail)
                            {
                                if (session.Types.IsAssignable(helper.Type, returnType)) statements.Add(new ManagedReturn(call.Address, helper));
                                else problem = "运行时尾调用返回类型不符";
                            }
                            else if (values.CallResult(call) is { } helperResult) statements.Add(new ManagedAssignment(call.Address, helperResult, helper));
                            else problem = "运行时调用返回值尚未恢复";
                            break;
                        }
                        if (values.Invocation(call, out problem) is not { } invocation) break;
                        var tail = call.Kind is CallKind.Tail or CallKind.TailIndirect;
                        var calledReturn = invocation.Method.Method.ReturnType.Substitute(invocation.Method.TypeArguments, invocation.Method.MethodArguments);
                        LocalValue? result = null;
                        if (tail)
                        {
                            if (!session.Types.IsAssignable(calledReturn, returnType)) problem = "尾调用返回类型不符";
                        }
                        else if (!ManagedTypes.IsVoid(calledReturn))
                        {
                            result = values.CallResult(call);
                            if (result is null) problem ??= "调用返回值尚未组装";
                        }
                        if (problem is null)
                        {
                            statements.Add(new ManagedCall(call.Address, invocation, result, tail));
                            if (!tail && result is not null && values.CallDestination(call) is { } destination)
                            {
                                var target = values.Location(destination, result.Width, out problem, whole: true);
                                if (target?.Type == result.Type) statements.Add(new ManagedStore(call.Address, target, result));
                                else problem ??= "调用返回缓冲区类型不符";
                            }
                        }
                        break;
                    case Branch branch:
                        if (values.Recover(branch.Condition, out problem) is { Width: 1 } condition)
                            statements.Add(new ManagedBranch(branch.Address, condition, Edge(block, 0, branch.Target), Edge(block, 1, branch.Fallthrough)));
                        else problem ??= "分支条件不是布尔值";
                        break;
                    case Jump jump:
                        statements.Add(new ManagedJump(jump.Address, Edge(block, 0, jump.Target)));
                        break;
                    case Return { Buffer: not null } ret:
                        if (values.ReturnValue is { } buffered) statements.Add(new ManagedReturn(ret.Address, buffered));
                        else problem = "缓冲区返回尚未组装";
                        break;
                    case Return { Pieces.Length: > 0 } ret:
                        if (values.Aggregate(returnType, ret.Pieces, out problem) is { } aggregate)
                            statements.Add(new ManagedReturn(ret.Address, aggregate));
                        break;
                    case Return { Value: { } native } ret:
                        if (values.RecoverAs(native, returnType, out problem) is { } returned)
                            statements.Add(new ManagedReturn(ret.Address, returned));
                        break;
                    case Return ret:
                        if (!ManagedTypes.IsVoid(returnType)) problem = "非 void 方法缺少返回值";
                        else statements.Add(new ManagedReturn(ret.Address, null));
                        break;
                    case Nop: break;
                    default: problem = $"未支持语句 {statement.GetType().Name}"; break;
                }
                if (problem is not null) problems.Add(new(statement.Address, problem));
            }
            if (statements.LastOrDefault() is not (ManagedReturn or ManagedJump or ManagedBranch or ManagedCall { Tail: true }))
            {
                var successors = block.NormalSuccessors.ToArray();
                if (successors.Length == 1) statements.Add(new ManagedJump(block.End, Edge(block, 0, successors[0].Start)));
                else problems.Add(new(block.Start, "基本块没有唯一终结方式"));
            }
            blocks.Add(new(block.Start, statements));
        }
        if (problems.Count > 0) return new(null, problems);
        var body = ObjectConstruction.Recover(new ManagedBody(prepared.Method, blocks));
        if (recoverConstructors) body = InlineConstructors.Recover(session, body);
        if (recoverAccessors) body = InlineAccessors.Recover(session, body);
        if (recoverConstructors) body = session.Constructors.Recover(body);
        return new(body, problems);
    }
}
