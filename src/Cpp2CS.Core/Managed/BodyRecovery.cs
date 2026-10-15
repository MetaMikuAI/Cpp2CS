using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>将完整 CFG 转为托管语句和边赋值。存在未恢复语句时不返回可输出的方法体。</summary>
public static class BodyRecovery
{
    public static BodyRecoveryResult Recover(RecoverySession session, PreparedMethod prepared, bool recoverAccessors = true)
    {
        var problems = prepared.Problems.Select(p => new RecoveryProblem(prepared.Function.Entry, p)).ToList();
        problems.AddRange(prepared.Function.Problems.Select(p => new RecoveryProblem(prepared.Function.Entry, "CFG: " + p)));
        if (problems.Count > 0) return new(null, problems);
        var values = new ValueRecovery(session, prepared);
        if (values.SignatureProblem is { } signatureProblem) problems.Add(new(prepared.Function.Entry, signatureProblem));
        var returnType = prepared.Method.Method.ReturnType.Substitute(prepared.Method.TypeArguments, prepared.Method.MethodArguments);
        var blocks = new List<ManagedBlock>();
        LocalValue? Local(Variable variable) => values.Locals.TryGetValue(variable, out var info) ? new(variable, info.Type, info.Width) : null;

        ManagedEdge Edge(Block from, ulong target)
        {
            var to = from.NormalSuccessors.FirstOrDefault(b => b.Start == target);
            if (to is null) throw new InvalidOperationException($"CFG 中缺少边 {from.Start:x} → {target:x}");
            var incoming = to.Predecessors.IndexOf(from);
            if (incoming < 0) throw new InvalidOperationException("CFG 前驱与后继不一致");
            var copies = new List<ManagedCopy>();
            foreach (var phi in to.Statements.OfType<Phi>())
            {
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
                string? problem = null;
                switch (statement)
                {
                    case Define define:
                        if (values.Recover(define.Value, out problem) is { } value && Local(define.Target) is { } local)
                            statements.Add(new ManagedAssignment(define.Address, local, value));
                        else problem ??= "定义的类型未确定";
                        break;
                    case Phi phi:
                        if (Local(phi.Target) is null) problem = "汇合值类型未确定";
                        break;
                    case Store store:
                        if (values.Location(store.Target, store.Value.Width, out problem) is { } location
                            && values.RecoverAs(store.Value, location.Type, out problem) is { } stored)
                            statements.Add(new ManagedStore(store.Address, location, stored));
                        break;
                    case Call call:
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
                            if (session.Abi.ClassifyReturn(calledReturn, out problem) is { Passing: Passing.Registers, Pieces: [var piece] })
                            {
                                var index = Array.IndexOf(call.Results, piece.Register);
                                if (index >= 0 && index < call.Defines.Length) result = Local(call.Defines[index]);
                            }
                            if (result is null) problem ??= "调用返回值尚未组装";
                        }
                        if (problem is null) statements.Add(new ManagedCall(call.Address, invocation, result, tail));
                        break;
                    case Branch branch:
                        if (values.Recover(branch.Condition, out problem) is { Width: 1 } condition)
                            statements.Add(new ManagedBranch(branch.Address, condition, Edge(block, branch.Target), Edge(block, branch.Fallthrough)));
                        else problem ??= "分支条件不是布尔值";
                        break;
                    case Jump jump:
                        statements.Add(new ManagedJump(jump.Address, Edge(block, jump.Target)));
                        break;
                    case Return { Buffer: not null }: problem = "缓冲区返回尚未组装"; break;
                    case Return { Pieces.Length: > 0 }: problem = "聚合返回尚未组装"; break;
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
                if (successors.Length == 1) statements.Add(new ManagedJump(block.End, Edge(block, successors[0].Start)));
                else problems.Add(new(block.Start, "基本块没有唯一终结方式"));
            }
            blocks.Add(new(block.Start, statements));
        }
        if (problems.Count > 0) return new(null, problems);
        var body = new ManagedBody(prepared.Method, blocks);
        return new(recoverAccessors ? InlineAccessors.Recover(session, body) : body, problems);
    }
}
