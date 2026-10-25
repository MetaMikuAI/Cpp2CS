using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static partial class ExecutionCheck
{
    [MutationFamily("异常", 50)]
    private static IEnumerable<(string, Action, Action)> ExceptionFamily(MutationSite site) => ExceptionMutations(site.Method);

    internal static IEnumerable<(string, Action, Action)> ExceptionMutations(MethodDefinition method)
    {
        if (!method.Body.HasExceptionHandlers) yield break;
        var instructions = method.Body.Instructions.ToArray();
        var positions = instructions.Select((i, n) => (i, n)).ToDictionary(p => p.i, p => p.n);
        var reachable = new HashSet<Instruction>();
        var pending = new Stack<Instruction>(method.Body.ExceptionHandlers.Select(h => h.HandlerStart).Prepend(instructions[0]));
        while (pending.TryPop(out var instruction))
        {
            if (!reachable.Add(instruction)) continue;
            if (instruction.Operand is Instruction target) pending.Push(target);
            if (instruction.OpCode.FlowControl is not (FlowControl.Return or FlowControl.Throw or FlowControl.Branch) && instruction.Next is { } next) pending.Push(next);
        }
        bool In(Instruction instruction, Instruction start, Instruction? end) => positions[instruction] >= positions[start]
            && (end is null || positions[instruction] < positions[end]);
        string Membership(Instruction i) => string.Join(",", method.Body.ExceptionHandlers.Select((h, n) =>
            In(i, h.TryStart, h.TryEnd) ? $"{n}t" : In(i, h.HandlerStart, h.HandlerEnd) ? $"{n}h" : ""));
        // 吞掉异常必须真正转向区域外返回，不能跳回 finally 续接点再次抛出或陷入循环。
        var returnExit = instructions.FirstOrDefault(i => i.OpCode.Code == Code.Nop && Membership(i).All(c => c == ',')
            && instructions.Skip(positions[i] + 1).TakeWhile(n => n.OpCode.Code != Code.Nop
                && n.OpCode.FlowControl is not (FlowControl.Branch or FlowControl.Cond_Branch or FlowControl.Throw)).Any(n => n.OpCode.Code == Code.Ret));
        foreach (var handler in method.Body.ExceptionHandlers)
        {
            var old = handler.TryStart;
            // 缩小一个最内层 try 的前缀，直到首个可能抛出调用之后的块边界。
            if (method.Body.ExceptionHandlers.Any(h => h != handler && In(h.TryStart, handler.TryStart, handler.TryEnd))) continue;
            // RunClassConstructor 是类初始化簿记，无参异常 newobj 是显式判空的 throw，
            // 都不消费抛出计划的调用事件。移动包含实际托管 call/callvirt 的块。
            var call = instructions.FirstOrDefault(i => In(i, handler.TryStart, handler.TryEnd)
                && i.OpCode.Code is Code.Call or Code.Callvirt && i.Operand is MethodReference callee
                && !(callee.Name == "RunClassConstructor" && callee.DeclaringType.FullName == "System.Runtime.CompilerServices.RuntimeHelpers"));
            var next = call is null ? null : instructions.Skip(positions[call] + 1).FirstOrDefault(i => i.OpCode.Code == Code.Nop && In(i, handler.TryStart, handler.TryEnd));
            if (next is not null)
                yield return ($"F5 块移出 try #{positions[old]} → #{positions[next]}", () => handler.TryStart = next, () => handler.TryStart = old);
        }
        var leaves = instructions.Where(i => i.OpCode.Code is Code.Leave or Code.Leave_S).ToArray();
        foreach (var instruction in instructions.Where(i => reachable.Contains(i) && i.OpCode.Code == Code.Rethrow))
        {
            var exit = returnExit;
            if (exit is null) continue;
            yield return ($"F5 删去 rethrow #{positions[instruction]}",
                () => { instruction.OpCode = OpCodes.Leave; instruction.Operand = exit; },
                () => { instruction.OpCode = OpCodes.Rethrow; instruction.Operand = null; });
        }
        // 此项针对存下的异常对象重抛；newobj Exception; throw 属于判空/显式新抛出，
        // 不是任务要求的“把重抛改为吞掉”，不混进这个变异种类。
        foreach (var instruction in instructions.Where(i => reachable.Contains(i) && i.OpCode.Code == Code.Throw
            && i.Previous?.OpCode.Code is Code.Ldloc or Code.Ldloc_S or Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or Code.Ldloc_3))
        {
            var exit = returnExit;
            if (exit is null) continue;
            var leave = Instruction.Create(OpCodes.Leave, exit);
            yield return ($"F5 重抛改为吞掉 #{positions[instruction]}",
                () => { instruction.OpCode = OpCodes.Pop; method.Body.GetILProcessor().InsertAfter(instruction, leave); },
                () => { method.Body.GetILProcessor().Remove(leave); instruction.OpCode = OpCodes.Throw; });
        }
        for (var i = 0; i < leaves.Length; i++)
            for (var j = i + 1; j < leaves.Length; j++)
            {
                var left = leaves[i]; var right = leaves[j];
                var a = (Instruction)left.Operand; var b = (Instruction)right.Operand;
                if (a == b || Membership(a) != Membership(b)) continue;
                yield return ($"F5 交换 leave 目标 #{positions[left]}/#{positions[right]}",
                    () => { left.Operand = b; right.Operand = a; }, () => { left.Operand = a; right.Operand = b; });
            }
    }
}
