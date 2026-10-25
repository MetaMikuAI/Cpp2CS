using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>语句与边的 CIL 写法：每种语句一处；边先读出全部复制的值，再写入目标局部。</summary>
public sealed partial class BodyEmitter
{
    private ulong statementAddress;

    private void Statement(ManagedStatement statement)
    {
        statementAddress = statement.Address;
        switch (statement)
        {
            case ManagedAssignment a: Value(a.Value); il.Emit(OpCodes.Stloc, Local(a.Target)); break;
            case ManagedStore { Target: IndirectValue i, Value: ComposedValue { Leaves.Count: 0 } }:
                Value(i.Address);
                var initialization = Instruction.Create(OpCodes.Initobj, TypeReference(i.Type));
                il.Append(initialization); ExplicitInitializations.Add(initialization); break;
            case ManagedStore { Target: IndirectValue i } s:
                Value(i.Address); Value(s.Value); il.Emit(OpCodes.Stobj, TypeReference(i.Type)); break;
            case ManagedStore { Target: FieldValue f } s:
                Value(f.Receiver); Value(s.Value);
                if (f.Accessor is { } setter) AccessorCall(setter); else il.Emit(OpCodes.Stfld, FieldReference(f.Field)); break;
            case ManagedStore { Target: StaticFieldValue f } s:
                Value(s.Value);
                if (f.Accessor is { } staticSetter) AccessorCall(staticSetter); else il.Emit(OpCodes.Stsfld, FieldReference(f.Field)); break;
            case ManagedStore { Target: ArrayElementValue element } s:
                Value(element.Array); Value(element.Index); Value(s.Value);
                il.Emit(OpCodes.Stelem_Any, TypeReference(element.Type)); break;
            case ManagedCall c:
                var call = Invocation(c.Invocation);
                if (c.Inlined) InlineCalls.Add(call, c.Invocation.Method);
                if (c.Tail) ReturnFromBlock();
                else if (c.Result is { } result) il.Emit(OpCodes.Stloc, Local(result));
                else if (!ManagedTypes.IsVoid(c.Invocation.Method.Method.ReturnType)) il.Emit(OpCodes.Pop);
                break;
            case ManagedReturn r:
                if (r.Value is { } returned) Value(returned);
                ReturnFromBlock(); break;
            case ManagedJump j: Edge(j.Edge); break;
            case ManagedBranch b:
                var taken = Instruction.Create(OpCodes.Nop);
                Value(b.Condition); il.Emit(OpCodes.Brtrue, taken);
                Edge(b.Fallthrough);
                il.Append(taken); Edge(b.Taken); break;
            case ManagedSwitch w:
            {
                // 越界不可达（原生代码在前驱中检查了上界）；落空时走第 0 项，保持每条路径都有出边。
                var cases = w.Cases.Select(_ => Instruction.Create(OpCodes.Nop)).ToArray();
                Value(w.Index); il.Emit(OpCodes.Switch, cases);
                Edge(w.Cases[0]);
                for (var i = 0; i < cases.Length; i++) { il.Append(cases[i]); Edge(w.Cases[i]); }
                break;
            }
            case ManagedThrow t: Value(t.Exception); il.Emit(OpCodes.Throw); break;
            case ManagedRethrow: il.Emit(OpCodes.Rethrow); break;
            case ManagedEndFault: il.Emit(OpCodes.Endfinally); break;
            case ManagedAwait awaited:
                Value(awaited.Task);
                var helpers = Awaits();
                if (awaited.Result is { } awaitedResult)
                {
                    il.Emit(OpCodes.Call, Generic(helpers.Of, awaited.Task.Type, awaitedResult.Type));
                    il.Emit(OpCodes.Stloc, Local(awaitedResult));
                }
                else il.Emit(OpCodes.Call, Generic(helpers.Do, awaited.Task.Type));
                break;
            case ManagedHole hole:
                il.Emit(OpCodes.Ldc_I8, unchecked((long)hole.Address));
                if (hole.Terminal) { il.Emit(OpCodes.Call, Unrecovered().Fail); il.Emit(OpCodes.Throw); }
                else il.Emit(OpCodes.Call, Unrecovered().At);
                break;
            case ManagedCheck check:
                var pass = Instruction.Create(OpCodes.Nop);
                Value(check.Condition); il.Emit(OpCodes.Brfalse, pass);
                il.Emit(OpCodes.Newobj, MethodReference(check.Exception)); il.Emit(OpCodes.Throw);
                il.Append(pass); break;
            default: throw new NotSupportedException(statement.ToString());
        }
    }

    /// <summary>洞标记只携带原生地址，完整原因留在 recovery.jsonl，避免诊断文本撑爆 #US 字符串堆。</summary>
    private (MethodReference At, MethodReference Fail, MethodDefinition Value) Unrecovered()
    {
        var module = destination.Module;
        if (unrecovered.TryGetValue(module, out var known)) return known;
        var type = new TypeDefinition("Cpp2CS", "Unrecovered", TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit, TypeReference(types.Object));
        module.Types.Add(type);
        MethodDefinition Method(string name, TypeReference returns)
        {
            var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig, returns);
            method.Parameters.Add(new ParameterDefinition("address", ParameterAttributes.None, TypeReference(types.UInt64)));
            var processor = method.Body.GetILProcessor();
            processor.Emit(OpCodes.Ldnull); processor.Emit(OpCodes.Throw);
            type.Methods.Add(method);
            return method;
        }
        var value = Method("Value", TypeReference(types.Object));
        var parameter = new GenericParameter("T", value);
        value.GenericParameters.Add(parameter);
        value.ReturnType = parameter;
        var created = (Method("At", TypeReference(types.Corlib("System.Void"))), Method("Fail", TypeReference(types.Corlib("System.Exception"))), value);
        unrecovered.Add(module, created);
        return created;
    }

    private GenericInstanceMethod Generic(MethodDefinition method, params TypeRef[] arguments)
    {
        var instance = new GenericInstanceMethod(method);
        foreach (var argument in arguments) instance.GenericArguments.Add(TypeReference(argument));
        return instance;
    }

    /// <summary>
    /// async 提升（<see cref="AsyncLifting"/>）的标记：每个模块一个 Cpp2CS.Await 静态类，C# 输出时改写成 await / return
    /// （Of&lt;TTask,TResult&gt;、Do&lt;TTask&gt; 是 await，Result、Completed 是 async 方法的 return；void 完成使用非泛型重载）。方法体只抛出。
    /// </summary>
    private (MethodDefinition Of, MethodDefinition Do, MethodDefinition Result, MethodDefinition Completed, MethodDefinition CompletedVoid) Awaits()
    {
        var module = destination.Module;
        if (awaits.TryGetValue(module, out var known)) return known;
        var type = new TypeDefinition("Cpp2CS", "Await", TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit, TypeReference(types.Object));
        module.Types.Add(type);
        MethodDefinition Method(string name, string[] parameters, Func<GenericParameter[], TypeReference> returns, Func<GenericParameter[], TypeReference[]> arguments)
        {
            var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig, TypeReference(types.Corlib("System.Void")));
            var generic = parameters.Select(p => new GenericParameter(p, method)).ToArray();
            foreach (var parameter in generic) method.GenericParameters.Add(parameter);
            method.ReturnType = returns(generic);
            foreach (var argument in arguments(generic)) method.Parameters.Add(new ParameterDefinition(argument));
            var processor = method.Body.GetILProcessor();
            processor.Emit(OpCodes.Ldnull); processor.Emit(OpCodes.Throw);
            type.Methods.Add(method);
            return method;
        }
        var created = (Method("Of", ["TTask", "TResult"], g => g[1], g => [g[0]]), Method("Do", ["TTask"], _ => TypeReference(types.Corlib("System.Void")), g => [g[0]]),
            Method("Result", ["TTask", "TResult"], g => g[0], g => [g[1]]), Method("Completed", ["TTask"], g => g[0], _ => []),
            Method("Completed", [], _ => TypeReference(types.Corlib("System.Void")), _ => []));
        awaits.Add(module, created);
        return created;
    }

    private void Edge(ManagedEdge edge)
    {
        foreach (var copy in edge.Copies) Value(copy.Value);
        for (var i = edge.Copies.Count - 1; i >= 0; i--) il.Emit(OpCodes.Stloc, Local(edge.Copies[i].Target));
        il.Emit(LeavesRegion(edge.Target) ? OpCodes.Leave : OpCodes.Br, labels[edge.Target]);
    }

    private Instruction Invocation(ManagedInvocation invocation)
    {
        if (invocation.Receiver is { } receiver) Value(receiver);
        foreach (var argument in invocation.Arguments) Value(argument);
        var call = Instruction.Create(invocation.Virtual ? OpCodes.Callvirt : OpCodes.Call, MethodReference(invocation.Method));
        il.Append(call);
        return call;
    }
}
