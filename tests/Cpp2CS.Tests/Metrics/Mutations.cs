using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Metrics;

internal enum MutationKind { IntegerConstant, InvertBranch, AddSubtract, RemoveFieldWrite, RemoveCall, DefaultReturn, SwapArguments }
internal sealed record Mutation(MutationKind Kind, int Index, int Offset, int FirstArgument = -1, int SecondArgument = -1);

/// <summary>每类取方法中第一个可表达的改动；一次只改一个位置，保持求值栈和分支引用合法。</summary>
internal static class Mutations
{
    public static IEnumerable<Mutation> Generate(MethodDefinition method)
    {
        if (!method.HasBody) yield break;
        var seen = new HashSet<MutationKind>();
        for (var n = 0; n < method.Body.Instructions.Count; n++)
        {
            var i = method.Body.Instructions[n];
            var kinds = new List<MutationKind>();
            if (Integer(i) is not null) kinds.Add(MutationKind.IntegerConstant);
            if (i.OpCode.FlowControl == FlowControl.Cond_Branch && i.Operand is Instruction) kinds.Add(MutationKind.InvertBranch);
            if (i.OpCode.Code is Code.Add or Code.Sub) kinds.Add(MutationKind.AddSubtract);
            var prefixed = i.Previous?.OpCode.OpCodeType == OpCodeType.Prefix;
            if (!prefixed && i.OpCode.Code is Code.Stfld or Code.Stsfld) kinds.Add(MutationKind.RemoveFieldWrite);
            if (!prefixed && i.OpCode.Code is Code.Call or Code.Callvirt && i.Operand is MethodReference call && !call.ContainsGenericParameter && call.ReturnType is not ByReferenceType)
            {
                kinds.Add(MutationKind.RemoveCall);
                var pair = (from a in Enumerable.Range(0, call.Parameters.Count)
                            from b in Enumerable.Range(a + 1, call.Parameters.Count - a - 1)
                            where IlMetrics.TypeKey(call.Parameters[a].ParameterType, method.Module) == IlMetrics.TypeKey(call.Parameters[b].ParameterType, method.Module)
                            select (a, b)).Take(1).ToArray();
                if (pair.Length != 0 && seen.Add(MutationKind.SwapArguments))
                    yield return new(MutationKind.SwapArguments, n, i.Offset, pair[0].a, pair[0].b);
            }
            if (i.OpCode.Code == Code.Ret && method.ReturnType.MetadataType != MetadataType.Void && !method.ReturnType.ContainsGenericParameter && method.ReturnType is not ByReferenceType)
                kinds.Add(MutationKind.DefaultReturn);
            foreach (var kind in kinds)
                if (seen.Add(kind)) yield return new(kind, n, i.Offset);
        }
    }
    private static long? Integer(Instruction i) => i.OpCode.Code switch
    {
        Code.Ldc_I4 => (int)i.Operand, Code.Ldc_I4_S => (sbyte)i.Operand, Code.Ldc_I8 => (long)i.Operand,
        >= Code.Ldc_I4_M1 and <= Code.Ldc_I4_8 => i.OpCode.Code - Code.Ldc_I4_0, _ => null
    };
    public static MethodBody Changed(MethodDefinition method, Mutation mutation)
    {
        var body = Clone(method);
        var at = body.Instructions[mutation.Index];
        var code = at.OpCode.Code;
        var originalOperand = at.Operand;
        var replacement = new List<Instruction>();
        void Default(TypeReference type)
        {
            var local = new VariableDefinition(type);
            body.Variables.Add(local);
            replacement.Add(Instruction.Create(OpCodes.Ldloca, local));
            replacement.Add(Instruction.Create(OpCodes.Initobj, type));
            replacement.Add(Instruction.Create(OpCodes.Ldloc, local));
        }
        switch (mutation.Kind)
        {
            case MutationKind.IntegerConstant:
                replacement.Add(code == Code.Ldc_I8 ? Instruction.Create(OpCodes.Ldc_I8, unchecked(Integer(at)!.Value + 1))
                    : Instruction.Create(OpCodes.Ldc_I4, unchecked((int)(Integer(at)!.Value + 1)))); break;
            case MutationKind.InvertBranch:
                // 保留原比较的有符号/无符号/NaN 语义，只交换两个出口。
                replacement.Add(Instruction.Create(at.OpCode, body.Instructions[mutation.Index + 1]));
                replacement.Add(Instruction.Create(OpCodes.Br, (Instruction)originalOperand));
                break;
            case MutationKind.AddSubtract: replacement.Add(Instruction.Create(code == Code.Add ? OpCodes.Sub : OpCodes.Add)); break;
            case MutationKind.RemoveFieldWrite:
                replacement.Add(Instruction.Create(OpCodes.Pop));
                if (code == Code.Stfld) replacement.Add(Instruction.Create(OpCodes.Pop));
                break;
            case MutationKind.RemoveCall:
            {
                var call = (MethodReference)originalOperand;
                for (var n = 0; n < call.Parameters.Count + (call.HasThis ? 1 : 0); n++) replacement.Add(Instruction.Create(OpCodes.Pop));
                if (call.ReturnType.MetadataType != MetadataType.Void) Default(call.ReturnType);
                break;
            }
            case MutationKind.DefaultReturn:
                replacement.Add(Instruction.Create(OpCodes.Pop)); Default(method.ReturnType); replacement.Add(Instruction.Create(OpCodes.Ret)); break;
            case MutationKind.SwapArguments:
            {
                var call = (MethodReference)originalOperand;
                var locals = call.Parameters.Select(p => new VariableDefinition(p.ParameterType)).ToArray();
                foreach (var local in locals) body.Variables.Add(local);
                for (var n = locals.Length - 1; n >= 0; n--) replacement.Add(Instruction.Create(OpCodes.Stloc, locals[n]));
                for (var n = 0; n < locals.Length; n++) replacement.Add(Instruction.Create(OpCodes.Ldloc,
                    locals[n == mutation.FirstArgument ? mutation.SecondArgument : n == mutation.SecondArgument ? mutation.FirstArgument : n]));
                replacement.Add(Instruction.Create(at.OpCode, call)); break;
            }
        }
        if (replacement.Count == 0) replacement.Add(Instruction.Create(OpCodes.Nop));
        at.OpCode = replacement[0].OpCode; at.Operand = replacement[0].Operand;
        for (var n = 1; n < replacement.Count; n++) body.Instructions.Insert(mutation.Index + n, replacement[n]);
        return body;
    }
    private static MethodBody Clone(MethodDefinition method)
    {
        var source = method.Body;
        var body = new MethodBody(method) { InitLocals = source.InitLocals, MaxStackSize = source.MaxStackSize + 4 };
        foreach (var v in source.Variables) body.Variables.Add(new(v.VariableType));
        var map = source.Instructions.ToDictionary(i => i, i => Instruction.Create(OpCodes.Nop));
        foreach (var i in source.Instructions)
        {
            var copy = map[i]; copy.OpCode = i.OpCode;
            copy.Operand = i.Operand switch { Instruction target => map[target], Instruction[] targets => targets.Select(t => map[t]).ToArray(),
                VariableDefinition v => body.Variables[v.Index], _ => i.Operand };
            body.Instructions.Add(copy);
        }
        Instruction? Map(Instruction? i) => i is null ? null : map[i];
        foreach (var h in source.ExceptionHandlers) body.ExceptionHandlers.Add(new(h.HandlerType)
        {
            TryStart = Map(h.TryStart), TryEnd = Map(h.TryEnd), HandlerStart = Map(h.HandlerStart), HandlerEnd = Map(h.HandlerEnd),
            FilterStart = Map(h.FilterStart), CatchType = h.CatchType
        });
        return body;
    }
}
