using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;

namespace Cpp2CS.Tests.Execution;

internal static partial class ExecutionCheck
{
    /// <summary>
    /// 半数种子先执行不注入的 CIL，只用于枚举可达调用事件；计划随后冻结，两侧共享。
    /// 变异前建立同一份计划，不能根据变异后的行为改变抛出位置或异常类型。
    /// </summary>
    private static ThrowPlan?[] ThrowPlans(MethodRef tested, MethodDefinition definition, CecilModel cecil, CilInterpreter interpreter, WorldIndex index, bool preferProtected = true, int caseCount = Cases)
    {
        var plans = new ThrowPlan?[caseCount];
        if (!definition.Body.HasExceptionHandlers) return plans;
        var hints = HintsOf(definition, cecil);
        var exception = index.Types.Corlib("System.Exception");
        var choices = hints.Types.Concat(new[] { exception, index.Types.Corlib("System.InvalidOperationException"), index.Types.Corlib("System.NullReferenceException") })
            .Where(t => t is DefinitionRef d && (d.Definition.Attributes & System.Reflection.TypeAttributes.Abstract) == 0 && index.Types.IsAssignable(t, exception)).Distinct().ToArray();
        var signature = index.StructAbi.Signature(tested);
        var statics = interpreter.ExpandedInstructions(definition).Where(i => i.OpCode.Code is Mono.Cecil.Cil.Code.Ldsfld or Mono.Cecil.Cil.Code.Stsfld or Mono.Cecil.Cil.Code.Ldsflda)
            .Select(i => cecil.Field((FieldReference)i.Operand)).Concat(interpreter.IntrinsicStatics(definition)).Distinct().ToArray();
        for (var seed = 1; seed < caseCount; seed += 2)
        {
            var world = new World(index, seed, hints, InitializedOwner(tested));
            try
            {
                foreach (var field in statics) world.PrepareStatic(field);
                var (_, values) = Arguments(world, interpreter, tested, signature);
                var pilot = interpreter.Run(world, definition, tested, values);
                var calls = preferProtected ? pilot.ProtectedCallEvents.Order().ToArray() : [];
                if (calls.Length == 0) calls = Enumerable.Range(0, pilot.CallEvents).ToArray();
                if (calls.Length > 0) plans[seed] = new(calls[(seed / 2) % calls.Length], choices[(seed / 2) % choices.Length]);
            }
            catch (Unsupported) { }
        }
        return plans;
    }
}
