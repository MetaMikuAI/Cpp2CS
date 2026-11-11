using Cpp2CS.Model;
using Mono.Cecil;
namespace Cpp2CS.Tests.Execution;
internal static partial class CilComparison
{
    /// <summary>奇数种子先枚举左侧可达调用；计划冻结后交给两侧，不能根据右侧行为调整。</summary>
    private static ThrowPlan? ThrowPlanFor(MethodDefinition definition, MethodRef method, CilInterpreter interpreter, WorldIndex index, Hints hints, int seed)
    {
        if ((seed & 1) == 0 || !definition.Body.HasExceptionHandlers) return null;
        var world = new World(index, seed, hints, method.DeclaringType);
        var pilot = interpreter.Run(world, definition, method, Arguments(world, interpreter, method));
        var calls = pilot.ProtectedCallEvents.Order().ToArray();
        if (calls.Length == 0) calls = Enumerable.Range(0, pilot.CallEvents).ToArray();
        if (calls.Length == 0) return null;
        var exception = index.Types.Corlib("System.Exception");
        var choices = hints.Types.Concat([exception, index.Types.Corlib("System.InvalidOperationException"), index.Types.Corlib("System.NullReferenceException")])
            .Where(t => t is DefinitionRef d && (d.Definition.Attributes & System.Reflection.TypeAttributes.Abstract) == 0 && index.Types.IsAssignable(t, exception)).Distinct().ToArray();
        var ordinal = (int)((uint)seed / 2);
        return new(calls[ordinal % calls.Length], choices[ordinal % choices.Length]);
    }
}
