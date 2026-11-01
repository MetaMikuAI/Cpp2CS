using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// 调用点的执行。写出时标为透明的构造（内联证明：原生代码内联了被调构造函数）按被调方法的方法体透明执行，
/// 不产生调用与返回事件；其余调用点按普通调用执行。
/// </summary>
internal sealed partial class CilInterpreter
{
    private IReadOnlyDictionary<Instruction, MethodRef> inlineSites = new Dictionary<Instruction, MethodRef>();
    private readonly Dictionary<MethodDef, MethodDefinition> transparentInline = [];

    public void SetInline(Output.BodyEmitter emitter, Output.Skeleton skeleton)
    {
        inlineSites = emitter.InlineCalls;
        transparentInline.Clear();
        foreach (var method in inlineSites.Values) transparentInline[method.Method] = skeleton.Method(method.Method);
    }

    private StackValue? InvokeAt(CilSide side, Instruction instruction, MethodRef callee, StackValue[] values) =>
        inlineSites.ContainsKey(instruction) && transparentInline.TryGetValue(callee.Method, out var inlined)
            ? Execute(side, inlined, callee, values, transparent: true)
            : Invoke(side, callee, values);

    /// <summary>执行前须准备的、经内建模型读写的静态字段：没有。</summary>
    public IEnumerable<FieldRef> IntrinsicStatics(MethodDefinition method) => [];

    /// <summary>执行时会解释的全部指令：方法体自身。</summary>
    public IEnumerable<Instruction> ExpandedInstructions(MethodDefinition method) => method.Body.Instructions;
}
