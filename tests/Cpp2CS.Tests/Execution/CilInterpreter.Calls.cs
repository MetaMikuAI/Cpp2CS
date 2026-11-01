using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>调用点的执行。恢复管线没有访问器与内联认回，调用点一律按普通调用执行。</summary>
internal sealed partial class CilInterpreter
{
    private StackValue? InvokeAt(CilSide side, Instruction instruction, MethodRef callee, StackValue[] values) => Invoke(side, callee, values);

    /// <summary>执行前须准备的、经内建模型读写的静态字段：没有。</summary>
    public IEnumerable<FieldRef> IntrinsicStatics(MethodDefinition method) => [];

    /// <summary>执行时会解释的全部指令：方法体自身。</summary>
    public IEnumerable<Instruction> ExpandedInstructions(MethodDefinition method) => method.Body.Instructions;
}
