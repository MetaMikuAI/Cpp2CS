using Cpp2CS.Model;
using Mono.Cecil;
using Mono.Cecil.Cil;
namespace Cpp2CS.Tests.Execution;
internal sealed partial class CilInterpreter
{
    public ModuleDefinition? BodyModule { get; set; }
    private int depth;
    private StackValue? InvokeAt(CilSide side, Instruction instruction, MethodRef callee, StackValue[] values)
    {
        // 核心库无参异常构造与隐式检查共用异常对象抽象，不取决于被测模块是否恰是核心库。
        if (callee.Method is { Name: ".ctor", Parameters.Count: 0, Owner.Assembly: "mscorlib.dll" }
            && Side.InExceptionRegion(values[0].Bits)) return null;
        if (BodyModule is { } module && model.Body(callee, module) is { } body)
        {
            if (depth >= 128) throw new Unsupported("CIL 调用深度预算耗尽", ComparisonReason.CallDepthBudget);
            depth++;
            try { return Execute(side, body, callee, values, transparent: true); }
            finally { depth--; }
        }
        if (callee.Method is { Name: ".ctor", Owner.FullName: "System.Object", Parameters.Count: 0 }) return null;
        return Invoke(side, callee, values);
    }
}
