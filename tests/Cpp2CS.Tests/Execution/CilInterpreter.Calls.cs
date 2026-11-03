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

    /// <summary>透明执行的调用点：内联证明成立的构造（InlineCalls）与被内联的访问器（AccessorCalls）。</summary>
    public void SetInline(Output.BodyEmitter emitter, Output.Skeleton skeleton)
    {
        var sites = new Dictionary<Instruction, MethodRef>(emitter.InlineCalls);
        foreach (var (instruction, accessor) in emitter.AccessorCalls) sites[instruction] = accessor.Method;
        inlineSites = sites;
        transparentInline.Clear();
        foreach (var method in inlineSites.Values) transparentInline[method.Method] = skeleton.Method(method.Method);
    }

    private StackValue? InvokeAt(CilSide side, Instruction instruction, MethodRef callee, StackValue[] values) =>
        inlineSites.ContainsKey(instruction) && transparentInline.TryGetValue(callee.Method, out var inlined)
            ? Execute(side, inlined, callee, values, transparent: true)
            : Invoke(side, callee, values);

    /// <summary>按每个透明调用的泛型上下文收集静态字段；同一定义的不同实例分别准备输入。</summary>
    public IEnumerable<FieldRef> StaticFields(MethodDefinition definition, MethodRef instance)
    {
        var pending = new Queue<(MethodDefinition, MethodRef)>();
        var seen = new HashSet<MethodRef>();
        pending.Enqueue((definition, instance));
        while (pending.TryDequeue(out var next))
        {
            if (!seen.Add(next.Item2)) continue;
            var context = model.InContext(next.Item2);
            foreach (var instruction in next.Item1.Body.Instructions)
            {
                if (instruction.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda)
                    yield return context.Field((FieldReference)instruction.Operand);
                if (inlineSites.ContainsKey(instruction) && instruction.Operand is MethodReference called)
                {
                    var method = context.Method(called);
                    if (transparentInline.TryGetValue(method.Method, out var body)) pending.Enqueue((body, method));
                }
            }
        }
    }

}
