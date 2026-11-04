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
    private readonly Dictionary<MethodRef, MethodBody> instanceBodies = [];

    /// <summary>
    /// 透明执行的调用点：内联证明成立的构造（InlineCalls）与被内联的访问器（AccessorCalls）。
    /// 泛型定义只按一个见证写出，而值类型实例有单独编译的原生代码（只对引用类型成立的分支已被折叠）。
    /// 被内联的是这个实例，所以按它自己的恢复体执行。
    /// </summary>
    public void SetInline(Output.BodyEmitter emitter, Output.Skeleton skeleton, Func<MethodRef, MethodBody?> ownBody)
    {
        transparentInline.Clear();
        instanceBodies.Clear();
        var seen = new HashSet<MethodRef>();
        // 实例体里还可能有内联调用，写成后继续处理新出现的调用点。
        while (emitter.InlineCalls.Values.Concat(emitter.AccessorCalls.Values.Select(a => a.Method)).Where(seen.Add).ToArray() is { Length: > 0 } methods)
            foreach (var method in methods)
            {
                transparentInline[method.Method] = skeleton.Method(method.Method);
                if (ownBody(method) is { } body) instanceBodies[method] = body;
            }
        var sites = new Dictionary<Instruction, MethodRef>(emitter.InlineCalls);
        foreach (var (instruction, accessor) in emitter.AccessorCalls) sites[instruction] = accessor.Method;
        inlineSites = sites;
    }

    private StackValue? InvokeAt(CilSide side, Instruction instruction, MethodRef callee, StackValue[] values) =>
        inlineSites.ContainsKey(instruction) && transparentInline.TryGetValue(callee.Method, out var inlined)
            ? Execute(side, inlined, callee, values, transparent: true, instanceBodies.GetValueOrDefault(callee))
            : Invoke(side, callee, values);

    /// <summary>按每个透明调用的泛型上下文收集静态字段；同一定义的不同实例分别准备输入。</summary>
    public IEnumerable<FieldRef> StaticFields(MethodDefinition definition, MethodRef instance)
    {
        var pending = new Queue<(MethodBody, MethodRef)>();
        var seen = new HashSet<MethodRef>();
        pending.Enqueue((definition.Body, instance));
        while (pending.TryDequeue(out var next))
        {
            if (!seen.Add(next.Item2)) continue;
            var context = model.InContext(next.Item2);
            foreach (var instruction in next.Item1.Instructions)
            {
                if (instruction.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda)
                    yield return context.Field((FieldReference)instruction.Operand);
                if (inlineSites.ContainsKey(instruction) && instruction.Operand is MethodReference called)
                {
                    var method = context.Method(called);
                    if (transparentInline.TryGetValue(method.Method, out var body)) pending.Enqueue((instanceBodies.GetValueOrDefault(method) ?? body.Body, method));
                }
            }
        }
    }

}
