using Cpp2CS.Model;
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
    private HashSet<Instruction> compiledSites = [];
    private readonly HashSet<MethodDef> inlinedHere = [];
    private readonly HashSet<string> calledHere = [];
    private readonly HashSet<string> backingHere = [];
    private Func<MethodDef, MethodDefinition?> transparentAccessor = _ => null;
    public void SetAccessors(Func<MethodDef, MethodDefinition?> accessor) => transparentAccessor = accessor;

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

    private StackValue? InvokeAt(CilSide side, Instruction instruction, MethodRef callee, StackValue[] values)
    {
        if (compiledSites.Contains(instruction)) return InvokeCompiled(side, callee, values);
        return inlineSites.ContainsKey(instruction) && transparentInline.TryGetValue(callee.Method, out var inlined)
            ? Execute(side, inlined, callee, values, transparent: true, instanceBodies.GetValueOrDefault(callee))
            : Invoke(side, callee, values);
    }

    /// <summary>
    /// 换成 C# 的编译体来执行。编译体没有逐指令的内联标记，按恢复体里的调用点判断：
    /// 被调方法只出现在内联位置时透明执行；恢复体直接读写后备字段、C# 写成属性访问的，按访问器透明执行；其余是普通调用。
    /// 恢复体可能经接口或基类调用同一个访问器，所以调用按名字统计。同一目标两种写法都有时分不清对应关系，按不可检查处理。
    /// </summary>
    public void UseCompiled(MethodDefinition compiled, MethodDefinition recovered, MethodRef tested)
    {
        compiledSites = compiled.Body.Instructions.ToHashSet();
        inlinedHere.Clear();
        calledHere.Clear();
        backingHere.Clear();
        foreach (var instruction in recovered.Body.Instructions)
        {
            if (inlineSites.TryGetValue(instruction, out var inlined)) inlinedHere.Add(inlined.Method);
            // 原生库导入不在程序模型里，也不产生调用事件。
            else if (instruction is { OpCode.Code: Code.Call or Code.Callvirt or Code.Newobj, Operand: MethodReference target } && target.Resolve() is not { IsPInvokeImpl: true })
                calledHere.Add(target.Name);
            else if (instruction.Operand is FieldReference field) backingHere.Add(field.Name);
        }
    }

    private StackValue? InvokeCompiled(CilSide side, MethodRef callee, StackValue[] values)
    {
        var method = callee.Method;
        var inlined = inlinedHere.Contains(method);
        var accessor = !inlined && !method.IsOverridable && method.Name.Length > 4 && backingHere.Contains($"<{method.Name[4..]}>k__BackingField") ? transparentAccessor(method) : null;
        if (!inlined && accessor is null) return Invoke(side, callee, values);
        if (calledHere.Contains(method.Name)) throw new Unsupported($"{callee} 在恢复体里既有内联又有调用，编译体分不清");
        return accessor is not null
            ? Execute(side, accessor, callee, values, transparent: true)
            : Execute(side, transparentInline[method], callee, values, transparent: true, instanceBodies.GetValueOrDefault(callee));
    }

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
