using System.Collections.Immutable;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private MethodRef? RuntimeMethod(ClassifiedCall call, string input)
    {
        if (valueNames is null || call.Inputs?.GetValueOrDefault(input)?.Source is not TermSource term) return null;
        var named = context.Get(valueNames, term.Term);
        return named.IsSuccess ? named.Value.Name switch
        {
            EntityName { Entity: MethodEntity entity } => entity.Method,
            ParameterName { MethodInformation: true } => method,
            _ => null,
        } : null;
    }

    private void PrepareProfileException(Call call, ClassifiedCall classified)
    {
        Fail<object>(LoweringFailureKind.RuntimeCall,
            "运行时 profile 桩替换了原托管实现及异常；当前不能把该替代桩作为已恢复的托管方法体",
            code: "lowering.Profile.Unavailable");
    }

    private void PrepareGetType(Call call, ClassifiedCall classified)
    {
        var target = RuntimeMethod(classified, "target");
        var caller = RuntimeMethod(classified, "caller");
        if (caller is null || caller.Method.Owner.Assembly != method.Method.Owner.Assembly)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "类型查找的提示程序集与当前输出调用位置不一致或未命名", code: "lowering.GetType.Caller"); return; }
        if (target is null || target.Method.Owner is not { Assembly: "mscorlib.dll", FullName: "System.Type" }
            || !target.Method.IsStatic || target.Method.Name != "GetType" || target.Method.GenericParameters.Count != 0
            || target.Method.Parameters.Count is < 1 or > 3 || target.Method.ReturnType is not DefinitionRef { Definition.FullName: "System.Type" }
            || target.Method.Parameters.Where((p, i) => p.Type is not DefinitionRef d
                || d.Definition.Assembly != "mscorlib.dll" || d.Definition.FullName != (i == 0 ? "System.String" : "System.Boolean")).Any()
            || classified.Binding is not { } binding || binding.Arguments.Length != target.Method.Parameters.Count + 2)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "类型查找目标不是与运行时输入一致的 System.Type.GetType 重载", code: "lowering.GetType.Method"); return; }
        int count = target.Method.Parameters.Count;
        var signature = binder.Classify(binding.Signature.Signature with
            { Parameters = binding.Signature.Signature.Parameters.Take(count).ToImmutableArray() });
        if (signature.Value is not { } classifiedSignature)
        { Fail<object>(LoweringFailureKind.Binding, signature.Failure!.Detail, code: "lowering.GetType.Binding"); return; }
        var bound = binding with { Signature = classifiedSignature, Arguments = binding.Arguments.Take(count).ToImmutableArray() };
        var definition = new CallDefinition(target, bound);
        callDefinitions.Add(call.Identity, definition);
        if (bound.Result.Source is TermSource output) callResults.Add(output.Term, definition);
    }

    private void PrepareUncheckedUnbox(Call call, ClassifiedCall classified)
    {
        if (classified.Inputs?.GetValueOrDefault("object") is not { Source: TermSource input } obj
            || classified.Result?.Source is not TermSource output)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "无检查拆箱的对象或结果没有完整绑定", code: "lowering.UnboxUnchecked.Binding"); return; }
        var resolved = context.Get(state.Resolve, input.Term);
        var box = resolved.IsSuccess && resolved.Value.Identity is ResultAtom { Definition: CallIdentity id } && calls is not null
            ? context.Get(calls, id) : default;
        if (!box.IsSuccess || box.Value.Operation?.Il.Name != "Box")
        { Fail<object>(LoweringFailureKind.RuntimeCall, "无检查拆箱尚无非空盒及其精确值类型的凭据", code: "lowering.UnboxUnchecked.Type"); return; }
        var type = RuntimeClass(box.Value, "lowering.UnboxUnchecked.Type");
        if (type is null || BoxedScalar(type, "UnboxUnchecked") is null) return;
        unboxes.Add(call.Identity, new(obj, type, output.Term, new(new(nextLocal++), type, types.Size(type) * 8)));
    }
}
