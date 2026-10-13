namespace Cpp2CS.Native;

// 参数与继承链的类型绑定在方法分析入口完成，供 SSA 和表达式恢复共同使用。
public static class ManagedTypeBindings
{
    public static void Bind(NativeMethod method, Symbols symbols, HeaderLayout layouts, ManagedNames managed)
    {
        var signature = managed.SignatureOf(method.Name.Split("$$")[0], method.Name.Split("$$")[1]);
        var parameters = method.Parameters.Where(p => p.Name != "__this" && !(p.Name == "method" && p.Type.Contains("MethodInfo"))).ToArray();
        if (signature is { } known && known.ParameterTypes.Length == parameters.Length)
            for (var index = 0; index < parameters.Length; index++)
                if (parameters[index].Type.EndsWith('*')) symbols.DisplayTypes.TryAdd(parameters[index].Type.TrimEnd('*'), known.ParameterTypes[index]);
        foreach (var parameter in method.Parameters.Where(p => p.Type.EndsWith("_o*")))
        {
            var native = parameter.Type.TrimEnd('*');
            var logical = symbols.Display(native);
            while (layouts.ParentFields(native) is { } parent && managed.BaseTypeOf(logical) is { } logicalParent)
            {
                native = parent.EndsWith("_Fields") ? parent[..^7] + "_o" : parent;
                symbols.DisplayTypes.TryAdd(native, logicalParent);
                logical = logicalParent;
            }
        }
    }
}
