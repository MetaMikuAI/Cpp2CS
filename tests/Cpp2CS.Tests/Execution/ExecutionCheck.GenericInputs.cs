using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

internal static partial class ExecutionCheck
{
    /// <summary>共享引用入口：用二进制实际引用的实例补足接口输入，避免占位类型只产生 null 路径。</summary>
    private static MethodRef ConcreteGenericInput(MethodRef original, ulong entry, WorldIndex index)
    {
        var arguments = original.TypeArguments.Concat(original.MethodArguments).ToArray();
        if (arguments.Length == 0 || arguments.Any(t => !ManagedTypes.IsReferenceType(t) || FieldLayouts.IsFullyShared(t))) return original;
        int Score(MethodRef method) => StructAbi.ArgumentTypes(method).OfType<DefinitionRef>()
            .Count(t => t.Definition.IsInterface && index.Concrete(t).Length > 0);
        var score = Score(original);
        var candidates = index.Facts.Usages.Slots.Values
            .Where(s => s.Usage.Value is MethodRef m && m.Method == original.Method)
            .Select(s => (Slot: s.Address, Method: (MethodRef)s.Usage.Value))
            .Where(p => p.Method.TypeArguments.Concat(p.Method.MethodArguments)
                .All(t => ManagedTypes.IsReferenceType(t) && !FieldLayouts.IsFullyShared(t)))
            .Where(p => index.CodeAddress(p.Method) == entry)
            .Select(p => (p.Slot, p.Method, Score: Score(p.Method)))
            .Where(p => p.Score > score).OrderByDescending(p => p.Score).ThenBy(p => p.Slot).ToArray();
        if (candidates.Length == 0) return original;
        var selected = candidates[0];
        Console.WriteLine($"  泛型输入实例 0x{entry:x}：{selected.Method}；原生元数据槽 0x{selected.Slot:x}；可构造接口输入 {score} -> {selected.Score}");
        return selected.Method;
    }
}
