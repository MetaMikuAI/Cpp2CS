using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Analysis;

/// <summary>
/// F5 的异常值闭包：从 BeginCatch 的结果（wrapper）与 catch 对象出发，沿复制、wrapper+0 的 64 位加载与来源一致的 φ 传播。
/// wrapper 是运行时引用；wrapper+0 读出的是被捕获的托管异常对象。恢复器与类型引擎共用这一份结果。
/// </summary>
internal static class ExceptionValueClosure
{
    public static (Dictionary<Variable, LocalValue> Wrappers, Dictionary<Variable, LocalValue> Exceptions) Close(
        IEnumerable<Stmt> statements, IReadOnlyDictionary<Variable, LocalValue> wrapperSeeds, IReadOnlyDictionary<Variable, LocalValue> exceptionSeeds)
    {
        var wrappers = wrapperSeeds.ToDictionary();
        var exceptions = exceptionSeeds.ToDictionary();
        var all = statements.ToArray();
        var defines = all.OfType<Define>().ToArray();
        var phis = all.OfType<Phi>().ToArray();
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var define in defines)
            {
                if (define.Value is Use alias && wrappers.TryGetValue(alias.Variable, out var wrapper)) changed |= wrappers.TryAdd(define.Target, wrapper);
                if (define.Value is Load { Width: 64, Address: Use address } && wrappers.TryGetValue(address.Variable, out var caught)) changed |= exceptions.TryAdd(define.Target, caught);
                if (define.Value is Use copied && exceptions.TryGetValue(copied.Variable, out var exception)) changed |= exceptions.TryAdd(define.Target, exception);
            }
            foreach (var phi in phis)
            {
                var sources = phi.Sources.Where(v => v != phi.Target).Distinct().ToArray();
                if (sources.Length == 0) continue;
                if (sources.All(wrappers.ContainsKey) && sources.Select(v => wrappers[v]).Distinct().ToArray() is [var wrapper]) changed |= wrappers.TryAdd(phi.Target, wrapper);
                if (sources.All(exceptions.ContainsKey) && sources.Select(v => exceptions[v]).Distinct().ToArray() is [var exception]) changed |= exceptions.TryAdd(phi.Target, exception);
            }
        }
        return (wrappers, exceptions);
    }
}
