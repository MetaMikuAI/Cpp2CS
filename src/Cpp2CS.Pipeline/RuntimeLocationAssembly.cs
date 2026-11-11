using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Runtime;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Pipeline;

/// <summary>与默认前端共用一次创建的组件；恢复层不引用目标实现。</summary>
internal static class RuntimeLocationAssembly
{
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, Lazy<FrontendComponents>> components = [];
    internal static FrontendComponents Components(GlobalFacts facts, Func<GlobalFacts, FrontendComponents> create) =>
        components.GetValue(facts, f => new(() => create(f))).Value;

    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, Lazy<RuntimeFunctionLocations>> locations = [];
    internal static RuntimeFunctionLocations Locations(GlobalFacts facts) => locations.GetValue(facts, f => new(() => Locate(f))).Value;

    private static RuntimeFunctionLocations Locate(GlobalFacts facts)
    {
        var catalog = RuntimeFunctionCatalog.Select(facts.Spec.Layout.UnityVersion, facts.Spec.Layout.Triple, facts.Spec.Layout.DataModel);
        var parts = RecoverySession.DefaultComponents(facts);
        return RuntimeFunctionLocations.Locate(facts.Image, facts.Symbols, catalog,
            target => parts.Instructions is INoReturnInstructionSet resolver ? resolver.ResolveCallTarget(facts.Image, target) : target);
    }
}
