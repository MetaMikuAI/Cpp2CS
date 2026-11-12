using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Runtime;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Pipeline;

/// <summary>模型及代码地图建立后只读；层不得修改其中的集合。</summary>
public sealed record GlobalFacts(IImage Image, ProgramModel Model, Registrations CodeMap, RuntimeSpec Spec, string Architecture)
{
    /// <summary>同一次构建的符号伴随文件提供的函数身份；未提供时为空，定位不读取函数符号。</summary>
    public ImmutableArray<FunctionSymbol> Symbols { get; init; } = [];
    /// <summary>运行时函数身份；按映像建立一次，导入查询包含 PLT 归一。</summary>
    public Cpp2CS.Recovery.RuntimeFunctions.RuntimeFunctionLocations RuntimeFunctions => RuntimeLocationAssembly.Locations(this);
    /// <summary>有处理入口的原生异常区域，按地址查询。</summary>
    public TryRegionIndex HandlerRegions { get; } = new(Image.TryRegions);
    /// <summary>映像的函数范围按起点索引。</summary>
    public ILookup<ulong, FunctionRange> FunctionsByStart { get; } = Image.Functions.ToLookup(f => f.Start);
}
public sealed record MethodContext(MethodDef Method, CodeEntry Entry, GlobalFacts Facts);
public sealed record Hole(string Layer, ulong Position, string Step, Reason Reason, bool Derived = false);
public abstract record StageResult<T> where T : class;
public sealed record Completed<T>(T Value) : StageResult<T> where T : class;
public sealed record Missing<T>(Hole Hole) : StageResult<T> where T : class;
/// <summary>实现必须可并发调用；失败是洞，异常是程序错误（会话把它记入汇总并以失败退出）。</summary>
public interface IMethodStage<TInput, TOutput> where TOutput : class
{
    string Name { get; }
    StageResult<TOutput> Run(TInput input, MethodContext context);
}
public sealed record FrontendComponents(IInstructionSet Instructions, RegisterConvention Convention, IFlowFacts Flow);
/// <summary>一次运行（一份全局事实）创建一次组件，全部方法共用，组件必须可并发使用；架构键与全局事实的 Architecture 一致。</summary>
public interface IFrontendProvider
{
    string Architecture { get; }
    FrontendComponents Create(GlobalFacts facts);
}
public sealed record FrontendProvider(string Architecture, Func<GlobalFacts, FrontendComponents> Factory) : IFrontendProvider
{
    public FrontendComponents Create(GlobalFacts facts) => Factory(facts);
}
public sealed class FrontendStage(IEnumerable<IFrontendProvider> providers) : IMethodStage<CodeEntry, NativeFunction>
{
    private readonly IReadOnlyDictionary<string, IFrontendProvider> providers = providers.ToDictionary(p => p.Architecture, StringComparer.Ordinal);
    // 全映像的分析（不返回的函数等）在组件创建时做一次。
    private readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, Lazy<FrontendComponents>> components = [];
    public string Name => "前端";
    public StageResult<NativeFunction> Run(CodeEntry input, MethodContext context)
    {
        Missing<NativeFunction> Fail(string code, string message) => new(new(Name, input.Address, "提升", new(code, message)));
        if (!providers.TryGetValue(context.Facts.Architecture, out var provider))
            return Fail("frontend.unavailable", "该架构的前端尚未接入");
        var ranges = context.Facts.FunctionsByStart[input.Address].ToArray();
        if (ranges.Length != 1) return Fail("frontend.function_range", "入口没有唯一的映像函数范围");
        var parts = components.GetValue(context.Facts, facts => new(() => provider.Create(facts))).Value;
        var result = FunctionLifter.Lift(parts.Instructions, parts.Convention, parts.Flow, ranges[0], input.Address);
        return result.Function is { } function ? new Completed<NativeFunction>(function)
            : new Missing<NativeFunction>(new(Name, result.Failure!.Address, "提升", result.Failure.Reason));
    }
}
/// <summary>恢复成功必须给出开放定义的方法体；实例体不能直接发布为定义体。</summary>
public sealed class UnavailableRecoveryStage : IMethodStage<NativeFunction, ManagedBody>
{
    public string Name => "恢复";
    public StageResult<ManagedBody> Run(NativeFunction input, MethodContext context) =>
        new Missing<ManagedBody>(new(Name, context.Entry.Address, "原生 IR 到托管方法体", new("recovery.unavailable", "恢复层尚未接入")));
}
