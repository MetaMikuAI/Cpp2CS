using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// 对照器的形态模型：每种形态在原生侧、解释器侧或世界里的建模，以类为单位声明名称与建模依据
/// （运行时代码、普查、ECMA-335、AAPCS64、ARM ARM 等）。审核时逐个核对依据；<c>shape-models</c> 检查保证每个模型都写了依据。
/// 模型的代码不引用恢复路径的规则（架构总览第 6 节）。
/// </summary>
[AttributeUsage(AttributeTargets.Class, AllowMultiple = true)]
internal sealed class ShapeModelAttribute(string name) : Attribute
{
    public string Name => name;
    public required string Basis { get; init; }
}

/// <summary>变异算子族 <c>IEnumerable&lt;(string, Action, Action)&gt; M(MutationSite)</c>：属于某个形态模型，按 Order 依次生成变异。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class MutationFamilyAttribute(string model, int order) : Attribute
{
    public string Model => model;
    public int Order => order;
}

/// <summary>变异算子看到的现场：被测方法的 CIL、Cecil 模型、世界索引、帧初始化指令与解释器。</summary>
internal sealed record MutationSite(MethodDefinition Method, CecilModel Cecil, WorldIndex Index, IReadOnlySet<Instruction> Initializations, CilInterpreter Interpreter);

internal static class ShapeModels
{
    public static readonly (string Name, string Basis, Type Type)[] All = typeof(ShapeModels).Assembly.GetTypes()
        .SelectMany(t => t.GetCustomAttributes<ShapeModelAttribute>().Select(a => (a.Name, a.Basis, t)))
        .OrderBy(m => m.Name, StringComparer.Ordinal).ToArray();

    public static readonly (MutationFamilyAttribute Family, Func<MutationSite, IEnumerable<(string, Action, Action)>> Run)[] MutationFamilies =
        typeof(ShapeModels).Assembly.GetTypes().SelectMany(t => t.GetMethods(BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.DeclaredOnly))
            .Select(m => (Method: m, Family: m.GetCustomAttribute<MutationFamilyAttribute>())).Where(p => p.Family is not null)
            .OrderBy(p => p.Family!.Order).ThenBy(p => p.Method.Name, StringComparer.Ordinal)
            .Select(p => (p.Family!, p.Method.CreateDelegate<Func<MutationSite, IEnumerable<(string, Action, Action)>>>())).ToArray();

    public static IEnumerable<(string Description, Action Apply, Action Revert)> Mutate(MutationSite site) =>
        MutationFamilies.SelectMany(f => f.Run(site));

    [Command("shape-models", "对照器形态模型清单：每个模型声明建模依据，每个变异族属于已注册的模型", Gate = Gate.Unit)]
    public static int Check()
    {
        var a = new Assertions();
        foreach (var (name, basis, type) in All)
        {
            Console.WriteLine($"  {name}（{type.Name}）：{basis}");
            a.True(!string.IsNullOrWhiteSpace(basis), $"形态模型 {name} 没有写建模依据");
        }
        var names = All.Select(m => m.Name).ToHashSet();
        foreach (var (family, _) in MutationFamilies)
            a.True(names.Contains(family.Model), $"变异族（次序 {family.Order}）所属的形态模型 {family.Model} 未注册");
        a.True(MutationFamilies.Length > 0, "没有注册的变异族");
        return a.Finish("shape-models");
    }
}
