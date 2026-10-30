using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

// 注册按依赖排序分析、下降规则与证明。可失败的下降规则返回 RecoveryResult，
// 分析返回 RecoveryFailure?；纯规则仍可返回 bool/空值，由注册器适配。
/// <summary>分析步骤 <c>void M()</c>。按 After 拓扑排序，同时可运行的按 Order 从小到大。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal class AnalysisAttribute(string name, int order) : Attribute
{
    public string Name => name;
    public int Order => order;
    public string[] After { get; init; } = [];
}

[Flags]
internal enum AnalysisInvalidation
{
    None = 0,
    Definitions = 1,
    ControlFlow = 2,
    Uses = 4,
    All = 7
}

[AttributeUsage(AttributeTargets.Method)]
internal sealed class MachinePassAttribute(string name, int order) : AnalysisAttribute(name, order)
{
    public AnalysisInvalidation Invalidates { get; init; } = AnalysisInvalidation.All;
}

/// <summary>语句级下降规则 <c>bool M(Block, Stmt, List&lt;ManagedStatement&gt;)</c>，在通用翻译之前尝试；返回 true 表示已处理。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class StatementRuleAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>定义的下降规则 <c>bool M(Define, List&lt;ManagedStatement&gt;)</c>，在运行时引用、内联与对象类指针之后、普通赋值之前。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class DefineRuleAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>存储的下降规则 <c>bool M(Store, List&lt;ManagedStatement&gt;)</c>，在解析写入位置之前。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class StoreRuleAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>写入位置已解析后的存储规则 <c>bool M(Store, ManagedValue, List&lt;ManagedStatement&gt;)</c>。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class StoreTargetRuleAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>调用的下降规则 <c>bool M(Call, List&lt;ManagedStatement&gt;)</c>，在删去的运行时操作与通用分派之前。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class CallRuleAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>托管调用的下降规则 <c>bool M(Call, List&lt;ManagedStatement&gt;)</c>，在解析调用目标之前。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class InvocationRuleAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>实参已恢复后的调用写出规则 <c>bool M(Call, AbiSignature, Dictionary&lt;Storage, Expr&gt;, ManagedInvocation, List&lt;ManagedStatement&gt;)</c>。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class InvocationOutputRuleAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>按 ABI 传递的实参 <c>ManagedValue? M(AbiValue, ArgumentSite)</c>；返回 null 表示不归它处理。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class ArgumentRuleAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>调用结果的局部 <c>LocalValue? M(Call, AbiValue)</c>；返回 null 表示不归它处理。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class ResultRuleAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>入口参数的绑定 <c>bool M(AbiValue, int)</c>；返回 true 表示已绑定。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class ParameterBindingAttribute(int order) : Attribute
{
    public int Order => order;
}

/// <summary>方法体证明 <c>void M(ManagedBody)</c>：方法体建成之后逐个检查，失败时登记洞。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class BodyProofAttribute(int order) : Attribute
{
    public int Order => order;
}
