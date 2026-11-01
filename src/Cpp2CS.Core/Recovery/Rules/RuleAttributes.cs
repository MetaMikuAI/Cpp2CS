namespace Cpp2CS.Recovery;

// 步骤与规则的统一声明。每个注册方法有全局唯一的 Id（族.名称，前缀等于所在族目录名）；顺序由 Order 与 After 完全决定。
// 可失败的下降规则返回 RecoveryResult，步骤返回 RecoveryFailure?；纯规则仍可返回 bool/空值，由注册器适配。

/// <summary>步骤所在的阶段。</summary>
internal enum StepPhase
{
    /// <summary>Prepare：顺序由 Prepare 计划表给出，不使用 Order 与 After。</summary>
    Prepare,
    /// <summary>Analyze：按 After 拓扑排序，同时可运行的按 Order 从小到大。</summary>
    Analyze,
}

/// <summary>步骤种类：分析步骤只读（调度器在步骤前后核对机器 IR 未变），改写步骤可以修改机器 IR。</summary>
internal enum StepKind
{
    Analysis,
    Rewrite,
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

/// <summary>
/// 步骤。Analyze 阶段的步骤为 <c>void M(scope)</c> 或 <c>RecoveryFailure? M(scope)</c>，按 After 拓扑排序，同时可运行的按 Order 从小到大；
/// 同一阶段内 Order 唯一（分析步骤与改写步骤在同一个拓扑排序里，不分种类查重）。After 写依赖步骤的 Id。
/// Prepare 阶段的步骤为 <c>void M(scope[, PreparedMethod])</c> 或 <c>PrepareOutcome M(scope[, PreparedMethod])</c>，顺序由计划表给出。
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class StepAttribute(string id, StepPhase phase, StepKind kind) : Attribute
{
    public string Id => id;
    public StepPhase Phase => phase;
    public StepKind Kind => kind;
    public int Order { get; init; }
    public string[] After { get; init; } = [];
    /// <summary>中文名，只作说明。</summary>
    public string Name { get; init; } = "";
    /// <summary>改写步骤声明的失效范围，只用于追踪。</summary>
    public AnalysisInvalidation Invalidates { get; init; } = AnalysisInvalidation.All;
}

/// <summary>下降规则、参数绑定与方法体证明的类别；各类别有自己的委托形状，Order 在类别内唯一。</summary>
internal enum RuleKind
{
    /// <summary>语句级下降规则 <c>bool M(Block, Stmt, List&lt;ManagedStatement&gt;)</c>，在通用翻译之前尝试；返回 true 表示已处理。</summary>
    Statement,
    /// <summary>定义的下降规则 <c>bool M(Define, List&lt;ManagedStatement&gt;)</c>，在运行时引用、内联与对象类指针之后、普通赋值之前。</summary>
    Define,
    /// <summary>存储的下降规则 <c>bool M(Store, List&lt;ManagedStatement&gt;)</c>，在解析写入位置之前。</summary>
    Store,
    /// <summary>写入位置已解析后的存储规则 <c>bool M(Store, ManagedValue, List&lt;ManagedStatement&gt;)</c>。</summary>
    StoreTarget,
    /// <summary>调用的下降规则 <c>bool M(Call, List&lt;ManagedStatement&gt;)</c>，在删去的运行时操作与通用分派之前。</summary>
    Call,
    /// <summary>托管调用的下降规则 <c>bool M(Call, List&lt;ManagedStatement&gt;)</c>，在解析调用目标之前。</summary>
    Invocation,
    /// <summary>实参已恢复后的调用写出规则 <c>bool M(Call, AbiSignature, Dictionary&lt;Storage, Expr&gt;, ManagedInvocation, List&lt;ManagedStatement&gt;)</c>。</summary>
    InvocationOutput,
    /// <summary>按 ABI 传递的实参 <c>ManagedValue? M(AbiValue, ArgumentSite)</c>；返回 null 表示不归它处理。</summary>
    Argument,
    /// <summary>调用结果的局部 <c>LocalValue? M(Call, AbiValue)</c>；返回 null 表示不归它处理。</summary>
    Result,
    /// <summary>入口参数的绑定 <c>bool M(AbiValue, int)</c>；返回 true 表示已绑定。</summary>
    ParameterBinding,
    /// <summary>方法体证明 <c>void M(ManagedBody)</c>：方法体建成之后逐个检查，失败时登记洞。</summary>
    BodyProof,
}

/// <summary>下降规则、参数绑定或方法体证明。同一类别内按 Order 从小到大尝试，Order 在类别内唯一。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class RuleAttribute(RuleKind kind, string id) : Attribute
{
    public RuleKind Kind => kind;
    public string Id => id;
    public int Order { get; init; }
}
