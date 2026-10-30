using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>L2 模板。每个模板命中一次计一次（见 <see cref="IdiomResult.Hits"/>）。</summary>
public enum Template
{
    /// <summary>读取元数据槽位 → Symbol。</summary>
    MetadataSlot,
    /// <summary>读取 Il2CppClass.static_fields → Symbol(StaticFields)。</summary>
    StaticFields,
    /// <summary>读取 MethodInfo.klass → Symbol(Class)。</summary>
    MethodClass,
    /// <summary>读取 MethodInfo.rgctx_data / Il2CppClass.rgctx_data → Symbol(Rgctx)。</summary>
    RgctxData,
    /// <summary>读取 RGCTX 数组第 i 项 → 表中条目（Class/Type/Method/Constrained）。</summary>
    RgctxEntry,
    /// <summary>方法级 s_Il2CppMethodInitialized 守卫及其中的 InitMetadata 调用：整体删除。</summary>
    MetadataInitGuard,
    /// <summary>cctor_finished_or_no_cctor 守卫 + il2cpp_runtime_class_init → RunClassConstructor。</summary>
    ClassConstructorGuard,
    /// <summary>initialized_and_no_error 位守卫 + InitializedTypeInfo → InitClass。</summary>
    InitClassGuard,
    /// <summary>MethodInfo.rgctx_data 为空守卫 + InitMethodRgctx → InitMethodRgctx。</summary>
    MethodRgctxGuard,
    /// <summary>条件分支到只抛异常的块 → NullCheck / BoundsCheck / ThrowIf。</summary>
    NullCheck, BoundsCheck, ThrowIf,
    /// <summary>内联的接口偏移扫描 + 慢路径查找 → InterfaceInvokeData。</summary>
    InterfaceDispatch,
    /// <summary>typeHierarchyDepth 比较 + typeHierarchy[depth-1] 比较 → TypeCheck。</summary>
    InlineTypeCheck,
    VirtualCall, InterfaceCall, DelegateCall, MethodPointerCall,
    /// <summary>MethodInfo.slot 读取 → 元数据中的槽位常量。</summary>
    MethodSlot,
    /// <summary>vtable[slot].method + 泛型方法实例 → 运行时解析泛型虚方法；之后经其 virtualMethodPointer 调用。</summary>
    GenericVirtualCall,
    /// <summary>直接调用已识别的运行时 helper → 对应操作。</summary>
    HelperCall,
    /// <summary>写屏障与其前紧邻的同一引用写入配对。</summary>
    WriteBarrier,
    /// <summary>守卫之外的 InitMetadata(槽位)：结果即槽位的值 → Symbol。</summary>
    LazyMetadataInit,
    /// <summary>PLT 导入调用。</summary>
    ImportCall,
    /// <summary>同一个 wrapper 分配、写入与抛出的完整配对。</summary>
    ManagedThrow,
}

/// <summary>模板没有消化的运行时痕迹：Category 用于汇总，Detail 是样例说明。</summary>
public readonly record struct Residual(ulong Address, string Category, string Detail);

/// <summary>
/// 一个模板实例的机器级描述，供 tests/oracle/template_oracle.py 在 Unicorn 中执行原指令验证：
/// Head 为起始块地址；Exits 为出口块地址；Inputs 为输入的位置（槽位地址、起始时所在寄存器）与参数。
/// </summary>
public sealed record TemplateInstance(Template Template, ulong Function, ulong Head, IReadOnlyDictionary<string, ulong> Exits, IReadOnlyDictionary<string, object> Inputs);

public sealed class IdiomResult
{
    public List<TemplateInstance> Instances { get; } = [];
    public Dictionary<Template, int> Hits { get; } = new();
    public List<Residual> Residuals { get; } = [];
    public List<string> Errors { get; } = [];
    public List<PassStep> Passes { get; } = [];
    /// <summary>本函数守卫中初始化的槽位、读取的槽位、守卫字节地址。</summary>
    public HashSet<ulong> InitializedSlots { get; } = [];
    public HashSet<ulong> ReadSlots { get; } = [];
    public HashSet<ulong> Guards => [.. GuardSlots.Keys];
    /// <summary>守卫字节 → 它的区域初始化的槽位（升序）。</summary>
    public Dictionary<ulong, ulong[]> GuardSlots { get; } = new();
    /// <summary>已证明为元数据初始化守卫的条件分支位置，供原生同形核对使用。</summary>
    public HashSet<ulong> MetadataGuardBranches { get; } = [];
    /// <summary>改写之前，对各类 helper 的调用点数与间接调用数。</summary>
    public Dictionary<HelperKind, int> HelperCalls { get; } = new();
    public int IndirectCalls { get; set; }

    public void Hit(Template template) => Hits[template] = Hits.GetValueOrDefault(template) + 1;
}

/// <summary>
/// L2 惯用法归一：在寄存器 SSA 上把 IL2CPP 生成代码的固定形态替换为带语义的 <see cref="RuntimeOp"/>。
/// 每个模板都检查完整形态（守卫条件按代入常量后的分支方向判定，区域内只允许模板规定的语句），
/// 不符合就不改动，留作 <see cref="Residual"/>。改动控制流之后重新传播并校验 SSA。
/// </summary>
public sealed class IdiomRewriter(ProgramFacts facts)
{
    public IdiomRewriter(BaseFacts facts) : this(new ProgramFacts(facts, new())) { }
    internal readonly ProgramFacts facts = facts;
    internal readonly ImageSection[] guardSections = facts.Model.Image.Sections
        .Where(s => (s.Flags & 1) != 0 && !s.Executable && s.Name != ".got").ToArray();
    internal readonly ManagedAbi abi = new(facts.Layouts);
    internal readonly Cpp2CS.Machine.Lifting.FactsCallModel calls = new(facts, new Arm64Machine(facts.Code).Convention);
    private Cpp2CS.Facts.Derived.NativeCalleeFacts? nativeCallees;
    internal Cpp2CS.Facts.Derived.NativeCalleeFacts NativeCallees => nativeCallees ??= new(facts, RecoverUnusedInputs);
    internal bool UnusedInput(ulong entry, Storage register) => NativeCallees.UnusedInput(entry, register);
    internal bool UnusedResultBuffer(ulong entry) => NativeCallees.UnusedResultBuffer(entry);

    /// <summary>为哪些函数（按入口）记录模板实例；null 为全部。记录要逐个寄存器回溯取值，普查全程序时按函数抽样。</summary>
    public Func<ulong, bool>? RecordFilter { get; set; }
    /// <summary>只读普查中的宽泛委托偏移标签；恢复器使用默认的严格归一。</summary>
    public bool AuditLegacyDelegateCalls { get; init; }
    /// <summary>仅供全程序普查保留 allocate/store/throw 的原始配对证据。</summary>
    public bool AuditRawManagedThrows { get; init; }
    /// <summary>恢复托管调用时清理未用输入的残值；事实推断仍保留原始调用参数。</summary>
    public bool RecoverUnusedInputs { get; init; }

    public IdiomResult Run(MachineFunction function)
    {
        IdiomState context = new IdiomState(this, function);
        context.Run();
        return context.Result;
    }

    /// <summary>调用目标是运行时 helper（不含托管区域中没有注册表所有者的生成函数，它们按托管调用处理）。</summary>
    internal RuntimeHelper? HelperOf(Call call) =>
        call is { Kind: CallKind.Direct or CallKind.Tail, Target: Const target } && facts.Helpers.At(target.Value) is { } helper
            && facts.Code.RegionOf(target.Value) != CodeRegion.Managed ? helper : null;

    /// <summary>定义表：把 SSA 变量展开为定义它的表达式（深度有限），用于比较与形状匹配。</summary>
    internal sealed class Defs
    {
        private readonly Dictionary<Variable, Expr> values = new();

        public Defs(MachineFunction function)
        {
            foreach (var stmt in function.Blocks.SelectMany(b => b.Statements))
                if (stmt is Define define) values[define.Target] = define.Value;
            foreach (var (_, define) in function.Dead) values.TryAdd(define.Target, define.Value);
            // 对象与其不可变类指针同时汇合；每条边必须逐一对应同一对象，不能只比较静态类型。
            foreach (var block in function.Blocks)
                foreach (var klass in block.Statements.OfType<Phi>())
                {
                    var objects = klass.Sources.Select(v => values.GetValueOrDefault(v) is Load { Width: 64, Address: Use { Width: 64 } obj }
                        ? obj.Variable : null).ToArray();
                    if (objects.Length == 0 || objects.Any(v => v is null)) continue;
                    var receiver = block.Statements.OfType<Phi>().FirstOrDefault(p => p.Sources.SequenceEqual(objects!));
                    if (receiver is not null) values[klass.Target] = new Load(new Use(receiver.Target, 64), 64);
                }
        }

        /// <summary>变量的定义表达式（不展开）；不是 Define 定义的为 null。</summary>
        public Expr? Raw(Variable variable) => values.GetValueOrDefault(variable);

        public Expr Expand(Expr expr, int depth = 8) => depth == 0 ? expr : Fold.Simplify(ExprMap.Map(expr, e =>
            e is Use use && values.TryGetValue(use.Variable, out var value)
                ? Fold.Convert(ConvKind.Truncate, Expand(value, depth - 1), use.Width)
                : null));
    }
}
