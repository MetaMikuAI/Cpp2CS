using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using static Cpp2CS.Idioms.IdiomRewriter;

namespace Cpp2CS.Idioms;

internal sealed class IdiomState(IdiomRewriter owner, MachineFunction function)
{
    internal readonly IdiomRewriter owner = owner;
    internal readonly MachineFunction function = function;
    internal readonly ProgramFacts facts = owner.facts;
    internal readonly HashSet<Block> removed = [];
    internal readonly Dictionary<Variable, object> interfaceData = new();
    /// <summary>泛型虚方法解析结果（MethodInfo*）→ 方法。</summary>
    internal readonly Dictionary<Variable, MethodRef> genericVirtual = new();
    /// <summary>守卫之外的 InitMetadata 调用及其结果代表的符号；Calls 之后替换为定义（或删除）。</summary>
    internal readonly List<(Call Call, Symbol Value)> lazyValues = [];
    /// <summary>由槽位读取得到的符号 → 槽位地址（模板实例的输入位置）。</summary>
    internal readonly Dictionary<Symbol, ulong> symbolSlots = new();
    internal NameSupply? Names;
    internal Defs defs = new(function);
    internal readonly bool recording = owner.RecordFilter?.Invoke(function.Entry) ?? true;
    /// <summary>函数自身的托管所有者与其 MethodInfo* 入口位置（共享泛型代码由此取自身的 RGCTX）。</summary>
    internal MethodRef? self;
    internal Storage? selfMethodInfo;
    internal bool foldedRuntimeGuards;
    internal readonly List<(Block End, ulong Guard)> initializedGuards = [];
    public IdiomResult Result { get; } = new();
    private Cpp2CS.Machine.Algebra.PassList? passes;
    internal Cpp2CS.Machine.Algebra.PassList Passes => passes ??= new(function, Result.Passes);
    internal IEnumerable<Stmt> All => this.function.Blocks.Where(b => !this.removed.Contains(b)).SelectMany(b => b.Statements);

    /// <summary>块内的一个执行位置：第 Index 条语句之前、地址 Address 的指令之前（传播删去的定义按地址排入）。</summary>
    internal readonly record struct Point(int Index, ulong Address);
}
