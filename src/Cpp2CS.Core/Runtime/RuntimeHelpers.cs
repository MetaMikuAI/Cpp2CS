using System.Text;
using Cpp2CS.Flow;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Ssa;

namespace Cpp2CS.Runtime;

public enum HelperKind
{
    ObjectNew, NewArray, NewArrayFull, Box, Unbox, ClassInit, Raise, WriteBarrier, IsInst, IsAssignableFrom,
    /// <summary>不返回：构造并抛出指定异常。</summary>
    Throw,
    /// <summary>返回指定异常对象（随后由 Raise 抛出）。</summary>
    GetException,
    /// <summary>按编码令牌初始化元数据槽位（参数为槽位地址），返回槽位中的运行时指针。</summary>
    InitMetadata,
    /// <summary>接口方法查找的慢路径：(对象, 接口类, 槽位) → VirtualInvokeData*。</summary>
    InterfaceLookup,
    /// <summary>以 C++ 异常 Il2CppExceptionWrapper 重新抛出 x0 中的托管异常对象（不更新堆栈）。</summary>
    Rethrow,
    /// <summary>__clang_call_terminate：开始捕获后调用 std::terminate。</summary>
    Terminate,
    /// <summary>泛型虚方法解析：(vtable 槽中的方法, 泛型实例方法) → 实际 MethodInfo*。</summary>
    GenericVirtualMethod,
    /// <summary>_Unwind_Resume：清理落地块结束后继续展开。</summary>
    UnwindResume,
    /// <summary>x0 为空则抛 NullReferenceException，否则返回 x0。</summary>
    NullCheck,
    /// <summary>返回第一个参数本身的小型运行时初始化函数（启发式）。</summary>
    EnsureInit,
    CxaBeginCatch, CxaEndCatch, CxaAllocateException, CxaThrow, Memcpy, Memset,
    /// <summary>C 数学库函数（Detail 为函数名），对应 System.Math/MathF 或浮点取余。</summary>
    LibM,
    /// <summary>__stack_chk_fail：栈保护检查失败，不返回；属于函数尾的编译器检查，不对应托管代码。</summary>
    StackCheckFail,
}

/// <summary>识别出的运行时辅助函数。Evidence 说明依据（导出链、字符串、结构）。</summary>
/// <summary>Detail：Throw/GetException 的异常类型全名，LibM 的函数名。</summary>
public sealed record Helper(HelperKind Kind, string Evidence, string? Detail = null)
{
    public override string ToString() => Detail is null ? Kind.ToString() : $"{Kind}({Detail})";
}

/// <summary>
/// 识别 IL2CPP 生成代码调用的运行时辅助函数（剥离符号后的 il2cpp-codegen 内联桩）。
/// 依据：
/// 1. 导入名：PLT 桩的符号名（含静态链接并导出的 libc++abi）；
/// 2. 导出链：辅助桩与 il2cpp_* 导出函数经无条件跳转/纯包装调用到达同一内部函数；
/// 3. 导出函数体中的调用：il2cpp_object_get_virtual_method 在接口偏移扫描失败后以 (obj, method-&gt;klass, method-&gt;slot) 调用的慢路径；
/// 4. 异常名：调用链中以 ("System", "XxxException") 两个 C 字符串为参数调用异常构造；
/// 5. 结构：元数据令牌解码（位 0 标记、位 29–31 种类、位 1–28 索引）；抛出 typeinfo 名为 Il2CppExceptionWrapper 的 C++ 异常；
///    判空后调用 IsAssignableFrom 的实现（IsInst，启发式）；返回值恒为第一个参数的小函数（EnsureInit，启发式）。
/// </summary>
public sealed class RuntimeHelpers
{
    private const int ChainJumps = 4;
    private const int ThinInstructions = 6;
    /// <summary>Itanium ABI 下 Il2CppExceptionWrapper 的 typeinfo 名。</summary>
    private const string WrapperTypeName = "22Il2CppExceptionWrapper";

    private static readonly (string Export, HelperKind Kind)[] ExportKinds =
    [
        ("il2cpp_object_new", HelperKind.ObjectNew),
        ("il2cpp_array_new_specific", HelperKind.NewArray),
        ("il2cpp_array_new_full", HelperKind.NewArrayFull),
        ("il2cpp_value_box", HelperKind.Box),
        ("il2cpp_object_unbox", HelperKind.Unbox),
        ("il2cpp_runtime_class_init", HelperKind.ClassInit),
        ("il2cpp_raise_exception", HelperKind.Raise),
        ("il2cpp_gc_wbarrier_set_field", HelperKind.WriteBarrier),
        ("il2cpp_class_is_assignable_from", HelperKind.IsAssignableFrom),
    ];

    private static readonly Dictionary<string, HelperKind> ImportKinds = new()
    {
        ["__cxa_begin_catch"] = HelperKind.CxaBeginCatch,
        ["__cxa_end_catch"] = HelperKind.CxaEndCatch,
        ["__cxa_allocate_exception"] = HelperKind.CxaAllocateException,
        ["__cxa_throw"] = HelperKind.CxaThrow,
        ["memcpy"] = HelperKind.Memcpy,
        ["memmove"] = HelperKind.Memcpy,
        ["memset"] = HelperKind.Memset,
        ["__stack_chk_fail"] = HelperKind.StackCheckFail,
    };

    /// <summary>托管代码会调用到的 libm 函数（Math/MathF 的内部调用与 float/double 取余）。</summary>
    private static readonly HashSet<string> LibMFunctions =
    [
        "sin", "cos", "tan", "asin", "acos", "atan", "atan2", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh",
        "exp", "log", "log10", "log2", "pow", "sqrt", "cbrt", "fmod", "modf", "floor", "ceil", "round", "trunc", "fabs", "sincos",
        "hypot", "exp2", "expm1", "log1p", "remainder", "nearbyint", "rint", "fma", "ilogb", "scalbn", "copysign",
    ];

    private readonly IMachine machine;
    private readonly CfgBuilder builder;
    private readonly NoReturnOracle noReturn;
    private readonly Dictionary<ulong, Helper?> cache = new();
    private readonly Dictionary<ulong, (HelperKind Kind, string Export)> exportTargets = new();
    private readonly HashSet<ulong> ambiguous = [];
    private readonly HashSet<ulong> assignableFrom = [];
    private readonly Dictionary<ulong, Helper> fromExportBodies = new();

    public RuntimeHelpers(CfgBuilder builder)
    {
        this.builder = builder;
        machine = builder.Machine;
        noReturn = builder.NoReturn;
        var exports = machine.Image.Exports;
        foreach (var (name, kind) in ExportKinds)
        {
            if (!exports.TryGetValue(name, out var address)) continue;
            foreach (var (target, _) in Chain(address))
            {
                if (exportTargets.TryGetValue(target, out var existing) && existing.Kind != kind) ambiguous.Add(target);
                else exportTargets[target] = (kind, name);
            }
        }
        if (exports.TryGetValue("il2cpp_class_is_assignable_from", out var assignable))
            foreach (var (target, _) in Chain(assignable)) assignableFrom.Add(target);
        if (exports.TryGetValue("il2cpp_object_get_virtual_method", out var virtualMethod))
        {
            var (slow, generic) = ScanVirtualMethodExport(Body(virtualMethod));
            if (slow is { } s)
                fromExportBodies[s] = new Helper(HelperKind.InterfaceLookup, $"il2cpp_object_get_virtual_method 在接口偏移扫描失败后以 (obj, method->klass, method->slot) 调用 0x{s:x}");
            if (generic is { } g)
                fromExportBodies[g] = new Helper(HelperKind.GenericVirtualMethod, $"il2cpp_object_get_virtual_method 对泛型实例方法以 (vtable 方法, method) 尾调用 0x{g:x}");
        }
    }

    public Helper? Identify(ulong target)
    {
        if (cache.TryGetValue(target, out var cached)) return cached;
        var helper = ByImport(target) ?? ByExport(target) ?? ByExportBody(target)
            ?? ByTokenDecode(target) ?? ByLibunwindName(target) ?? ByException(target) ?? ByWrapperThrow(target) ?? ByTerminate(target) ?? ByStructure(target) ?? ByPassThrough(target);
        cache[target] = helper;
        return helper;
    }

    /// <summary>
    /// 函数的“身份”：从 start 起沿薄代码（少量非控制指令后无条件转移）经过的跳转目标；
    /// 若最后是一个直接调用，且之后只有出栈与返回（纯包装）或被调用者不返回，再加上该调用目标。
    /// 遇到条件分支、寄存器跳转、普通函数体即停止，所以两个函数身份相交说明它们是同一内部函数的包装。
    /// </summary>
    public List<(ulong Target, bool IsCall)> Chain(ulong start)
    {
        var chain = new List<(ulong, bool)>();
        var address = start;
        var statements = new List<Stmt>();
        for (int jumps = 0, thin = 0; jumps <= ChainJumps && thin <= ThinInstructions;)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0 || statements.Count == 0) break;
            switch (statements[^1])
            {
                case Jump jump:
                    chain.Add((jump.Target, false));
                    address = jump.Target;
                    jumps++;
                    thin = 0;
                    continue;
                case Call { Kind: CallKind.Tail, Target: Const tail }:
                    chain.Add((tail.Value, false));
                    address = tail.Value;
                    jumps++;
                    thin = 0;
                    continue;
                case Call { Kind: CallKind.Direct, Target: Const callee }:
                    if (noReturn.IsNoReturn(callee.Value) || WrapperEpilogue(address + (ulong)size)) chain.Add((callee.Value, true));
                    return chain;
                case Branch or Return or IndirectJump or Trap or Opaque or Call:
                    return chain;
            }
            address += (ulong)size;
            thin++;
        }
        return chain;
    }

    /// <summary>沿身份链（含纯包装调用）走到最终的函数体。</summary>
    public ulong Body(ulong target)
    {
        var address = target;
        for (var i = 0; i < ChainJumps; i++)
        {
            var chain = Chain(address);
            if (chain.Count == 0) break;
            address = chain[^1].Target;
        }
        return address;
    }

    /// <summary>调用之后至多 3 条只写 SP/LR/被调用者保存寄存器的指令（或内存屏障），然后返回。</summary>
    private bool WrapperEpilogue(ulong address)
    {
        var statements = new List<Stmt>();
        var convention = machine.Convention;
        for (var i = 0; i < 4; i++)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0) return false;
            if (statements[^1] is Return) return true;
            // 返回值寄存器不能被改写
            if (statements.Any(s => s is Nop ? false : s is not Assign assign || convention.IntegerResults.Contains(assign.Target) || convention.FloatResults.Contains(assign.Target))) return false;
            address += (ulong)size;
        }
        return false;
    }

    private Helper? ByImport(ulong target)
    {
        if (noReturn.ImportName(target) is not { } name) return null;
        var bare = StripVersion(name);
        if (ImportKinds.TryGetValue(bare, out var kind)) return new Helper(kind, $"PLT 桩符号 {name}");
        // 单精度版本带 f 后缀（sinf、atan2f、sincosf）
        if (LibMFunctions.Contains(bare) || bare.EndsWith('f') && LibMFunctions.Contains(bare[..^1])) return new Helper(HelperKind.LibM, $"PLT 桩符号 {name}", bare);
        return null;
    }

    private static string StripVersion(string name) => name.IndexOf('@') is var at and > 0 ? name[..at] : name;

    private Helper? ByExport(ulong target)
    {
        (HelperKind Kind, string Export)? found = null;
        ulong via = 0;
        foreach (var (hop, _) in Chain(target))
        {
            if (ambiguous.Contains(hop) || !exportTargets.TryGetValue(hop, out var match)) continue;
            if (found is { } previous && previous.Kind != match.Kind) return null;
            if (found is null) via = hop;
            found = match;
        }
        return found is { } f ? new Helper(f.Kind, $"与导出 {f.Export} 经同一内部函数 0x{via:x}") : null;
    }

    private Helper? ByExportBody(ulong target)
    {
        if (fromExportBodies.TryGetValue(target, out var direct)) return direct;
        foreach (var (hop, _) in Chain(target))
            if (fromExportBodies.TryGetValue(hop, out var known)) return known with { Evidence = $"经 0x{hop:x}：{known.Evidence}" };
        return null;
    }

    /// <summary>
    /// 在 Object::GetVirtualMethod（导出体）的顺序指令中找：
    /// 唯一一个以 (x0 入口值, [x1+a], [x1+b]:16) 为参数的直接调用（对象、method-&gt;klass、method-&gt;slot：接口慢路径）；
    /// 唯一一个 x1 仍为入口 x1 的尾调用（泛型虚方法解析）。
    /// </summary>
    private (ulong? InterfaceSlowPath, ulong? GenericVirtual) ScanVirtualMethodExport(ulong body)
    {
        var convention = machine.Convention;
        var x0 = convention.IntegerArguments[0];
        var x1 = convention.IntegerArguments[1];
        var x2 = convention.IntegerArguments[2];
        var state = new SymbolicState(convention);
        var statements = new List<Stmt>();
        var address = body;
        var range = builder.Functions.At(body);
        ulong? slow = null, generic = null;
        bool slowAmbiguous = false, genericAmbiguous = false;
        for (var i = 0; i < 48; i++)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0) break;
            var last = statements[^1];
            foreach (var stmt in statements.Take(statements.Count - 1)) state.Step(stmt);
            if (last is Call { Kind: CallKind.Direct, Target: Const callee }
                && state.Eval(new Read(x0, 64)) == new Read(x0, 64)
                && state.Eval(new Read(x1, 64)) is Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Read r1, Right: Const } } && r1.Storage == x1
                && state.Eval(new Read(x2, 64)) is Ir.Convert { Kind: ConvKind.ZeroExtend, Operand: Load { Width: 16, Address: Binary { Op: BinOp.Add, Left: Read r2, Right: Const } } } && r2.Storage == x1)
            {
                slowAmbiguous |= slow is not null && slow != callee.Value;
                slow = callee.Value;
            }
            // 单条指令提升时尾调用表现为跳转：目标在函数范围外
            var tail = last switch
            {
                Call { Kind: CallKind.Tail, Target: Const t } => t.Value,
                Jump jump when range is not null && !range.Contains(jump.Target) => jump.Target,
                _ => (ulong?)null,
            };
            if (tail is { } tailTarget && state.Eval(new Read(x1, 64)) == new Read(x1, 64))
            {
                genericAmbiguous |= generic is not null && generic != tailTarget;
                generic = tailTarget;
            }
            if (last is IndirectJump or Trap or Opaque) break;
            state.Step(last);
            address += (ulong)size;
        }
        return (slowAmbiguous ? null : slow, genericAmbiguous ? null : generic);
    }

    /// <summary>
    /// libunwind 的 _LIBUNWIND_ABORT：fprintf(stderr, "libunwind: %s - %s\n", __func__, msg)。
    /// 函数体（≤64 条顺序指令）内这样调用时，x2 即该函数名。
    /// </summary>
    private Helper? ByLibunwindName(ulong target)
    {
        var convention = machine.Convention;
        var state = new SymbolicState(convention);
        var statements = new List<Stmt>();
        var address = target;
        for (var i = 0; i < 64; i++)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0) return null;
            foreach (var stmt in statements.Take(statements.Count - 1)) state.Step(stmt);
            var last = statements[^1];
            if (last is Call && CString(state.Eval(new Read(convention.IntegerArguments[1], 64))) == "libunwind: %s - %s\n"
                && CString(state.Eval(new Read(convention.IntegerArguments[2], 64))) is { } function)
                return function == "_Unwind_Resume" ? new Helper(HelperKind.UnwindResume, "函数体内 libunwind 中止信息的 __func__ 为 _Unwind_Resume") : null;
            if (last is Return or IndirectJump or Trap or Opaque) return null;
            state.Step(last);
            address += (ulong)size;
        }
        return null;
    }

    /// <summary>函数体前 24 条顺序指令内对同一寄存器做位 29–31 与位 1–28 的提取（元数据令牌 kind/index 解码）。</summary>
    private Helper? ByTokenDecode(ulong target)
    {
        var body = Body(target);
        var statements = new List<Stmt>();
        var address = body;
        Storage? kind = null, index = null;
        for (var i = 0; i < 24; i++)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0) return null;
            foreach (var e in statements.OfType<Assign>().SelectMany(a => ExprMap.Walk(a.Value)))
            {
                if (e is Extract { Low: 29, Width: 3, Operand: Read k }) kind = k.Storage;
                if (e is Extract { Low: 1, Width: 28, Operand: Read x }) index = x.Storage;
            }
            if (kind is not null && kind == index)
                return new Helper(HelperKind.InitMetadata, $"函数体 0x{body:x} 按元数据令牌编码解出种类（位 29–31）与索引（位 1–28）");
            if (statements[^1] is Return or IndirectJump or Trap) return null;
            address += (ulong)size;
        }
        return null;
    }

    private Helper? ByException(ulong target)
    {
        if (ExceptionName(target, 0, []) is not { } name) return null;
        return noReturn.IsNoReturn(target)
            ? new Helper(HelperKind.Throw, "调用链以命名空间与异常名字符串构造异常且不返回", name)
            : new Helper(HelperKind.GetException, "调用链以命名空间与异常名字符串构造异常并返回", name);
    }

    /// <summary>
    /// 在 address 起的代码（沿顺序执行与无条件跳转，进入直接调用，最多 3 层、每层 48 条指令）中，
    /// 找第一个以 x1=命名空间、x2=“…Exception” C 字符串为参数的调用或尾调用。
    /// </summary>
    private string? ExceptionName(ulong address, int depth, HashSet<ulong> visited)
    {
        if (depth > 3 || !visited.Add(address)) return null;
        var convention = machine.Convention;
        var state = new SymbolicState(convention);
        var statements = new List<Stmt>();
        for (var i = 0; i < 48; i++)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0) return null;
            foreach (var stmt in statements.Take(statements.Count - 1)) state.Step(stmt);
            var last = statements[^1];
            if (last is Call or Jump)
            {
                var ns = CString(state.Eval(new Read(convention.IntegerArguments[1], 64)));
                var name = CString(state.Eval(new Read(convention.IntegerArguments[2], 64)));
                if (ns is not null && name is not null && name.EndsWith("Exception", StringComparison.Ordinal) && IsIdentifier(ns) && IsIdentifier(name)) return $"{ns}.{name}";
            }
            switch (last)
            {
                case Jump jump:
                    return ExceptionName(jump.Target, depth, visited);
                case Call { Kind: CallKind.Tail, Target: Const tail }:
                    return ExceptionName(tail.Value, depth, visited);
                case Call { Kind: CallKind.Direct, Target: Const callee }:
                    if (ExceptionName(callee.Value, depth + 1, visited) is { } viaCall) return viaCall;
                    // 不返回的调用之后是别的函数
                    if (noReturn.IsNoReturn(callee.Value)) return null;
                    state.Step(last);
                    break;
                case Return or IndirectJump or Trap or Opaque:
                    return null;
                default:
                    state.Step(last);
                    break;
            }
            address += (ulong)size;
        }
        return null;
    }

    private Helper? ByWrapperThrow(ulong target) =>
        noReturn.IsNoReturn(target) && ThrowsWrapperOfX0(target, 0)
            ? new Helper(HelperKind.Rethrow, $"把入口 x0 存入 __cxa_allocate_exception 的对象后以 typeinfo “{WrapperTypeName}” 调用 __cxa_throw")
            : null;

    /// <summary>顺序代码（≤16 条，可进入 x0 原样传入的直接调用，最多 2 层）把入口 x0 写入内存后抛出 Il2CppExceptionWrapper。</summary>
    private bool ThrowsWrapperOfX0(ulong address, int depth)
    {
        if (depth > 2) return false;
        var convention = machine.Convention;
        var x0 = new Read(convention.IntegerArguments[0], 64);
        var state = new SymbolicState(convention);
        var statements = new List<Stmt>();
        var stored = false;
        for (var i = 0; i < 16; i++)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0) return false;
            foreach (var stmt in statements.Take(statements.Count - 1))
            {
                if (stmt is Store store && state.Eval(store.Value) == x0) stored = true;
                state.Step(stmt);
            }
            switch (statements[^1])
            {
                case Call { Kind: CallKind.Direct or CallKind.Tail, Target: Const callee } call:
                    if (noReturn.ImportName(callee.Value) is { } name && StripVersion(name) == "__cxa_throw")
                        return stored && state.Eval(new Read(convention.IntegerArguments[1], 64)) is Const typeinfo && TypeInfoName(typeinfo.Value) == WrapperTypeName;
                    if (noReturn.ImportName(callee.Value) is null && state.Eval(x0) == x0 && ThrowsWrapperOfX0(callee.Value, depth + 1)) return true;
                    if (call.Kind == CallKind.Tail || noReturn.IsNoReturn(callee.Value)) return false;
                    state.Step(call);
                    break;
                case Store store:
                    if (state.Eval(store.Value) == x0) stored = true;
                    break;
                case Branch or Jump or Return or IndirectJump or Trap or Opaque or Call:
                    return false;
                case var other:
                    state.Step(other);
                    break;
            }
            address += (ulong)size;
        }
        return false;
    }

    /// <summary>Itanium typeinfo：{vtable, const char* name, ...}。</summary>
    private string? TypeInfoName(ulong typeinfo) =>
        machine.Image.Resolve(typeinfo + 8).Kind == AddressKind.FileBacked && machine.Image.ReadPointer(typeinfo + 8) is { } name ? CString(new Const(name, 64)) : null;

    /// <summary>前 4 条指令内先调用 __cxa_begin_catch，再调用名为 terminate 的不返回导入。</summary>
    private Helper? ByTerminate(ulong target)
    {
        var statements = new List<Stmt>();
        var address = target;
        var caught = false;
        for (var i = 0; i < 4; i++)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0) return null;
            switch (statements[^1])
            {
                case Call { Kind: CallKind.Direct or CallKind.Tail, Target: Const callee }:
                    var name = noReturn.ImportName(callee.Value) is { } n ? StripVersion(n) : null;
                    if (!caught && name == "__cxa_begin_catch") caught = true;
                    else return caught && name is "_ZSt9terminatev" or "terminate" ? new Helper(HelperKind.Terminate, "__cxa_begin_catch 后调用 std::terminate") : null;
                    break;
                case Branch or Jump or Return or IndirectJump or Trap or Opaque:
                    return null;
            }
            address += (ulong)size;
        }
        return null;
    }

    private Helper? ByStructure(ulong target)
    {
        if (assignableFrom.Count == 0) return null;
        var body = Body(target);
        // 前 12 条指令内：对 x0 判零分支，然后（沿顺序执行）第一个直接调用是 IsAssignableFrom 的实现
        var statements = new List<Stmt>();
        var address = body;
        var nullCheck = false;
        for (var i = 0; i < 12; i++)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0) return null;
            switch (statements[^1])
            {
                case Branch { Condition: Compare { Cond: Cond.Eq, Left: Read { Storage: var s }, Right: Const { Value: 0 } } } when s == machine.Convention.IntegerArguments[0]:
                    nullCheck = true;
                    break;
                case Branch:
                    return null;
                case Call { Kind: CallKind.Direct, Target: Const callee }:
                    return nullCheck && assignableFrom.Contains(callee.Value)
                        ? new Helper(HelperKind.IsInst, $"判空后调用 il2cpp_class_is_assignable_from 的实现 0x{callee.Value:x}（结构启发式）")
                        : null;
                case Jump or Return or IndirectJump or Trap or Opaque or Call:
                    return null;
            }
            address += (ulong)size;
        }
        return null;
    }

    /// <summary>
    /// 小函数（≤ 16 条指令、无寄存器跳转）所有返回路径上 x0 都等于入口 x0：调用只为初始化副作用（启发式）。
    /// 用寄存器 SSA 判定，调用按保守约定处理。
    /// </summary>
    private Helper? ByPassThrough(ulong target)
    {
        if (builder.Functions.At(target) is not { } range || range.Start != target) return null;
        var function = builder.Build(target, range);
        var instructions = function.Blocks.Sum(b => b.Statements.Select(s => s.Address).Distinct().Count());
        if (instructions > 16 || function.Blocks.Any(b => b.Statements.Any(s => s is IndirectJump or Opaque or Trap))) return null;
        var convention = machine.Convention;
        var x0 = new Read(convention.IntegerResults[0], 64);
        if (Lowering.Registers(function, convention, new ConservativeCallModel(convention), x0).Count > 0) return null;
        var returns = function.Blocks.SelectMany(b => b.Statements).OfType<Return>().ToList();
        if (returns.Count == 0 || !returns.All(r => r.Value is Use { Variable: { Version: 0 } v } && v.Storage == x0.Storage)) return null;
        var callees = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Select(c => c.Target is Const t ? Identify(t.Value) : null).ToList();
        if (callees.Count == 0) return null;
        if (callees.All(h => h is { Kind: HelperKind.Throw, Detail: "System.NullReferenceException" }))
            return new Helper(HelperKind.NullCheck, "所有返回路径返回入口 x0，唯一的调用是抛 NullReferenceException");
        if (callees.All(h => h is { Kind: HelperKind.ClassInit }))
            return new Helper(HelperKind.ClassInit, "所有返回路径返回入口 x0，唯一的调用是 ClassInit（条件类初始化）");
        return new Helper(HelperKind.EnsureInit, "所有返回路径返回入口 x0，其余只有调用（启发式：运行时初始化）");
    }

    private static bool IsIdentifier(string s) => s.Length > 0 && s.All(c => char.IsAsciiLetterOrDigit(c) || c is '_' or '.');

    private string? CString(Expr value)
    {
        if (value is not Const { Value: var address }) return null;
        var mapping = machine.Image.Resolve(address);
        if (mapping.Kind != AddressKind.FileBacked || mapping.Range!.Executable) return null;
        var bytes = machine.Image.ReadUpTo(address, 128);
        var end = bytes.IndexOf((byte)0);
        if (end <= 0) return null;
        return Encoding.ASCII.GetString(bytes[..end]);
    }
}
