using System.Text;
using Cpp2CS.Arm64;
using Cpp2CS.Images;
using Cpp2CS.Ir;

namespace Cpp2CS.Facts;

/// <summary>F5 的全程序异常事实。只增加检查；不改变 helper 分类、异常边或恢复判定。</summary>
public static class ExceptionFacts
{
    public const string WrapperName = "22Il2CppExceptionWrapper";
    public sealed record ThrowSite(ulong Entry, ulong Site, CodeRegion Region, bool CalledByManaged, bool ThrowHelperPath, ulong? TypeInfo, ulong? Destructor, string? Name);

    /// <summary>检查真正传给 __cxa_throw 的 x1，不能以“函数引用过 wrapper 名”替代实参证明。</summary>
    public static ThrowSite[] Throws(CodeMap map, CodeScan scan, RuntimeHelpers helpers)
    {
        var result = new List<ThrowSite>();
        var targets = map.Functions.Where(f => f.Import == "__cxa_throw").Select(f => f.Start).ToHashSet();
        if (map.Image.Exports.TryGetValue("__cxa_throw", out var implementation)) targets.Add(implementation);
        // Raise/Rethrow 也有只含一次调用的导出/包装；顺着唯一调用走到真正抛出点。
        // 多调用函数不任意选一条路，仍由全映像逐点普查报告其所有直接 __cxa_throw。
        var paths = new HashSet<ulong>();
        var roots = helpers.Helpers.Values.Where(h => h.Kind is HelperKind.Raise or HelperKind.Rethrow or HelperKind.Throw).Select(h => h.Address).ToList();
        if (map.Image.Exports.TryGetValue("il2cpp_raise_exception", out var raise)) roots.Add(raise);
        foreach (var root in roots)
        {
            var current = root;
            while (paths.Add(current) && map.EntryIndex(current) is var index and >= 0)
            {
                var calls = scan.Of(index).ToArray().Where(r => r.Kind is RefKind.Call or RefKind.TailCall).ToArray();
                if (calls.Length != 1) break;
                current = calls[0].Target;
            }
        }
        for (var i = 0; i < map.Functions.Count; i++)
        {
            var function = map.Functions[i];
            var sites = scan.Of(i).ToArray().Where(r => r.Kind is RefKind.Call or RefKind.TailCall && targets.Contains(r.Target)).Select(r => r.Site).ToHashSet();
            if (sites.Count == 0) continue;
            var leaders = new HashSet<ulong>(function.ExceptionRegions.Select(r => r.LandingPad));
            for (var pc = function.Start; pc < function.End; pc += 4)
                if (map.Word(pc) is { } w)
                {
                    if (A64.ConditionalTarget(w, pc) is { } target) leaders.Add(target);
                    if (A64.IsB(w)) leaders.Add(A64.Imm26Target(w, pc));
                }
            var registers = new ulong?[32];
            for (var pc = function.Start; pc < function.End; pc += 4)
            {
                if (leaders.Contains(pc)) Array.Clear(registers);
                if (sites.Contains(pc))
                {
                    var typeInfo = registers[1] ?? AcrossBlocks(map, function, pc);
                    result.Add(new(function.Start, pc, function.Region, helpers.At(function.Start) is not null,
                        paths.Contains(function.Start), typeInfo, registers[2], typeInfo is { } type ? TypeName(map.Image, type) : null));
                }
                if (map.Word(pc) is not { } w) { Array.Clear(registers); continue; }
                if (A64.IsAdrp(w)) registers[A64.Rd(w)] = A64.AdrpPage(w, pc);
                else if (A64.IsAdr(w)) registers[A64.Rd(w)] = A64.AdrTarget(w, pc);
                else if (A64.IsAddImmediate64(w)) registers[A64.Rd(w)] = registers[A64.Rn(w)] + A64.AddImmediate(w);
                else if ((w & 0xffc00000) == 0xf9400000) // LDR X，无写回
                {
                    var address = registers[A64.Rn(w)] + A64.AccessOffset(w);
                    registers[A64.Rd(w)] = address is { } at && map.Image.Section(".got")?.Contains(at) == true ? map.Image.RelocatedPointer(at) : null;
                }
                else if ((w & 0xffe0ffe0) == 0xaa0003e0) // MOV Xd, Xm（ORR Xd, XZR, Xm）
                    registers[A64.Rd(w)] = ((w >> 16) & 31) == 31 ? 0 : registers[(w >> 16) & 31];
                else if (A64.IsUnsignedOffsetAccess(w) && A64.IsStore(w) || w == A64.Nop) { }
                // 未列出的指令全部失效，不能借近邻引用跨越调用、分支、写回访存或未知写寄存器。
                else Array.Clear(registers);
                registers[31] = null;
            }
        }
        return result.ToArray();
    }

    // 全程序见证中有将 RTTI 提到循环外的 callee-saved 寄存器。只对直线证明失败处，
    // 沿全部原生前驱（含 LSDA 边）反查同一个常量；未知跳转/写入/入口值一律拒绝。
    private static ulong? AcrossBlocks(CodeMap map, CodeFunction function, ulong site)
    {
        var predecessors = new Dictionary<ulong, List<ulong>>();
        var decoded = new Dictionary<ulong, List<Stmt>>();
        void Edge(ulong from, ulong to)
        {
            if (!function.Contains(to)) return;
            if (!predecessors.TryGetValue(to, out var list)) predecessors[to] = list = [];
            list.Add(from);
        }
        for (var pc = function.Start; pc < function.End; pc += 4)
        {
            if (map.Word(pc) is not { } w || A64.IsBr(w)) return null;
            var statements = new List<Stmt>(); Arm64Lifter.Lift(pc, w, statements); decoded[pc] = statements;
            if (A64.IsB(w)) Edge(pc, A64.Imm26Target(w, pc));
            else if (!A64.IsRet(w) && !A64.IsTrap(w)) Edge(pc, pc + 4);
            if (A64.ConditionalTarget(w, pc) is { } branch) Edge(pc, branch);
            if (A64.IsBl(w) || A64.IsBlr(w))
                foreach (var region in function.ExceptionRegions.Where(r => r.Start <= pc && pc < r.End && r.LandingPad != 0)) Edge(pc, region.LandingPad);
        }
        var pending = new Stack<(ulong Pc, int Register, ulong Offset)>(); pending.Push((site, 1, 0));
        var seen = new HashSet<(ulong, int, ulong)>(); var constants = new HashSet<ulong>();
        while (pending.TryPop(out var state))
        {
            if (!seen.Add(state)) continue;
            if (seen.Count > 10000 || state.Pc == function.Start || !predecessors.TryGetValue(state.Pc, out var previous)) return null;
            foreach (var pc in previous)
            {
                var statements = decoded[pc];
                if (statements.Any(s => s is Opaque)) return null;
                if (statements.Any(s => s is Call) && state.Register is not (>= 19 and <= 28)) return null;
                var writes = statements.OfType<Assign>().Where(a => a.Target == Storage.Gpr(state.Register)).ToArray();
                if (writes.Length == 0) { pending.Push((pc, state.Register, state.Offset)); continue; }
                if (writes.Length != 1) return null;
                var value = Fold.Simplify(writes[0].Value); var offset = state.Offset;
                if (value is Binary { Op: BinOp.Add, Right: Const add } sum) { value = sum.Left; offset = unchecked(offset + add.Value); }
                if (value is Const constant) constants.Add(unchecked(constant.Value + offset));
                else if (value is Read { Width: 64, Storage.Bank: Bank.Gpr } read) pending.Push((pc, read.Storage.Index, offset));
                else return null;
            }
        }
        return constants.Count == 1 ? constants.Single() : null;
    }

    public static string? TypeName(ImageDocument image, ulong type)
    {
        if (image.Resolve(type).AvailableBytes < 16 || image.ReadPointer(type + 8) is not { } name) return null;
        var bytes = image.ReadUpTo(name, 256);
        var end = bytes.IndexOf((byte)0);
        return end < 0 ? null : Encoding.UTF8.GetString(bytes[..end]);
    }

    public static void Check(FactChecks checks, CodeMap map, CodeScan scan, RuntimeHelpers helpers)
    {
        var throws = Throws(map, scan, helpers);
        var relevant = throws.Where(s => s.Region == CodeRegion.Managed || s.CalledByManaged || s.ThrowHelperPath).ToArray();
        var errors = relevant.Where(s => s.Name != WrapperName || s.Destructor != 0)
            .Select(s => $"0x{s.Entry:x}@0x{s.Site:x} x1=0x{s.TypeInfo:x} destructor=0x{s.Destructor:x} RTTI={s.Name ?? "未解析"}").ToList();
        if (relevant.Length == 0) errors.Add("没有找到托管 __cxa_throw 见证");
        checks.Add("eh.E1.throw-wrapper", "Error", relevant.Length, errors,
            $"全映像 __cxa_throw {throws.Length} 处；托管直接抛出 {relevant.Count(s => s.Region == CodeRegion.Managed)} 处；" +
            $"抛出 helper 终端 {relevant.Count(s => s.Region != CodeRegion.Managed)} 处（含 Raise/Rethrow 唯一调用包装链）。逐点核验 x1 的 RTTI 名为 {WrapperName}，x2 析构器为空；不证明任意原生服务不会抛出外来异常。");
        var typed = new List<string>();
        long total = 0, cleanup = 0, catchAll = 0;
        foreach (var function in map.Functions.Where(f => f.Region == CodeRegion.Managed))
            foreach (var region in function.ExceptionRegions.Where(r => r.LandingPad != 0))
            {
                if (region.Actions.Length == 0) cleanup++;
                foreach (var action in region.Actions)
                {
                    if (action.Filter == 0) { cleanup++; continue; }
                    total++;
                    if (action.Filter < 0) { typed.Add($"0x{function.Start:x}: filter {action.Filter}"); continue; }
                    var slot = action.TypeInfo;
                    // 本映像使用 indirect 类型表：必须由加载器重定位证明槽位的内容。
                    var type = slot is > 0 ? map.Image.RelocatedPointer(slot.Value) : null;
                    if (slot == 0)
                    {
                        catchAll++;
                        if (action.Filter != 2) typed.Add($"0x{function.Start:x}: catch-all 占用序号 {action.Filter}，预期 wrapper 为 1、catch-all 为 2");
                        continue;
                    }
                    if (action.Filter != 1 || type is null || TypeName(map.Image, type.Value) != WrapperName)
                        typed.Add($"0x{function.Start:x}@0x{region.LandingPad:x} filter={action.Filter} slot=0x{slot:x} type=0x{type:x}");
                }
            }
        if (total == 0) typed.Add("没有找到托管 LSDA 类型见证");
        checks.Add("eh.E2.selector-wrapper", "Error", total, typed,
            $"全托管 LSDA 正类型 action（按 call-site 计）；非空类型槽的序号必须为 1，重定位后的 RTTI 名必须为 {WrapperName}。" +
            $"cleanup {cleanup} 条；catch-all {catchAll} 条另计，不冒充 wrapper catch。");
    }
}
