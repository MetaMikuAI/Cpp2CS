using System.Security.Cryptography;
using System.Text;
using Cpp2CS.Flow;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Lifting;
using Cpp2CS.Model;
using Cpp2CS.Ssa;

namespace Cpp2CS.Facts;

public sealed partial class UnregisteredMethods
{
    internal static string ShapeDescription(ProgramFacts facts, ulong entry) => new Builder(facts, null).Describe(entry);

    private sealed partial class Builder
    {
        private sealed record ShapeKey(string Hash, HashSet<ulong> GuardCandidates, Dictionary<ulong, ulong> AddressPairs, HashSet<ulong> GuardBranches);

        public string Describe(ulong entry)
        {
            var text = "";
            var key = Fingerprint(facts.Code.At(entry)!, value => text = value);
            ProveAddresses(entry, key, message => text += ";proof:" + message);
            return text;
        }

        private ShapeKey Fingerprint(CodeFunction function, Action<string>? describe = null)
        {
            var refs = facts.Scan.Of(facts.Code.EntryIndex(function.Start)).ToArray();
            var adrpSites = new HashSet<ulong>();
            var pairs = new Dictionary<ulong, ulong>();
            var guardCandidates = new HashSet<ulong>();
            var branches = new HashSet<ulong>();
            var aliases = new Dictionary<ulong, int>();

            var descriptors = new Dictionary<ulong, string>();
            foreach (var r in refs.Where(r => r.Kind is RefKind.Address or RefKind.Load or RefKind.Store or RefKind.Adr))
            {
                var pointer = facts.Model.Image.SectionAt(r.Target)?.Name == ".got" && r.Kind == RefKind.Load && r.Size == 8
                    ? facts.Model.Image.RelocatedPointer(r.Target) : null;
                var address = pointer ?? r.Target;
                string descriptor;
                if (facts.Usages.At(address) is { } slot)
                {
                    // 保留实体定义与槽位别名关系，只抽象实例实参；不把所有元数据混成一种占位符。
                    var value = slot.Usage.Value switch
                    {
                        MethodRef m => "M" + m.Method.Index,
                        DefinitionRef d => "T" + d.Definition.Index,
                        FieldRef f => "F" + f.Field.Index,
                        _ => slot.Usage.Value.ToString(),
                    };
                    descriptor = $"slot:{slot.Usage.Kind}:{value}";
                }
                else if (pointer is null && r.Size == 1 && facts.Model.Image.SectionAt(address) is { } section && (section.Flags & 1) != 0)
                {
                    // 这里只建立候选索引；匹配后必须由 L2 GuardSlots 验证每个被擦除的字节确实为初始化守卫。
                    guardCandidates.Add(address);
                    descriptor = "guard-candidate";
                }
                else
                {
                    descriptor = function.Contains(address) ? $"local:{address - function.Start:x}" : $"exact:{address:x}";
                }
                if (!aliases.TryGetValue(address, out var alias)) aliases[address] = alias = aliases.Count;
                descriptors[r.Site] = $"{r.Kind}:{r.Size}:{descriptor}:alias{alias}";
                if (r.Kind == RefKind.Adr) continue;
                pairs[r.Site] = 0; // 找不到原始 ADRP 的配对必须在 SSA 证明阶段拒绝。
                var w = facts.Code.Word(r.Site)!.Value;
                // CodeScan 已经检查了写寄存器和窗口失效；这里定位其原始 ADRP，未配对的 ADRP 保留绝对页。
                for (var pc = r.Site - 4; pc >= function.Start && r.Site - pc <= 256; pc -= 4)
                    if (facts.Code.Word(pc) is { } previous && A64.IsAdrp(previous) && A64.Rd(previous) == A64.Rn(w)
                        && A64.AdrpPage(previous, pc) + (r.Kind == RefKind.Address ? A64.AddImmediate(w) : A64.AccessOffset(w)) == r.Target)
                    { adrpSites.Add(pc); pairs[r.Site] = pc; break; }
            }
            var text = new StringBuilder();
            for (var pc = function.Start; pc < function.End; pc += 4)
            {
                var word = facts.Code.Word(pc) ?? throw new InvalidDataException($"缺少指令 0x{pc:x}");
                // CBNZ Wn / TBNZ Wn,#0 仅在 L2 已证明的 0/1 元数据守卫上等价；候选索引之后逐分支复核。
                if (((word & 0xff000000) == 0x35000000 || (word & 0xfff80000) == 0x37000000)
                    && refs.Any(r => r.Kind == RefKind.Load && r.Size == 1 && guardCandidates.Contains(r.Target)
                        && r.Site < pc && pc - r.Site <= 32 && (facts.Code.Word(r.Site)!.Value & 31) == (word & 31)))
                {
                    branches.Add(pc);
                    var target = A64.IsCbz(word) ? A64.Imm19Target(word, pc) : A64.Imm14Target(word, pc);
                    text.Append("metadata-guard:").Append(word & 31).Append(':').Append(target - function.Start);
                }
                else if ((A64.IsBl(word) || A64.IsB(word)) && !function.Contains(A64.Imm26Target(word, pc)))
                {
                    var target = A64.Imm26Target(word, pc);
                    var owners = facts.EntriesAt(target).Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod).Select(e => e.Method).OfType<MethodRef>().ToArray();
                    var key = owners.Length == 1 ? "method:" + owners[0].Method.Index : "exact:" + target.ToString("x");
                    text.Append(A64.IsBl(word) ? "BL:" : "B:").Append(key);
                }
                else if (A64.IsAdrp(word))
                {
                    text.Append((word & 0x9F00001F).ToString("x8"));
                    if (!adrpSites.Contains(pc)) text.Append(":page:").Append(A64.AdrpPage(word, pc).ToString("x"));
                }
                else if (descriptors.TryGetValue(pc, out var descriptor))
                {
                    var masked = A64.IsAdr(word) ? word & 0x9F00001F : word & ~0x003FFC00u;
                    text.Append(masked.ToString("x8")).Append(':').Append(descriptor);
                }
                else if ((word & 0x3B000000) == 0x18000000)
                    text.Append(word.ToString("x8")).Append(":literal:").Append(A64.Imm19Target(word, pc).ToString("x"));
                else text.Append(word.ToString("x8"));
                text.Append(';');
            }
            // EH 表暂不抽象；绝对区间与动作原值均保留，不为提高匹配率擦掉异常行为。
            foreach (var region in function.ExceptionRegions)
            {
                text.Append("EH:").Append(region);
                foreach (var action in region.Actions) text.Append(action);
            }
            describe?.Invoke(text.ToString());
            return new(System.Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(text.ToString()))), guardCandidates, pairs, branches);
        }

        private bool ValidateGuards(ulong entry, ShapeKey key, FunctionLifter lifter, IdiomRewriter rewriter)
        {
            var candidates = key.GuardCandidates;
            if (candidates.Count == 0) return true;
            if (!guards.TryGetValue(entry, out var known))
            {
                var lifted = lifter.Lift(entry);
                if (!lifted.Succeeded) return false;
                var result = rewriter.Run(lifted.Function);
                if (result.Errors.Count > 0) return false;
                guards[entry] = known = result.Guards;
                guardBranches[entry] = result.MetadataGuardBranches;
            }
            return candidates.IsSubsetOf(known) && key.GuardBranches.IsSubsetOf(guardBranches[entry]);
        }

        private sealed record RegisteredShape(ulong Address, MethodRef Method, ShapeKey Key);

        private Dictionary<string, List<RegisteredShape>> RegisteredShapes()
        {
            var registered = new Dictionary<string, List<RegisteredShape>>();
            foreach (var function in facts.Code.Functions.Where(f => f.Region == CodeRegion.Managed))
            {
                var methods = facts.EntriesAt(function.Start).Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod)
                    .Select(e => e.Method).OfType<MethodRef>().Distinct().ToArray();
                if (methods.Length == 0) continue;
                var key = Fingerprint(function);
                if (!registered.TryGetValue(key.Hash, out var bucket)) registered[key.Hash] = bucket = [];
                foreach (var method in methods) bucket.Add(new(function.Start, method, key));
            }
            facts.Checks.Info("unregistered.shape-calibration", registered.Values.Sum(v => v.Count),
                $"指纹组 {registered.Count}，跨定义组 {registered.Values.Count(ms => ms.Select(m => m.Method.Method).Distinct().Count() > 1)}；同形不是身份真值");
            return registered;
        }

        private string Compare(CodeFunction function, MethodDef definition, AbiSignature signature,
            Dictionary<string, List<RegisteredShape>> registered, out ulong[] matches)
        {
            matches = [];
            var key = Fingerprint(function);
            if (!registered.TryGetValue(key.Hash, out var bucket)) return "B/无同形";
            if (bucket.Any(m => m.Method.Method != definition)) return "B/其他定义或歧义";
            var lifter = new FunctionLifter(facts);
            var rewriter = new IdiomRewriter(facts) { RecordFilter = _ => false };
            if (!ValidateGuards(function.Start, key, lifter, rewriter)) return "B/守卫未证明";
            var guarded = bucket.Where(m => ValidateGuards(m.Address, m.Key, lifter, rewriter)).ToArray();
            if (guarded.Length == 0) return "B/守卫未证明";
            var compatible = guarded.Where(m => Signature(m.Method) is { } sig && Shape(sig) == Shape(signature)).ToArray();
            if (compatible.Length == 0) return "ABI/注册同形体不吻合";
            if (!ProveAddresses(function.Start, key)) return "B/地址用途未证明";
            matches = compatible.Where(m => ProveAddresses(m.Address, m.Key)).Select(m => m.Address).Order().ToArray();
            return matches.Length == 0 ? "B/地址用途未证明" : "接受";
        }

        /// <summary>
        /// CodeScan 只是线性候选索引。真正擦除 ADRP 页之前，在未经传播/删死码的 SSA 上证明：
        /// 每个配对的基址确实来自该 ADRP，且该页的全部使用都是这些配对的地址计算。
        /// φ、存储页值、调用传页值、返回页值或不支持指令均拒绝；不因死定义而漏看用途。
        /// </summary>
        private bool ProveAddresses(ulong entry, ShapeKey key, Action<string>? diagnostic = null)
        {
            if (addressProofs.TryGetValue(entry, out var known)) return known;
            return addressProofs[entry] = Prove();
            bool Prove()
            {
                bool Reject(string reason) { diagnostic?.Invoke(reason); return false; }
                var machine = new Arm64Machine(facts.Code);
                var function = new CfgBuilder(machine, facts.Code).Build(entry);
                if (function.Problems.Count > 0 || function.Blocks.SelectMany(b => b.Statements).Any(s => s is Opaque)) return Reject("CFG/opaque");
                var calls = new FactsCallModel(facts, machine.Convention);
                SsaBuilder.PrepareCalls(function, calls, null);
                foreach (var block in function.Blocks)
                    for (var i = 0; i < block.Statements.Count; i++)
                        if (block.Statements[i] is Return ret)
                            block.Statements[i] = ret with { Pieces = new[] { 0, 1 }.Concat(Enumerable.Range(19, 11))
                                .Select(r => new ReturnPiece(r * 8, new Read(Storage.Gpr(r), 64))).ToArray() };
                var dominators = Dominators.Compute(function);
                SsaBuilder.Build(function, dominators, s => s.Bank is Bank.Gpr or Bank.Vec or Bank.Flags or Bank.Temp, calls, machine.Convention.StackPointer);
                if (SsaCheck.Verify(function, dominators).Count > 0) return Reject("SSA");
                var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
                var pages = statements.OfType<Define>().Where(d => key.AddressPairs.Values.Contains(d.Address)).ToDictionary(d => d.Target, d => d.Address);
                if (!key.AddressPairs.Values.Distinct().All(a => pages.ContainsValue(a))) return Reject("配对缺定义 " + string.Join(',', key.AddressPairs.Where(p => !pages.ContainsValue(p.Value))));
                var proven = new HashSet<ulong>();
                foreach (var stmt in statements)
                {
                    if (stmt is Phi phi && phi.Sources.Any(pages.ContainsKey)) return Reject($"phi 0x{stmt.Address:x} {stmt}");
                    foreach (var use in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).OfType<Use>().Where(u => pages.ContainsKey(u.Variable)))
                    {
                        if (!key.AddressPairs.TryGetValue(stmt.Address, out var source) || source != pages[use.Variable]) return Reject($"来源 0x{stmt.Address:x} {stmt} <- {use}");
                        var word = facts.Code.Word(stmt.Address)!.Value;
                        if (use.Variable.Storage != Storage.Gpr(A64.Rn(word))) return Reject($"基址寄存器 0x{stmt.Address:x}");
                        // STR 的值也可能恰好是页寄存器；只允许它出现在地址操作数中。
                        Expr? address = stmt switch
                        {
                            Define d when A64.IsAddImmediate64(word) => d.Value,
                            Define { Value: Load load } => load.Address,
                            Define { Value: Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: Load load } } => load.Address,
                            Store store => store.Target,
                            _ => null,
                        };
                        if (address is null || !ExprMap.Walk(address).Contains(use)
                            || stmt is Store st && ExprMap.Walk(st.Value).OfType<Use>().Any(u => pages.ContainsKey(u.Variable))) return Reject($"用途 0x{stmt.Address:x} {stmt}");
                        proven.Add(stmt.Address);
                    }
                }
                return key.AddressPairs.Keys.All(proven.Contains) || Reject("未证明 " + string.Join(',', key.AddressPairs.Keys.Where(k => !proven.Contains(k)).Select(k => $"0x{k:x}")));
            }
        }
    }
}
