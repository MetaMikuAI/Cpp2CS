using Cpp2CS.Native.Images;
using System.Collections.Immutable;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Native;

public sealed record ContractViolation(string Code, string Location, string Message);
public sealed record FrontendHole(string Location, Term Value, Reason Reason);
public sealed record ExitCheckResult(ImmutableArray<ContractViolation> Violations, ImmutableArray<FrontendHole> Holes)
{
    public bool IsValid => Violations.IsEmpty;
}

public static class ExitChecker
{
    public static ExitCheckResult Check(NativeFunction function) => new CheckContext(function).Run();

    private sealed class CheckContext(NativeFunction f)
    {
        private readonly List<ContractViolation> errors = [];
        private readonly List<FrontendHole> holes = [];
        private readonly HashSet<Term> seenHoles = [];
        private readonly Dictionary<BlockIdentity, Block> blocks = [];
        private readonly Dictionary<BlockIdentity, int[]> points = [];
        private int pointCount = 1;
        private readonly List<(BlockIdentity From, BlockIdentity To, int Point, bool Unwind)> edges = [];
        private readonly Dictionary<Term, int> definitions = [];
        private readonly HashSet<StableIdentity> identities = [];
        private readonly List<(Term Value, int Point, string Location)> uses = [];
        private Dominance dominance = null!;
        private void Error(string code, string location, string message) => errors.Add(new(code, location, message));
        private void Require(bool condition, string code, string location, string message)
        {
            if (!condition) Error(code, location, message);
        }
        private static string Place(int block, int? statement = null) => statement is null ? $"block[{block}]" : $"block[{block}].statement[{statement}]";
        private int NewPoint() => pointCount++;

        private void Identity(StableIdentity identity, string location)
            => Require(identities.Add(identity), "duplicate-identity", location, "稳定身份重复定义。");
        private void Term(Term value, string location)
        {
            var todo = new Stack<Term>();
            var seen = new HashSet<Term>();
            todo.Push(value);
            while (todo.TryPop(out var term))
            {
                if (!seen.Add(term)) continue;
                Require(ReferenceEquals(term.Table, f.Terms), "foreign-term", location, "项来自另一张项表。");
                if (term.Kind == TermKind.Atom)
                    Require(term.Identity is EntryAtom or ResultAtom or RootAtom or ExceptionAtom or SelectorAtom or CallerValue,
                        "atom-vocabulary", location, "原生 IR 不允许前端内部原子或其他层词汇。");
                if (term.Kind == TermKind.Unknown && seenHoles.Add(term)) holes.Add(new(location, term, term.Why!));
                foreach (var child in term.Operands) todo.Push(child);
            }
        }
        private void Define(Term term, int point, string location)
        {
            Term(term, location);
            Require(term.Kind == TermKind.Atom, "definition-kind", location, "定义结果必须是具名原子。");
            Require(definitions.TryAdd(term, point), "duplicate-definition", location, "原子重复定义。");
        }
        private void Result(Term term, StableIdentity identity, int index, int point, string location)
        {
            Define(term, point, location);
            Require(term.Identity is ResultAtom atom && ReferenceEquals(atom.Definition, identity) && atom.Index == index,
                "result-identity", location, "结果原子必须引用本定义的身份及结果序号。");
        }
        private void Use(Term term, int point, string location)
        {
            Term(term, location);
            uses.Add((term, point, location));
        }
        private void Width(bool valid, string location) => Require(valid, "width", location, "位宽不符合操作或地址契约。");
        private void Slots(IEnumerable<SlotValue> values, string location)
        {
            var seen = new HashSet<AbstractSlot>();
            foreach (var item in values)
            {
                Slot(item.Slot, location);
                Require(seen.Add(item.Slot), "duplicate-slot", location, "抽象槽重复。");
            }
        }
        private void Slot(AbstractSlot slot, string location) => Require(Enum.IsDefined(slot.Kind) && slot.Kind != SlotKind.ArgumentArea && slot.Position >= 0
            && (slot.Kind != SlotKind.IndirectResult || slot.Position == 0), "slot", location, "抽象槽种类、序号或偏移不合法。");
        private void Edge(BlockIdentity from, BlockIdentity to, int point, bool unwind, string location)
        {
            if (!points.ContainsKey(to))
            {
                Error("target", location, "目标块不存在。");
                return;
            }
            edges.Add((from, to, point, unwind));
            Require(unwind == (blocks[to].Handler is not null), "handler-edge", location, "展开边必须指向处理入口；普通边不能进入处理入口。");
        }
        internal ExitCheckResult Run()
        {
            Require(f.AddressWidth > 0, "width", "function", "地址位宽必须为正。");
            NormalizeCollections();
            IndexBlocks();
            CheckEntry();
            CheckBlocks();
            CheckMerges();
            ComputeDominators();
            CheckUses();
            return Finish();
        }
        private void IndexBlocks()
        {
            for (int i = 0; i < f.Blocks.Length; i++)
            {
                var b = f.Blocks[i];
                Identity(b.Identity, Place(i));
                if (!blocks.TryAdd(b.Identity, b))
                {
                    Error("duplicate-block", Place(i), "块身份重复。");
                    continue;
                }
                points.Add(b.Identity, Enumerable.Range(0, b.Statements.Length + 2).Select(_ => NewPoint()).ToArray());
            }
            Require(points.ContainsKey(f.Entry), "entry", "function", "入口块不存在。");

        }
        private void CheckEntry()
        {
            Slots(f.Inputs.Select(x => new SlotValue(x.Slot, x.Value)), "inputs");
            foreach (var input in f.Inputs)
            {
                Define(input.Value, 0, "inputs");
                Require(input.Value.Identity is EntryAtom atom && atom.Slot == input.Slot, "entry-identity", "inputs", "入口原子与抽象槽不一致。");
                Require(Enum.IsDefined(input.Role) && (input.Role == InputRole.IndirectResult) == (input.Slot.Kind == SlotKind.IndirectResult),
                    "input-role", "inputs", "入口角色与间接结果槽不一致。");
            }
            Require(f.Inputs.Count(x => x.Role == InputRole.MethodInformation) <= 1, "input-role", "inputs", "方法信息参数只能有一个。");
            Define(f.Frame.Base, 0, "frame");
            Width(f.Frame.Base.Width == f.AddressWidth, "frame");
            Require(f.Frame.Base.Identity is RootAtom { Kind: AddressRoot.Frame }, "root", "frame", "帧基址必须是帧根原子。");
            Root(f.ImageBase, AddressRoot.Image, "image-base");
            Root(f.ThreadPointer, AddressRoot.Thread, "thread-pointer");
            if (f.IncomingArgumentArea is { } area)
            {
                Width(area.Width == f.AddressWidth, "incoming-argument-area");
                Use(area, 0, "incoming-argument-area");
            }
        }
        private void CheckBlocks()
        {
            var visitedBlocks = new HashSet<BlockIdentity>();
            for (int bi = 0; bi < f.Blocks.Length; bi++)
            {
                var b = f.Blocks[bi];
                if (!visitedBlocks.Add(b.Identity)) continue;
                var p = points[b.Identity];
                var location = Place(bi);

                if (b.Handler is { } handler)
                {
                    Define(handler.Selector, p[0], location);
                    Require(handler.Selector.Identity is SelectorAtom selector && ReferenceEquals(selector.Handler, b.Identity),
                        "selector-identity", location, "选择值必须引用处理入口身份。");
                    Define(handler.Exception, p[0], location);
                    Width(handler.Exception.Width == f.AddressWidth, location);
                    Require(handler.Exception.Identity is ExceptionAtom atom && ReferenceEquals(atom.Handler, b.Identity),
                        "exception-identity", location, "异常对象必须引用处理入口身份。");
                    Require(!handler.Clauses.IsEmpty && handler.Clauses.All(c => Enum.IsDefined(c.Kind)
                        && (!c.Matches.IsDefault && c.Matches.All(m => m is PointerTarget.Internal or PointerTarget.Import)
                            && (c.Kind is ClauseKind.Cleanup or ClauseKind.CatchAll ? c.Matches.IsEmpty : c.Kind != ClauseKind.Catch || c.Matches.Length == 1))),
                        "clause", location, "处理入口需要合法的匹配子句。");
                }
                foreach (var merge in b.Merges)
                {
                    Identity(merge.Identity, location);
                    Result(merge.Result, merge.Identity, 0, p[0], location);
                }
                for (int si = 0; si < b.Statements.Length; si++)
                {
                    var s = b.Statements[si];
                    var loc = Place(bi, si);
                    foreach (var term in ProgramFacts.Uses(s)) Use(term, p[si + 1], loc);

                    switch (s)
                    {
                        case MemoryRead read:
                            Identity(read.Identity, loc);
                            Result(read.Result, read.Identity, 0, p[si + 2], loc);
                            Width(read.Width > 0 && read.Width == read.Result.Width && read.Address.Width == f.AddressWidth, loc);
                            break;
                        case MemoryWrite write:
                            Identity(write.Identity, loc);
                            Width(write.Width > 0 && write.Width == write.Value.Width && write.Address.Width == f.AddressWidth, loc);
                            break;
                        case DynamicAllocation allocation:
                            Identity(allocation.Identity, loc);
                            Result(allocation.Result, allocation.Identity, 0, p[si + 2], loc);
                            Width(allocation.Result.Width == f.AddressWidth && allocation.Size.Width == f.AddressWidth, loc);
                            Require(Aligned(allocation.Alignment), "alignment", loc, "动态分配对齐必须是正的二次幂。");
                            break;
                        case Call call:
                            if (call.OutgoingArgumentArea is { } outgoing) Width(outgoing.Width == f.AddressWidth, loc);
                            Identity(call.Identity, loc);
                            Slots(call.Arguments, loc);
                            Slots(call.Results, loc);
                            for (int ri = 0; ri < call.Results.Length; ri++) Result(call.Results[ri].Value, call.Identity, ri, p[si + 2], loc);
                            if (call.Unwind is { } unwind) Edge(b.Identity, unwind, p[si + 1], true, loc);
                            Require(!call.DoesNotReturn || (si == b.Statements.Length - 1 && b.End is Unreachable && call.Results.IsEmpty),
                                "noreturn", loc, "不返回调用必须结束块，后接不可达且没有结果定义。");
                            Require(call.Target switch
                            {
                                ImageFunction => true,
                                ImportedTarget import => import.Symbol is { } symbol && (!string.IsNullOrWhiteSpace(symbol.Name) || symbol.Ordinal is not null),
                                ComputedTarget target => target.Value.Width == f.AddressWidth,
                                _ => false
                            }, "call-target", loc, "调用目标种类、导入名称或间接目标位宽不合法。");
                            break;
                    }
                }
                foreach (var term in ProgramFacts.Uses(b.End)) Use(term, p[^1], location + ".end");
                foreach (var target in ProgramFacts.Targets(b.End)) Edge(b.Identity, target, p[^1], false, location + ".end");
                if (b.End is Branch branch) Width(branch.Condition.Width == 1, location);
                if (b.End is Return ret) Slots(ret.Results, location);
                if (b.End is ResumeUnwind resume) Width(resume.Exception.Width == f.AddressWidth, location);
                if (b.End is JumpTable table)
                    Require(table.Cases.Select(c => c.Value).Distinct().Count() == table.Cases.Length
                        && table.Cases.All(c => c.Value.Sign >= 0 && c.Value < (System.Numerics.BigInteger.One << table.Selector.Width)),
                        "switch-case", location, "跳转表标签重复或超出选择项位宽。");
            }
        }
        private void CheckMerges()
        {
            var incomingEdges = edges.ToLookup(e => e.To);
            for (int bi = 0; bi < f.Blocks.Length; bi++)
            {
                var b = f.Blocks[bi];
                var incoming = incomingEdges[b.Identity].ToArray();
                var byPredecessor = incoming.ToLookup(e => e.From);
                var expected = byPredecessor.Select(group => group.Key).ToHashSet();
                Require(!ReferenceEquals(b.Identity, f.Entry) || b.Merges.IsEmpty, "entry-merge", Place(bi), "入口块不能有前驱合流。");
                foreach (var merge in b.Merges)
                {
                    Require(merge.Inputs.Length == expected.Count && merge.Inputs.Select(x => x.Predecessor).ToHashSet().SetEquals(expected),
                        "merge-predecessors", Place(bi), "合流操作数必须与前驱块一一对应。");
                    foreach (var input in merge.Inputs)
                    {
                        Width(input.Value.Width == merge.Result.Width, Place(bi));
                        Term(input.Value, Place(bi));
                        var matching = byPredecessor[input.Predecessor].ToArray();
                        if (matching.Length == 0) Use(input.Value, 0, Place(bi) + ".merge");
                        foreach (var edge in matching) Use(input.Value, edge.Point, Place(bi) + ".merge");
                    }
                }
            }
        }
        private void CheckUses()
        {
            foreach (var (value, point, location) in uses)
            {
                var todo = new Stack<Term>();
                var seen = new HashSet<Term>();
                todo.Push(value);
                while (todo.TryPop(out var term))
                {
                    if (!seen.Add(term)) continue;
                    if (term.Identity is CallerValue caller)
                        Require(caller.Index >= 0, "caller-index", location, "调用方值序号不能为负。");
                    else if (term.Kind == TermKind.Atom)
                    {
                        if (!definitions.TryGetValue(term, out var definition)) Error("undefined-atom", location, "使用的原子没有定义。");
                        else Require(dominance.Dominates(definition, point), "dominance", location, "定义不支配使用（展开边不取得调用结果）。");
                    }
                    foreach (var child in term.Operands) todo.Push(child);
                }
            }
        }
        private void NormalizeCollections()
        {
            ImmutableArray<T> Array<T>(ImmutableArray<T> values, string location)
            {
                if (!values.IsDefault) return values;
                Error("collection", location, "集合必须显式初始化，空集合使用 []。");
                return [];
            }
            var normalized = f.Blocks.Select((b, bi) => b with
            {
                Merges = Array(b.Merges, Place(bi)).Select(m => m with { Inputs = Array(m.Inputs, Place(bi)) }).ToImmutableArray(),
                Statements = Array(b.Statements, Place(bi)).Select((s, si) => s is Call call ? call with
                {
                    Arguments = Array(call.Arguments, Place(bi, si)),
                    Results = Array(call.Results, Place(bi, si))
                } : s).ToImmutableArray(),
                Handler = b.Handler is { } handler ? handler with { Clauses = Array(handler.Clauses, Place(bi)) } : null,
                End = b.End switch
                {
                    Return ret => ret with { Results = Array(ret.Results, Place(bi)) },
                    JumpTable table => table with { Cases = Array(table.Cases, Place(bi)) },
                    _ => b.End
                }
            }).ToImmutableArray();
            f = new(f.Terms, f.Entry, f.AddressWidth, f.Inputs,
                f.Frame, f.ImageBase, f.ThreadPointer, f.IncomingArgumentArea, normalized);
        }
        private static bool Aligned(int value) => value > 0 && (value & (value - 1)) == 0;
        private ExitCheckResult Finish() => new(errors.ToImmutableArray(), holes.ToImmutableArray());
        private void Root(Term? value, AddressRoot kind, string location)
        {
            if (value is null) return;
            Define(value, 0, location);
            Width(value.Width == f.AddressWidth, location);
            Require(value.Identity is RootAtom atom && atom.Kind == kind, "root", location, "地址根必须是约定的原子。");
        }
        private void ComputeDominators()
        {
            dominance = new Dominance(f, points, pointCount);
        }
    }
}
