using Cpp2CS.Native.Images;
using System.Globalization;
using System.Text;
using System.Text.Json;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Native;

/// <summary>有效快照的结构转储。可达块按控制流遍历编号，身份按定义位置编号，不输出对象哈希。</summary>
public static class TextDump
{
    public static string Write(NativeFunction function, bool includeTrace = false)
    {
        if (!ExitChecker.Check(function).IsValid) throw new ArgumentException("只能转储通过出口检查的快照。", nameof(function));
        return new Writer(function, includeTrace).Write();
    }
    private sealed class Writer(NativeFunction f, bool trace)
    {
        private readonly StringBuilder text = new();
        private readonly Dictionary<BlockIdentity, int> blockIds = [];
        private readonly Dictionary<StableIdentity, int> identities = [];
        private readonly Dictionary<Term, string> terms = [];
        private readonly Dictionary<UnknownIdentity, int> unknowns = [];
        private readonly List<string> termDefinitions = [];
        private readonly List<StableIdentity> identityOrder = [];
        private readonly List<Block> order = [];
        private static string Q(string? value) => JsonSerializer.Serialize(value);
        private static string N<T>(T value) where T : IFormattable => value.ToString(null, CultureInfo.InvariantCulture);
        private string B(BlockIdentity block) => "b" + N(blockIds[block]);
        private string Id(StableIdentity identity)
        {
            if (!identities.TryGetValue(identity, out int number))
            {
                identities.Add(identity, number = identities.Count);
                identityOrder.Add(identity);
            }
            return "d" + N(number);
        }
        private string Provenance(StableIdentity identity) => identity.Origin is { } origin ? " origin=" + Id(origin) : "";
        private static string Slot(AbstractSlot slot) => slot.Kind + "[" + N(slot.Position) + "]";
        private string Values(IEnumerable<SlotValue> values) => string.Join(", ", values.OrderBy(x => x.Slot.Kind).ThenBy(x => x.Slot.Position)
            .Select(x => Slot(x.Slot) + "=" + T(x.Value)));
        private string T(Term term)
        {
            var pending = new Stack<(Term Value, bool Ready)>();
            pending.Push((term, false));
            while (pending.TryPop(out var item))
            {
                if (terms.ContainsKey(item.Value)) continue;
                if (!item.Ready && !item.Value.Operands.IsEmpty)
                {
                    pending.Push((item.Value, true));
                    for (int i = item.Value.Operands.Length - 1; i >= 0; i--) pending.Push((item.Value.Operands[i], false));
                    continue;
                }
                string body = Body(item.Value);
                if (item.Value.Operands.IsEmpty) terms.Add(item.Value, body);
                else
                {
                    string name = "t" + N(termDefinitions.Count);
                    terms.Add(item.Value, name);
                    termDefinitions.Add(name + " = " + body);
                }
            }
            return terms[term];
        }
        private string Body(Term term)
        {
            string body = term.Kind switch
            {
                TermKind.Constant => "const " + N(term.ConstantValue!.Value),
                TermKind.Undefined => "undefined",
                TermKind.Unknown => Unknown((UnknownValue)term.Payload!),
                TermKind.Atom => term.Identity switch
                {
                    ResultAtom result => Id(result.Definition) + "." + N(result.Index),
                    ExceptionAtom exception => "exception " + B(exception.Handler),
                    SelectorAtom selector => "selector " + B(selector.Handler),
                    _ => "atom " + Q(term.Identity!.StableText)
                },
                TermKind.Operation => Q(term.Operator!.Name) + "(" + string.Join(",", term.Operands.Select(x => terms[x])) + ")",
                TermKind.Slice => "slice " + N(term.SliceLow!.Value) + "(" + terms[term.Operands[0]] + ")",
                TermKind.Concat => "concat(" + string.Join(",", term.Operands.Select(x => terms[x])) + ")",
                _ => throw new InvalidOperationException("未知项种类。")
            };
            return "(" + body + ":" + N(term.Width) + ")";
        }
        private string Unknown(UnknownValue value)
        {
            if (!unknowns.TryGetValue(value.Identity, out int id)) unknowns.Add(value.Identity, id = unknowns.Count);
            return "unknown u" + N(id) + " " + Why(value.Reason);
        }
        private static string Why(Reason reason) => Q(reason.Code) + ":" + Q(reason.Message)
            + (reason.Cause is null ? "" : " <- " + Why(reason.Cause));
        private void Line(string line) => text.Append(line).Append('\n');
        internal string Write()
        {
            var byId = f.Blocks.ToDictionary(b => b.Identity);
            void Visit(BlockIdentity first)
            {
                var queue = new Queue<BlockIdentity>();
                queue.Enqueue(first);
                while (queue.TryDequeue(out var id))
                {
                    if (blockIds.ContainsKey(id)) continue;
                    blockIds.Add(id, order.Count);
                    var block = byId[id];
                    order.Add(block);
                    foreach (var target in ProgramFacts.Targets(block.End)) queue.Enqueue(target);
                    foreach (var call in block.Statements.OfType<Call>()) if (call.Unwind is { } unwind) queue.Enqueue(unwind);
                }
            }
            Visit(f.Entry);
            // 无入口可达路径的分量保留快照中的相对次序。
            foreach (var block in f.Blocks) Visit(block.Identity);
            foreach (var block in order)
            {
                Id(block.Identity);
                foreach (var merge in block.Merges) Id(merge.Identity);
                foreach (var statement in block.Statements)
                    switch (statement)
                    {
                        case MemoryWrite write:
                            Id(write.Identity);
                            break;
                        case MemoryRead read:
                            Id(read.Identity);
                            break;
                        case Call call:
                            Id(call.Identity);
                            break;
                        case DynamicAllocation allocation:
                            Id(allocation.Identity);
                            break;
                    }
            }
            Line("function address-width=" + N(f.AddressWidth) + " entry=" + B(f.Entry));
            foreach (var input in f.Inputs.OrderBy(x => x.Slot.Kind).ThenBy(x => x.Slot.Position))
                Line("input " + Slot(input.Slot) + " role=" + input.Role + " " + T(input.Value));
            Line("frame " + T(f.Frame.Base));
            if (f.ImageBase is { } imageBase) Line("image-base " + T(imageBase));
            if (f.ThreadPointer is { } threadPointer) Line("thread-pointer " + T(threadPointer));
            if (f.IncomingArgumentArea is { } incoming) Line("incoming-argument-area " + T(incoming));
            foreach (var block in order)
            {
                Line(B(block.Identity) + " " + Id(block.Identity) + Provenance(block.Identity)
                    + (trace && block.Trace is { } source ? " @0x" + source.NativeAddress.ToString("x", CultureInfo.InvariantCulture) : "") + ":");
                if (block.Handler is { } handler)
                    Line("  handler " + T(handler.Exception) + " selector=" + T(handler.Selector) + " clauses=" + string.Join(",", handler.Clauses.Select(c => c.Kind + "(" + string.Join(",", c.Matches.Select(Match)) + ")")));
                foreach (var merge in block.Merges)
                    Line("  merge " + Id(merge.Identity) + Provenance(merge.Identity) + " " + T(merge.Result) + " = "
                        + string.Join(", ", merge.Inputs.OrderBy(x => blockIds[x.Predecessor]).Select(x => B(x.Predecessor) + "=" + T(x.Value))));
                foreach (var statement in block.Statements)
                {
                    string line = statement switch
                    {
                        MemoryRead read => "read " + Id(read.Identity) + Provenance(read.Identity) + " " + T(read.Result) + " = [" + T(read.Address) + "]:" + N(read.Width),
                        MemoryWrite write => "write " + Id(write.Identity) + Provenance(write.Identity) + " [" + T(write.Address) + "]:" + N(write.Width) + " = " + T(write.Value),
                        DynamicAllocation allocation => "allocate " + Id(allocation.Identity) + Provenance(allocation.Identity) + " " + T(allocation.Result)
                            + " size=" + T(allocation.Size) + " align=" + N(allocation.Alignment),
                        Call call => "call " + Id(call.Identity) + Provenance(call.Identity) + " " + Target(call.Target) + " args={" + Values(call.Arguments)
                            + "} results={" + Values(call.Results) + "} noreturn=" + (call.DoesNotReturn ? "true" : "false")
                            + (call.OutgoingArgumentArea is { } outgoing ? " outgoing-argument-area=" + T(outgoing) : "")
                            + (call.Unwind is { } unwind ? " unwind=" + B(unwind) : ""),
                        _ => throw new InvalidOperationException("未知语句。")
                    };
                    if (trace && statement.Trace is { } statementSource) line += " @0x" + statementSource.NativeAddress.ToString("x", CultureInfo.InvariantCulture);
                    Line("  " + line);
                }
                Line("  " + (block.End switch
                {
                    Jump jump => "jump " + B(jump.Target),
                    Branch branch => "branch " + T(branch.Condition) + " " + B(branch.True) + " " + B(branch.False),
                    JumpTable table => "switch " + T(table.Selector) + " {" + string.Join(",", table.Cases.OrderBy(x => x.Value).Select(x => N(x.Value) + "=" + B(x.Target))) + "} default=" + B(table.Default),
                    Return ret => "return {" + Values(ret.Results) + "}",
                    ResumeUnwind resume => "resume " + T(resume.Exception),
                    Unreachable => "unreachable",
                    _ => throw new InvalidOperationException("未知终结。")
                }));
            }
            foreach (var definition in termDefinitions) Line("term " + definition);
            // 来源链也完整输出，包含不在当前快照中的原定义。
            for (int i = 0; i < identities.Count; i++)
            {
                var identity = identityOrder[i];
                Line("identity " + Id(identity) + " " + identity.GetType().Name + Provenance(identity));
            }
            return text.ToString();
        }
        private static string Symbol(ImportSymbol symbol) => Q(symbol.Library) + "/" + Q(symbol.Name)
            + (symbol.Ordinal is { } ordinal ? "#" + N(ordinal) : "");
        private static string Match(PointerTarget target) => target switch
        {
            PointerTarget.Internal value => "offset " + N(value.Offset),
            PointerTarget.Import value => "import " + Symbol(value.Symbol) + "+" + N(value.Addend),
            _ => throw new InvalidOperationException("非法异常匹配对象。")
        };
        private string Target(CallTarget target) => target switch
        {
            ImageFunction function => "entry-offset " + N(function.EntryOffset),
            ImportedTarget import => "import " + Symbol(import.Symbol),
            ComputedTarget computed => T(computed.Value),
            _ => throw new InvalidOperationException("未知调用目标。")
        };
    }
}
