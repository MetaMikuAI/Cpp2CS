using Cpp2CS.IR;
using Cpp2CS.Abi;

namespace Cpp2CS.Native;

public sealed partial class FunctionLifter
{
    private LiftResult LiftLoops(LiftResult result, NativeState entry)
    {
        var graph = result.Graph; var regions = new NaturalLoops(graph);
        if (!regions.Reducible || regions.Loops.Any(l => l.Header == graph.Entry || l.Nodes.Any(n => graph.Blocks[n].Instructions.Any(i =>
            i.Operands.Any(o => o.Base == "sp") && (i.Mnemonic.StartsWith("st") || i.Writeback)))))
        { result.Problems.Add("循环需要可归约区域及不变的栈布局"); return result; }
        var uses = new Dictionary<ulong, HashSet<string>>(); var definitions = new Dictionary<ulong, HashSet<string>>();
        foreach (var block in graph.Blocks.Values)
        {
            var use = new HashSet<string>(); var define = new HashSet<string>();
            foreach (var instruction in block.Instructions)
            {
                var reads = instruction.Reads.Select(Canonical).Where(Register).ToHashSet();
                var writes = instruction.Writes.Select(Canonical).Where(Register).ToHashSet();
                if (instruction.Mnemonic == "bl")
                {
                    var target = NativeGraph.Target(instruction);
                    if (runtime.Helpers.TryGetValue(target, out var helper))
                        reads.UnionWith(Enumerable.Range(0, helper.Kind is "Box" or "AllocateArray" or "IsInstance" ? 2 : helper.NoReturn ? 0 : 1).Select(n => "x" + n));
                    else
                        foreach (var method in symbols.Methods.GetValueOrDefault(target, []))
                            if (Classify(method) is { } abi) reads.UnionWith(abi.Arguments.SelectMany(a => a.Pieces).Select(p => p.Location).OfType<RegisterLocation>().Select(r => Canonical(r.Name.ToLowerInvariant())));
                    writes.UnionWith(Enumerable.Range(0, 19).Select(n => "x" + n));
                    writes.UnionWith(Enumerable.Range(0, 32).Where(n => n < 8 || n >= 16).Select(n => "v" + n));
                }
                use.UnionWith(reads.Except(define)); define.UnionWith(writes);
            }
            uses[block.Address] = use; definitions[block.Address] = define;
        }
        var live = graph.Blocks.Keys.ToDictionary(k => k, k => new HashSet<string>(uses[k]));
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var block in graph.Blocks.Values.Reverse())
            {
                var next = uses[block.Address].Concat(block.Successors.SelectMany(s => live[s]).Except(definitions[block.Address])).ToHashSet();
                if (!next.SetEquals(live[block.Address])) { live[block.Address] = next; changed = true; }
            }
        }
        var incoming = new Dictionary<ulong, List<(ulong Predecessor, NativeState State)>> { [graph.Entry] = [(graph.Entry, entry)] };
        var outgoing = new Dictionary<ulong, NativeState>();
        var variables = new List<(NaturalLoop Loop, string Register, NativeValue Value, (ulong Predecessor, NativeValue Value)[] Entry)>();
        foreach (var address in regions.Order)
        {
            if (!incoming.TryGetValue(address, out var states)) continue;
            var state = Merge(address, states);
            if (result.Finally is { } cleanup && address == cleanup.Header)
            {
                var type = cleanup.StorageType;
                var initial = Project(NativeValues.LoadStack(state, stackRegion, cleanup.StorageOffset, layouts.Size(type)));
                if (initial.Expression is UnknownExpression) { result.Problems.Add("清理接收者的入口值不完整"); return result; }
                var name = $"enumerator_{address:x}";
                if (states.Count != 1 || result.Blocks[states[0].Predecessor].Successors.Length != 1)
                { result.Problems.Add("清理区域入口需要唯一初始化边"); return result; }
                result.Blocks[states[0].Predecessor].Statements.Add(new AssignStatement(address, name, initial.Expression, type));
                var value = new NativeValue(new InputBits(name, layouts.Size(type) * 8), type, new NameExpression(name));
                aggregateValues[value.Bits] = (type, value.Expression);
                if (aggregateLogicalTypes.TryGetValue(initial.Bits, out var logical)) aggregateLogicalTypes[value.Bits] = logical;
                mutableStack[cleanup.StorageOffset] = (name, type);
                NativeValues.StoreStack(state, stackRegion, cleanup.StorageOffset, value, name);
            }
            foreach (var loop in regions.Loops.Where(l => l.Header == address))
            {
                var modified = loop.Nodes.SelectMany(n => definitions[n]).ToHashSet();
                foreach (var register in live[address].Where(modified.Contains))
                {
                    var original = Read(state, register);
                    if (original.Type == "unknown") { result.Problems.Add("循环入口寄存器类型未确定：" + register); continue; }
                    var name = $"loop_{address:x}_{register}";
                    var value = new NativeValue(new InputBits(name, original.Bits.Width), original.Type, new NameExpression(name));
                    state.Registers[register] = value;
                    variables.Add((loop, register, value, states.Select(s => (s.Predecessor, Read(s.State, register))).ToArray()));
                }
                state.Comparison = null;
            }
            var block = graph.Blocks[address]; var lifted = new LiftedBlock(address, [], null, block.Successors);
            result.Blocks[address] = lifted;
            foreach (var instruction in block.Instructions)
                if (Step(instruction, state, lifted.Statements, result) is { } condition) lifted = lifted with { Condition = condition };
            result.Blocks[address] = lifted; outgoing[address] = state.Copy();
            foreach (var successor in block.Successors)
            {
                if (regions.Loops.Any(l => l.Header == successor && l.Latches.Contains(address))) continue;
                if (!incoming.TryGetValue(successor, out var list)) incoming[successor] = list = [];
                list.Add((address, state.Copy()));
            }
        }
        PhiLowering.Apply(result);
        var assignments = new Dictionary<(ulong Predecessor, ulong Header), List<(string Name, NativeValue Value)>>();
        foreach (var variable in variables)
        {
            var name = ((NameExpression)variable.Value.Expression).Name;
            result.Blocks[graph.Entry].Statements.Insert(0, new DeclareStatement(graph.Entry, name, symbols.Display(variable.Value.Type)));
            foreach (var (predecessor, value) in variable.Entry.Concat(variable.Loop.Latches.Select(l => (l, Read(outgoing[l], variable.Register)))))
            {
                if (value.Type != variable.Value.Type) result.Problems.Add($"循环回边类型不一致：{name}: {value.Type} / {variable.Value.Type}");
                var edge = (predecessor, variable.Loop.Header);
                if (!assignments.TryGetValue(edge, out var list)) assignments[edge] = list = [];
                list.Add((name, value));
            }
        }
        var synthetic = ulong.MaxValue - 1;
        foreach (var (edge, copies) in assignments)
        {
            while (result.Blocks.ContainsKey(synthetic)) synthetic--;
            var address = synthetic--;
            var predecessor = result.Blocks[edge.Predecessor];
            result.Blocks[edge.Predecessor] = predecessor with { Successors = predecessor.Successors.Select(s => s == edge.Header ? address : s).ToArray() };
            var block = new LiftedBlock(address, [], null, [edge.Header]); result.Blocks.Add(address, block);
            block.Statements.AddRange(copies.Select((c, index) => new AssignStatement(address, $"edge_{address:x}_{index}", c.Value.Expression, c.Value.Type)));
            block.Statements.AddRange(copies.Select((c, index) => new SetLocalStatement(address, c.Name, new NameExpression($"edge_{address:x}_{index}"))));
        }
        SemanticValidation.Check(result);
        result.Proofs.Add(new(graph.Entry, "LoopRegisterPhi", "dominator-checked natural loops; live modified registers have stable typed identities; all entry/backedge values checked; parallel copies preserve swaps; loop stack writes rejected"));
        return result;
        static bool Register(string r) => r.Length > 1 && r[0] is 'x' or 'v' && int.TryParse(r.AsSpan(1), out var n) && n < (r[0] == 'x' ? 29 : 32);
    }
}
