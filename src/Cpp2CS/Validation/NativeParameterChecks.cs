using System.Collections.Immutable;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Validation;

public static class NativeParameterChecks
{
    private const string Image = "fixture:native-parameters";

    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        foreach (var architecture in Enum.GetValues<Architecture>())
        {
            var first = architecture == Architecture.Arm64 ? "x0" : "rax";
            var second = architecture == Architecture.Arm64 ? "x1" : "rcx";
            void Constant(MirBuilder builder) => builder.Write(first, builder.Const(64, 7));
            void Swap(MirBuilder builder)
            {
                var a = builder.Read(first, 64);
                var b = builder.Read(second, 64);
                builder.Write(first, b);
                builder.Write(second, a);
            }
            var chain = Fixture(architecture, [[1], [2], []], [Constant, null, null]);
            var aliases = NativeParameterAnalysis.FindAliases(chain);
            var definition = Block(chain, 0).FinalState.Slots[first];
            Check(aliases.GetValueOrDefault(Parameter(chain, 1, first).Id) == definition &&
                aliases.GetValueOrDefault(Parameter(chain, 2, first).Id) == definition,
                "single-predecessor parameters resolve transitively to the dominating definition");
            Check(Block(chain, 0).Parameters.All(parameter => !aliases.ContainsKey(parameter.Value.Id)),
                "external entry parameters retain their independent inputs");
            Check(chain.Blocks.All(block => !aliases.ContainsKey(block.InitialState.World.Id)),
                "World parameters are preserved independently of scalar aliases");

            var diamond = Fixture(architecture, [[1, 2], [3], [3], []], [Constant, null, null, null]);
            aliases = NativeParameterAnalysis.FindAliases(diamond);
            Check(aliases.GetValueOrDefault(Parameter(diamond, 3, first).Id) == Block(diamond, 0).FinalState.Slots[first],
                "diamond join collapses after both arm parameters resolve to the same definition");
            var differing = Fixture(architecture, [[1, 2], [3], [3], []],
                [null, Constant, builder => builder.Write(first, builder.Const(64, 9)), null]);
            aliases = NativeParameterAnalysis.FindAliases(differing);
            Check(!aliases.ContainsKey(Parameter(differing, 3, first).Id),
                "a diamond with different definitions preserves its join parameter");
            var equalLiterals = Fixture(architecture, [[1, 2], [3], [3], []], [null, Constant, Constant, null]);
            Check(!NativeParameterAnalysis.FindAliases(equalLiterals).ContainsKey(Parameter(equalLiterals, 3, first).Id),
                "parameter analysis does not equate distinct literal definitions without a value proof");

            var carry = Fixture(architecture, [[1], [1]], [Constant, null]);
            aliases = NativeParameterAnalysis.FindAliases(carry);
            Check(aliases.GetValueOrDefault(Parameter(carry, 1, first).Id) == Block(carry, 0).FinalState.Slots[first],
                "a self-loop carrying one external definition removes the redundant parameter");
            var increment = Fixture(architecture, [[1], [1]],
                [null, builder => builder.Write(first, builder.Add(builder.Read(first, 64), builder.Const(64, 1)))]);
            Check(!NativeParameterAnalysis.FindAliases(increment).ContainsKey(Parameter(increment, 1, first).Id),
                "a changing loop value remains a loop-carried parameter");
            var swap = Fixture(architecture, [[1], [1]], [null, Swap]);
            aliases = NativeParameterAnalysis.FindAliases(swap);
            Check(!aliases.ContainsKey(Parameter(swap, 1, first).Id) && !aliases.ContainsKey(Parameter(swap, 1, second).Id),
                "a swap loop with distinct initial values retains both mutually dependent parameters");
            var equalSwap = Fixture(architecture, [[1], [1]], [builder =>
            {
                var value = builder.Const(64, 7);
                builder.Write(first, value);
                builder.Write(second, value);
            }, Swap]);
            aliases = NativeParameterAnalysis.FindAliases(equalSwap);
            definition = Block(equalSwap, 0).FinalState.Slots[first];
            Check(aliases.GetValueOrDefault(Parameter(equalSwap, 1, first).Id) == definition &&
                aliases.GetValueOrDefault(Parameter(equalSwap, 1, second).Id) == definition,
                "a mutually dependent swap component with one external definition collapses as a group");

            var irreducible = Fixture(architecture, [[2], [3], [3], [2]], [null, null, null, null], [0, 1]);
            aliases = NativeParameterAnalysis.FindAliases(irreducible);
            Check(!aliases.ContainsKey(Parameter(irreducible, 2, first).Id) && !aliases.ContainsKey(Parameter(irreducible, 3, first).Id),
                "irreducible cycles reached from distinct external entries retain both input sources");
            var dominance = new NativeDominance(irreducible);
            Check(!dominance.Dominates(Block(irreducible, 0).Id, Block(irreducible, 2).Id) &&
                !dominance.Dominates(Block(irreducible, 1).Id, Block(irreducible, 3).Id),
                "the synthetic root prevents one explicit entry from dominating another entry's paths");
            var entryLoop = Fixture(architecture, [[1], [0]], [Constant, null], [0, 1]);
            Check(NativeParameterAnalysis.FindAliases(entryLoop).Count == 0,
                "incoming backedges never turn explicitly seeded blocks into derived-only entries");

            var parallel = Fixture(architecture, [[1, 1], []], [null, null]);
            aliases = NativeParameterAnalysis.FindAliases(parallel);
            Check(aliases.GetValueOrDefault(Parameter(parallel, 1, first).Id) == Parameter(parallel, 0, first),
                "parallel edges with equal arguments permit a parameter alias");
            var start = Block(parallel, 0);
            var target = Block(parallel, 1);
            var parameterIndex = Array.FindIndex(target.Parameters.ToArray(), parameter => parameter.Slot == first);
            var changedEdge = start.Edges[1] with { Arguments = start.Edges[1].Arguments.SetItem(parameterIndex, Parameter(parallel, 0, second)) };
            var differentParallel = Replace(parallel, start with { Edges = start.Edges.SetItem(1, changedEdge) });
            Check(!NativeParameterAnalysis.FindAliases(differentParallel).ContainsKey(Parameter(parallel, 1, first).Id),
                "each parallel edge contributes its own argument rather than being deduplicated by predecessor");

            // 以下输入刻意破坏 SSA 前提，分析不得由它们制造可用的常量或前向定义。
            start = Block(carry, 0);
            target = Block(carry, 1);
            parameterIndex = Array.FindIndex(target.Parameters.ToArray(), parameter => parameter.Slot == first);
            var selfOnly = Replace(carry, start with { Edges = start.Edges.SetItem(0,
                start.Edges[0] with { Arguments = start.Edges[0].Arguments.SetItem(parameterIndex, Parameter(carry, 1, first)) }) });
            Check(!NativeParameterAnalysis.FindAliases(selfOnly).ContainsKey(Parameter(carry, 1, first).Id),
                "a self-only dependency component has no known external value and cannot be erased");
            var forward = Fixture(architecture, [[1], []], [null, Constant]);
            start = Block(forward, 0);
            target = Block(forward, 1);
            parameterIndex = Array.FindIndex(target.Parameters.ToArray(), parameter => parameter.Slot == first);
            forward = Replace(forward, start with { Edges = start.Edges.SetItem(0,
                start.Edges[0] with { Arguments = start.Edges[0].Arguments.SetItem(parameterIndex, target.FinalState.Slots[first]) }) });
            Check(!NativeParameterAnalysis.FindAliases(forward).ContainsKey(Parameter(forward, 1, first).Id),
                "a result produced inside the target block cannot replace its entry parameter");
            var bypass = Fixture(architecture, [[1, 2], [3], [3], []], [null, Constant, null, null]);
            var source = Block(bypass, 1).FinalState.Slots[first];
            start = Block(bypass, 2);
            target = Block(bypass, 3);
            parameterIndex = Array.FindIndex(target.Parameters.ToArray(), parameter => parameter.Slot == first);
            bypass = Replace(bypass, start with { Edges = start.Edges.SetItem(0,
                start.Edges[0] with { Arguments = start.Edges[0].Arguments.SetItem(parameterIndex, source) }) });
            Check(!NativeParameterAnalysis.FindAliases(bypass).ContainsKey(Parameter(bypass, 3, first).Id),
                "one syntactically equal argument cannot supply a definition absent from a bypass path");

            // 归约后的块不再有完整参数列表；实参位置以目标当前参数列表为准。
            var sparse = chain with { Blocks = chain.Blocks.Select(block => block with
            {
                Parameters = block.Parameters.Where(parameter => parameter.Slot == first || parameter.Slot is null).ToImmutableArray(),
                Edges = block.Edges.Select(edge => edge.Target is { } id ? edge with
                {
                    Arguments = chain.Blocks.Single(item => item.Id == id).Parameters.Select((parameter, index) => (parameter, index))
                        .Where(item => item.parameter.Slot == first || item.parameter.Slot is null)
                        .Select(item => edge.Arguments[item.index]).ToImmutableArray()
                } : edge).ToImmutableArray()
            }).ToImmutableArray() };
            Check(NativeParameterAnalysis.FindAliases(sparse).GetValueOrDefault(Parameter(sparse, 2, first).Id) ==
                Block(sparse, 0).FinalState.Slots[first], "parameter positions follow the reduced target parameter list");
        }
        return checks;
    }

    private static NativeBlock Block(NativeRegion region, int index) => region.Blocks.Single(block => block.Source.Address == Address(index));
    private static NativeValue Parameter(NativeRegion region, int index, string slot) => Block(region, index).Parameters.Single(parameter => parameter.Slot == slot).Value;
    private static ulong Address(int index) => 0x1000UL + (ulong)index * 4;
    private static NativeRegion Replace(NativeRegion region, NativeBlock replacement) =>
        region with { Blocks = region.Blocks.SetItem(Array.FindIndex(region.Blocks.ToArray(), block => block.Id == replacement.Id), replacement) };

    private static NativeRegion Fixture(Architecture architecture, int[][] targets, Action<MirBuilder>?[] bodies, int[]? entries = null)
    {
        var instructions = new List<MirInstruction>();
        for (var index = 0; index < targets.Length; index++)
        {
            var builder = new MirBuilder(architecture, new(Image, Address(index), index * 4,
                architecture == Architecture.Arm64 ? new byte[4] : new byte[] { 0x90 }), "fixture.native-parameters");
            bodies[index]?.Invoke(builder);
            var exit = targets[index].Length switch
            {
                0 => MirExit.Jump(builder.Read(architecture == Architecture.Arm64 ? "x0" : "rax", 64)),
                1 => MirExit.Next(Address(targets[index][0])),
                2 => MirExit.Branch(builder.Read(architecture == Architecture.Arm64 ? "z" : "zf", 1),
                    builder.Const(64, Address(targets[index][0])), builder.Const(64, Address(targets[index][1]))),
                _ => throw new InvalidOperationException("Fixture has more than two successors")
            };
            instructions.Add(builder.Finish(exit));
        }
        return StateSsaConverter.Convert(RegionBuilder.FromInstructions(architecture, Image, instructions,
            (entries ?? [0]).Select(index => new EntrySeed(Address(index), "synthetic parameter analysis"))));
    }
}
