using System.Collections.Immutable;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Validation;

public static class NativeNormalizationChecks
{
    public static int Run()
    {
        var checks = 0;
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        {
            var input = architecture == Architecture.Arm64 ? "x0" : "rax";
            var output = architecture == Architecture.Arm64 ? "x1" : "rcx";
            const string image = "fixture:native-normalization";
            MirBuilder Builder(ulong address) => new(architecture, new(image, address, (long)address, new byte[4]), "fixture.normalization");
            var first = Builder(0x1000);
            first.Write(output, first.Const(64, 17));
            var second = Builder(0x1004);
            var original = second.Read(input, 64);
            var saved = second.Read(output, 64);
            var expression = second.Sub(second.Add(original, saved), saved);
            second.Write(input, expression);
            second.Write(output, second.Add(saved, second.Const(64, 3)));
            var choice1 = second.Undefined(8, "independent choice");
            var choice2 = second.Undefined(8, "independent choice");
            second.Write(output, second.Add(second.Read(output, 64), second.Zext(second.Sub(choice1, choice2), 64)));
            second.LoadIf(second.Const(1, 0), second.Const(64, ulong.MaxValue), 64);
            var graph = RegionBuilder.FromInstructions(architecture, image,
                [first.Finish(MirExit.Next(0x1004)), second.Finish(MirExit.Next(0x1008))], [new(0x1000, "normalization fixture")], 8);
            var mechanical = StateSsaConverter.Convert(graph);
            var normalized = NativeNormalizer.Normalize(mechanical);
            Require(NativeNormalizationValidator.Validate(normalized).Count == 0, "normalization replay and use-def validation");
            Require(normalized.ReachedFixedPoint && normalized.Statistics.Parameters < normalized.Statistics.OriginalParameters &&
                normalized.Statistics.Nodes < normalized.Statistics.OriginalNodes, "normalization actually removes parameters and nodes");
            Require(normalized.Region.Blocks.SelectMany(b => b.Nodes).Count(n => n.Code == OpCode.Undefined) == 2,
                "identical choice syntax preserves two dynamic producers");
            Require(normalized.Region.Blocks.SelectMany(b => b.Nodes).Count(n => n.Code == OpCode.LoadIf) == 1,
                "inactive load remains an effect stage");
            var limited = NativeNormalizer.Normalize(mechanical, 1);
            Require(!limited.ReachedFixedPoint && NativeNormalizationValidator.Validate(limited).Count == 0,
                "round budget reports unfinished fixed point without claiming a complete reduction");
            var repeated = NativeNormalizer.Run(normalized.Region, 64);
            Require(repeated.Rewrites.IsEmpty, "fixed point is idempotent");
            foreach (var value in new ulong[] { 0, 1, 17, 0x8000000000000000, ulong.MaxValue })
            {
                var state = NativeExecutionChecks.State(architecture);
                state.Slots[input] = value;
                state.ChoiceInputs.Enqueue(23);
                state.ChoiceInputs.Enqueue(9);
                checks += NativeExecutionChecks.Compare(graph, 0x1000, state, 8);
            }
            // 消去 x-x 等表达式不能掩盖原 ReadSlot 的环境停止。
            checks += NativeExecutionChecks.Compare(graph, 0x1000, new MachineState(), 8);

            Reject(normalized with { Revision = "unrelated" }, "changed output revision");
            Reject(normalized with { RuleVersion = "unknown" }, "unknown rules");
            Reject(normalized with { ReachedFixedPoint = !normalized.ReachedFixedPoint }, "false completion claim");
            Reject(normalized with { Statistics = normalized.Statistics with { Parameters = 0 } }, "false reduction count");
            Reject(normalized with { Rewrites = [] }, "missing rewrite evidence");
            Reject(normalized with { Rewrites = normalized.Rewrites.SetItem(0, normalized.Rewrites[0] with { Rule = "unproved" }) }, "changed rule evidence");
            var blockIndex = Enumerable.Range(0, normalized.Region.Blocks.Length).First(i => normalized.Region.Blocks[i].Nodes.Length != 0);
            var block = normalized.Region.Blocks[blockIndex];
            var mutated = block with { Nodes = block.Nodes.RemoveAt(0) };
            Reject(normalized with { Region = normalized.Region with { Blocks = normalized.Region.Blocks.SetItem(blockIndex, mutated) } }, "deleted node");
            mutated = block with { Steps = block.Steps.RemoveAt(0) };
            Reject(normalized with { Region = normalized.Region with { Blocks = normalized.Region.Blocks.SetItem(blockIndex, mutated) } }, "deleted read or effect stage");
            mutated = block with { FinalState = block.FinalState with { Slots = block.FinalState.Slots.Remove(input) } };
            Reject(normalized with { Region = normalized.Region with { Blocks = normalized.Region.Blocks.SetItem(blockIndex, mutated) } }, "lost exit slot");
            mutated = block with { Edges = [] };
            Reject(normalized with { Region = normalized.Region with { Blocks = normalized.Region.Blocks.SetItem(blockIndex, mutated) } }, "closed residual without proof");
        }
        return checks;

        void Require(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        void Reject(NativeNormalizationResult result, string reason) => Require(NativeNormalizationValidator.Validate(result).Count != 0, reason);
    }
}
