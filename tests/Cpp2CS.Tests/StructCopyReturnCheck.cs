using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Tests;

internal static class StructCopyReturnCheck
{
    [Command("struct-copy-return", "结构体尾部复制返回的来源、目标与完整大小边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new MethodRecovery(facts, types);
        var entries = facts.Registrations.Entries.Where(e => e.Kind == EntryKind.GenericMethod && e.Method is { Method.Parameters.Count: 0 }
            && facts.Code.At(e.Address) is { Size: <= 32 } && facts.Helpers.InternalCall(e.Address) is { Kind: HelperKind.Import, Detail: "memcpy" })
            .Where(e => types.Kind(e.Method!.Method.ReturnType.Substitute(e.Method.TypeArguments, e.Method.MethodArguments)) == TypeKind.Struct)
            .DistinctBy(e => e.Method!.Method.Owner.IsValueType).Take(2).ToArray();
        var a = new Assertions();
        a.Equal(2, entries.Length, "覆盖引用与值类型接收者的实际复制入口");
        foreach (var entry in entries)
        {
            var method = entry.Method!;
            a.Equal(0, recovery.RecoverInstance(method, entry.Address).Holes.Count, "完整恢复实际原生入口");
            var context = new RecoveryScope(recovery, method, entry.Address) { ClosedInstance = true };
            a.True(context.Prepare(), "准备实际调用形态");
            a.True(context.Analyze() is null, "实际地址类型分析成功");
            var function = context.function;
            var call = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single(c => c.Op is { Kind: OpKind.Import, Operand: "memcpy" });
            var count = (Const)call.Arguments[2];
            void Check(Call candidate, bool matched, bool failed = false)
            {
                var output = new List<ManagedStatement>();
                var result = context.Lowering.CopyStructReturn(candidate, output);
                a.Equal(!failed, result.TryGet(out var accepted, out _), "地址不明保留恢复失败");
                if (!failed) a.Equal(matched, accepted, "仅完整返回复制被接受");
                a.Equal(matched ? 2 : 0, output.Count, "拒绝时不写出部分结果");
                if (matched) a.True(output is [ManagedAssignment { Value: IndirectValue }, ManagedReturn], "完整值复制后返回");
            }
            Check(call, true);
            Check(call with { Arguments = [call.Arguments[0], call.Arguments[1], Expr.C(count.Value - 1, count.Width)] }, false);
            Check(call with { Arguments = [call.Arguments[0], call.Arguments[1], Expr.C(count.Value + 1, count.Width)] }, false);
            Check(call with { Arguments = [call.Arguments[1], call.Arguments[1], count] }, false);
            Check(call with { Arguments = [call.Arguments[0], call.Arguments[0], count] }, false);
            Check(call with { Arguments = [call.Arguments[0], Expr.C(0x1000, 64), count] }, false, failed: true);
            Check(call with { Kind = CallKind.Direct }, false);
            Check(call with { Op = new(OpKind.Import, "memmove") }, false);
            foreach (var length in new[] { count.Value - 1, count.Value })
            {
                var output = new List<ManagedStatement>();
                var direct = call with { Kind = CallKind.Direct, Arguments = [call.Arguments[0], call.Arguments[1], Expr.C(length, count.Width)] };
                a.True(context.Lowering.CopyStructValue(direct, output).TryGet(out var accepted, out _), "定长复制匹配不产生部分诊断");
                a.Equal(length == count.Value, accepted, "直接复制仍核对完整字段大小");
                if (accepted) a.True(output is [ManagedAssignment], "返回局部直接接收完整值快照");
            }
        }
        return a.Finish("struct-copy-return");
    }
}
