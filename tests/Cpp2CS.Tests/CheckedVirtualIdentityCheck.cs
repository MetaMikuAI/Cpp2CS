using System.Reflection;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class CheckedVirtualIdentityCheck
{
    [Command("checked-virtual-identity", "强制转换后虚表接收者身份及失败分支边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var recovery = new MethodRecovery(facts, new ManagedTypes(facts.Model, facts.Layouts));
        var method = MethodRef.Open(facts.Model.Methods.Single(m => m.Owner.FullName == "Sekai.VirtualLiveSelectView" && m.Name == "OnInstantiate"));
        var a = new Assertions();
        foreach (var mode in new[] { "checked", "missing", "inverted", "other-flag", "other-exception" })
        {
            var context = new RecoveryScope(recovery, method, method.Method.Address);
            a.True(context.Prepare(), "准备实际强制转换入口");
            a.True(context.Analyze() is null, "恢复分析成功");
            var function = context.function;
            var call = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single(c => c.Op?.Kind == OpKind.CallVirtual);
            var entry = ((Use)call.Target).Variable;
            var block = function.Blocks.Single(b => b.Statements.OfType<Call>().Any(c => c.Op?.Kind == OpKind.ThrowIf));
            var at = block.Statements.FindIndex(s => s is Call { Op.Kind: OpKind.ThrowIf });
            var guard = (Call)block.Statements[at];
            var condition = (Compare)guard.Arguments.Single();
            block.Statements[at] = mode switch
            {
                "missing" => new Nop(guard.Address, "removed guard"),
                "inverted" => guard with { Arguments = [condition with { Cond = Cond.Ne }] },
                "other-flag" => guard with { Arguments = [condition with { Left = new Use(new(Storage.Temp(999), 1), 64) }] },
                "other-exception" => guard with { Op = new(OpKind.ThrowIf, "System.Exception") },
                _ => guard,
            };
            var runtime = context.State.Runtime.runtime;
            runtime.Clear();
            context.MarkVtableLoads();
            a.Equal(mode == "checked", runtime.Contains(entry), "仅同一对象的成功类型检查证明虚表身份：" + mode);
        }
        return a.Finish("checked-virtual-identity");
    }
}
