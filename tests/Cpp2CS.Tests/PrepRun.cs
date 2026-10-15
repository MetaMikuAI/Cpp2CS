using System.Diagnostics;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Runtime;
using Cpp2CS.Ssa;

namespace Cpp2CS.Tests;

/// <summary>
/// prep &lt;binary&gt; &lt;metadata&gt; [0x地址 | 命名空间,...]：寄存器 SSA → 运行时样板整理（Prepare），
/// 单个地址时打印结果，命名空间时统计整理后残留的调用、Unknown 与栈地址。
/// </summary>
internal static class PrepRun
{
    public sealed record Context(ProgramModel Model, FunctionTable Functions, IMachine Machine, CfgBuilder Builder, CallResolver Resolver, ManagedTypes Types, IManagedAbi Abi);

    public static Context Create(ProgramModel model)
    {
        var functions = FunctionTable.Build(model.Image);
        var machine = Corpus.Machine(model.Image);
        var builder = new CfgBuilder(machine, functions);
        var resolver = new CallResolver(model, new RuntimeHelpers(builder), new ManagedCopies(machine, functions, model));
        var types = new ManagedTypes(model, 16);
        return new Context(model, functions, machine, builder, resolver, types, new Arm64ManagedAbi(types));
    }

    /// <summary>构建并整理一个方法；SSA 失败时返回错误。</summary>
    public static (MachineFunction Function, Prepare.Result? Result, List<string> Errors) Build(Context context, MethodDef method, ulong address, FunctionRange? range)
    {
        var convention = context.Machine.Convention;
        var function = range is null ? context.Builder.Build(address) : context.Builder.Build(address, range);
        var errors = SsaRun.Lower(function, convention, SsaRun.ReturnValue(method, convention));
        if (errors.Count > 0) return (function, null, errors);
        var result = new Prepare(context.Resolver, context.Abi, convention).Run(function);
        return (function, result, SsaCheck.Verify(function, Dominators.Compute(function)));
    }

    public static int Run(string binary, string metadata, string? selector)
    {
        var model = ModelCheck.Load(binary, metadata);
        var context = Create(model);
        if (selector is not null && selector.StartsWith("0x"))
        {
            var address = System.Convert.ToUInt64(selector[2..], 16);
            var owners = model.Code.TryGetValue(address, out var list) ? list : [];
            foreach (var owner in owners) Console.WriteLine($"// {owner.Method}");
            var (function, result, errors) = Build(context, owners[0].Method.Method, address, null);
            foreach (var error in errors) Console.WriteLine($"// 错误: {error}");
            if (result is not null) Console.WriteLine($"// 提升栈槽 {result.PromotedSlots}  castclass {string.Join(",", result.Castclass.Select(a => $"0x{a:x}"))}");
            Console.Write(Annotate(context, function));
            return 0;
        }

        var namespaces = selector?.Split(',') ?? Corpus.Default(model.Image.Architecture);
        var methods = Corpus.Select(model, namespaces).GroupBy(m => m.Address).Select(g => g.First()).OrderBy(m => m.Address).ToList();
        var watch = Stopwatch.StartNew();
        int built = 0, failed = 0, landing = 0;
        var calls = new Dictionary<string, int>();
        var unknowns = new Dictionary<string, int>();
        int escapes = 0, frameLoads = 0, blocks = 0, statements = 0;
        var samples = new Dictionary<string, string>();
        foreach (var method in methods)
        {
            if (context.Functions.At(method.Address) is not { } range || range.Start != method.Address) continue;
            var (function, result, errors) = Build(context, method, method.Address, range);
            built++;
            if (errors.Count > 0)
            {
                failed++;
                continue;
            }
            if (function.Blocks.Any(b => b.IsLandingPad)) landing++;
            blocks += function.Blocks.Count;
            foreach (var stmt in function.Blocks.SelectMany(b => b.Statements))
            {
                statements++;
                if (stmt is Call call)
                {
                    var key = call.Kind is CallKind.Indirect or CallKind.TailIndirect ? "间接" : context.Resolver.Resolve(call) switch
                    {
                        HelperCallee h => h.Helper.ToString(),
                        ManagedCallee { Copy: not null } => "托管(副本)",
                        ManagedCallee m => m.Owners.Count == 1 ? "托管" : "托管(多所有者)",
                        _ => "未知",
                    };
                    calls[key] = calls.GetValueOrDefault(key) + 1;
                    samples.TryAdd("调用 " + key, $"0x{method.Address:x}");
                }
                foreach (var e in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk))
                {
                    switch (e)
                    {
                        case Unknown u:
                            var reason = u.Reason.Contains("被调用破坏") ? "调用破坏" : u.Reason.Contains("已删除") ? "已删除" : u.Reason;
                            unknowns[reason] = unknowns.GetValueOrDefault(reason) + 1;
                            samples.TryAdd("Unknown " + reason, $"0x{method.Address:x}");
                            break;
                        case Load { Address: FrameAddress }:
                            frameLoads++;
                            break;
                        case FrameAddress:
                            escapes++;
                            break;
                    }
                }
            }
        }
        Console.WriteLine($"命名空间   {string.Join(",", namespaces)}");
        Console.WriteLine($"函数       {built}  失败 {failed}  有落地块 {landing}  用时 {watch.ElapsedMilliseconds} ms");
        Console.WriteLine($"块         {blocks}  语句 {statements}  栈读 {frameLoads}  栈地址 {escapes}");
        foreach (var (key, count) in calls.OrderByDescending(p => p.Value)) Console.WriteLine($"  调用 {count,7}  {key}  例 {samples["调用 " + key]}");
        foreach (var (key, count) in unknowns.OrderByDescending(p => p.Value).Take(10)) Console.WriteLine($"  Unknown {count,7}  {key}  例 {samples["Unknown " + key]}");
        return 0;
    }

    /// <summary>打印函数，并在调用后注明被调用者。</summary>
    public static string Annotate(Context context, MachineFunction function)
    {
        var text = new System.Text.StringBuilder();
        foreach (var block in function.Blocks)
        {
            text.AppendLine($"{block}{(block.IsLandingPad ? " (落地块)" : "")} <- [{string.Join(", ", block.Predecessors)}]");
            foreach (var stmt in block.Statements)
            {
                var note = stmt is Call call ? context.Resolver.Resolve(call) switch
                {
                    HelperCallee h => $"  ; {h.Helper}",
                    ManagedCallee m => $"  ; {string.Join(" | ", m.Owners.Select(o => o.Method.ToString()).Take(3))}{(m.Copy is null ? "" : " (副本)")}",
                    UnknownCallee => "  ; ?",
                    _ => "",
                } : "";
                text.AppendLine($"    {stmt.Address:x}: {stmt}{note}");
            }
            text.AppendLine($"    -> [{string.Join(", ", block.Successors)}]");
        }
        return text.ToString();
    }
}
