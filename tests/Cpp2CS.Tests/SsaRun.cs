using System.Diagnostics;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Ssa;

namespace Cpp2CS.Tests;

/// <summary>
/// ssa &lt;binary&gt; &lt;metadata&gt; [0x地址 | 命名空间,...]：控制流图 → 寄存器 SSA → 传播与清理，并检查 SSA 不变量。
/// </summary>
internal static class SsaRun
{
    /// <summary>按托管签名给出返回值所在存储；结构体返回尚未区分（待验证），暂按 x0。</summary>
    public static Expr? ReturnValue(MethodDef method, CallingConvention convention) => method.ReturnType.ToString() switch
    {
        "void" => null,
        "float" => new Read(convention.FloatResults[0], 32),
        "double" => new Read(convention.FloatResults[0], 64),
        _ => new Read(convention.IntegerResults[0], 64),
    };

    public static List<string> Lower(MachineFunction function, CallingConvention convention, Expr? returnValue) =>
        Lowering.Registers(function, convention, new ConservativeCallModel(convention), returnValue);

    public static int Run(string binary, string metadata, string? selector)
    {
        var model = ModelCheck.Load(binary, metadata);
        var functions = FunctionTable.Build(model.Image);
        var machine = Corpus.Machine(model.Image);
        var builder = new CfgBuilder(machine, functions);
        var convention = machine.Convention;
        if (selector is not null && selector.StartsWith("0x"))
        {
            var address = System.Convert.ToUInt64(selector[2..], 16);
            var owners = model.Code.TryGetValue(address, out var list) ? list : [];
            foreach (var owner in owners) Console.WriteLine($"// {owner.Method}");
            var function = builder.Build(address);
            var errors = Lower(function, convention, owners.Count > 0 ? ReturnValue(owners[0].Method.Method, convention) : new Read(convention.IntegerResults[0], 64));
            foreach (var error in errors) Console.WriteLine($"// SSA 错误: {error}");
            Console.Write(function);
            return 0;
        }

        var namespaces = selector?.Split(',') ?? Corpus.Default(model.Image.Architecture);
        var methods = Corpus.Select(model, namespaces).GroupBy(m => m.Address).Select(g => g.First()).OrderBy(m => m.Address).ToList();
        var watch = Stopwatch.StartNew();
        int lowered = 0, failed = 0;
        long statements = 0, phis = 0, defines = 0, opaque = 0, unknown = 0, flags = 0, testFlags = 0;
        var samples = new List<string>();
        var unknownReasons = new Dictionary<string, int>();
        foreach (var method in methods)
        {
            if (functions.At(method.Address) is not { } range || range.Start != method.Address) continue;
            var function = builder.Build(method.Address, range);
            var errors = Lower(function, convention, ReturnValue(method, convention));
            lowered++;
            if (errors.Count > 0)
            {
                failed++;
                if (samples.Count < 20) samples.Add($"0x{method.Address:x} {method}: {errors[0]}（共 {errors.Count}）");
            }
            foreach (var stmt in function.Blocks.SelectMany(b => b.Statements))
            {
                statements++;
                switch (stmt)
                {
                    case Phi: phis++; break;
                    case Define: defines++; break;
                    case Opaque: opaque++; break;
                }
                foreach (var e in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk))
                {
                    switch (e)
                    {
                        case Unknown u:
                            unknown++;
                            var reason = u.Reason.Contains("被调用破坏") ? "调用破坏" : u.Reason;
                            unknownReasons[reason] = unknownReasons.GetValueOrDefault(reason) + 1;
                            break;
                        case TestFlags: testFlags++; break;
                        case Flags: flags++; break;
                    }
                }
            }
        }
        Console.WriteLine($"命名空间   {string.Join(",", namespaces)}");
        Console.WriteLine($"函数       {lowered}  SSA 失败 {failed}  用时 {watch.ElapsedMilliseconds} ms");
        Console.WriteLine($"语句       {statements}  φ {phis}  定义 {defines}  不透明 {opaque}");
        Console.WriteLine($"残留       Unknown {unknown}  TestFlags {testFlags}  Flags {flags}");
        foreach (var (reason, count) in unknownReasons.OrderByDescending(p => p.Value).Take(10)) Console.WriteLine($"  Unknown {count,7}  {reason}");
        foreach (var sample in samples) Console.WriteLine("  " + sample);
        return 0;
    }
}
