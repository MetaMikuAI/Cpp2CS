using System.Text.Json;
using Cpp2CS.Arm64;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

/// <summary>
/// ARM64 单指令差分测试：读取 tests/oracle/arm64_oracle.py 的输出，
/// 用同一 seed 构造初始状态，执行提升后的 IR，与 Unicorn 的结果逐项比较。
/// </summary>
internal static class Arm64Oracle
{
    private static ulong Mix(ulong x)
    {
        var z = x + 0x9E3779B97F4A7C15UL;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
        return z ^ (z >> 31);
    }

    private static Evaluator Initial(ulong seed)
    {
        var evaluator = new Evaluator();
        var basis = seed * 64;
        var narrow = (seed & 1) != 0;
        for (var i = 0; i < 31; i++)
        {
            var value = Mix(basis + (ulong)i);
            if (narrow) value &= (1UL << 47) - 1;
            evaluator.Registers[Storage.Gpr(i)] = value;
        }
        var sp = Mix(basis + 31) & ~0xFUL;
        if (narrow) sp &= (1UL << 47) - 1;
        evaluator.Registers[Storage.Gpr(Arm64Lifter.Sp)] = sp;
        for (var i = 0; i < 32; i++)
            evaluator.Registers[Storage.Vec(i)] = ((UInt128)Mix(basis + 64 + (ulong)i) << 64) | Mix(basis + 32 + (ulong)i);
        evaluator.Nzcv = (int)(Mix(basis + 63) & 0xF);
        return evaluator;
    }

    [Command("arm64-oracle", "提升器逐指令差分（参照为 Unicorn，输入由 tests/oracle 生成）", Arguments = "<oracle.jsonl>...")]
    private static int CommandLine(string[] files) => files.Length > 0 ? Run(files, 4) : Commands.Usage();

    public static int Run(string[] files, int examples)
    {
        var outcome = new Dictionary<string, int>();
        var byMnemonic = new Dictionary<string, Tally>();
        void Count(string key) => outcome[key] = outcome.GetValueOrDefault(key) + 1;

        foreach (var file in files)
        foreach (var line in File.ReadLines(file))
        {
            using var document = JsonDocument.Parse(line);
            var root = document.RootElement;
            var pc = root.GetProperty("pc").GetUInt64();
            var word = root.GetProperty("word").GetUInt32();
            var seed = root.GetProperty("seed").GetUInt64();
            var asm = root.GetProperty("asm").GetString()!;
            var mnemonic = asm.Split(' ')[0];
            if (!byMnemonic.TryGetValue(mnemonic, out var entry)) byMnemonic.Add(mnemonic, entry = new Tally());

            var statements = new List<Stmt>();
            Arm64Lifter.Lift(pc, word, statements);
            if (statements.OfType<Opaque>().FirstOrDefault() is { } opaque)
            {
                Count("opaque:" + opaque.Text.Split(' ')[0]);
                entry.Opaque++;
                if (entry.Examples.Count < examples && !entry.Examples.Any(e => e.EndsWith(opaque.Text.Split(' ')[0])))
                    entry.Examples.Add($"opaque {word:x8} `{asm}` {opaque.Text.Split(' ')[0]}");
                continue;
            }
            if (statements.OfType<Trap>().Any()) { Count("trap"); continue; }
            if (root.GetProperty("status").GetString() != "ok") { Count("oracle-fault"); continue; }

            var evaluator = Initial(seed);
            for (var i = 0; i < 4; i++) evaluator.Written[pc + (ulong)i] = (byte)(word >> (i * 8));
            evaluator.Run(statements, pc, pc + 4);
            if (evaluator.Failure is not null) { Count("unevaluable:" + evaluator.Failure); continue; }

            var problems = Compare(evaluator, root, pc, word);
            if (problems.Count == 0)
            {
                Count("pass");
                entry.Pass++;
            }
            else
            {
                Count("fail");
                entry.Fail++;
                if (entry.Examples.Count < examples)
                    entry.Examples.Add($"0x{pc:x} {word:x8} seed {seed} `{asm}`: {string.Join("; ", problems)}  IR: {string.Join(" | ", statements)}");
            }
        }

        foreach (var (key, value) in outcome.OrderByDescending(p => p.Value)) Console.WriteLine($"{key,-40} {value}");
        Console.WriteLine();
        foreach (var (mnemonic, entry) in byMnemonic.Where(p => p.Value.Fail > 0 || p.Value.Opaque > 0).OrderByDescending(p => p.Value.Fail + p.Value.Opaque))
        {
            Console.WriteLine($"{mnemonic,-10} pass {entry.Pass} fail {entry.Fail} opaque {entry.Opaque}");
            foreach (var example in entry.Examples) Console.WriteLine("    " + example);
        }
        return outcome.GetValueOrDefault("fail") == 0 ? 0 : 1;
    }

    private sealed class Tally
    {
        public int Pass, Fail, Opaque;
        public readonly List<string> Examples = [];
    }

    private static List<string> Compare(Evaluator evaluator, JsonElement root, ulong pc, uint word)
    {
        var problems = new List<string>();
        var x = root.GetProperty("x").EnumerateArray().Select(e => ulong.Parse(e.GetString()!)).ToArray();
        for (var i = 0; i < 31; i++)
        {
            var actual = (ulong)evaluator.Get(Storage.Gpr(i));
            if (actual != x[i]) problems.Add($"x{i} ir=0x{actual:x} hw=0x{x[i]:x}");
        }
        var sp = ulong.Parse(root.GetProperty("sp").GetString()!);
        var irSp = (ulong)evaluator.Get(Storage.Gpr(Arm64Lifter.Sp));
        if (irSp != sp) problems.Add($"sp ir=0x{irSp:x} hw=0x{sp:x}");
        var q = root.GetProperty("q").EnumerateArray().Select(e => UInt128.Parse(e.GetString()!)).ToArray();
        for (var i = 0; i < 32; i++)
        {
            var actual = evaluator.Get(Storage.Vec(i));
            if (actual != q[i]) problems.Add($"q{i} ir=0x{actual:x} hw=0x{q[i]:x}");
        }
        var nzcv = root.GetProperty("nzcv").GetInt32();
        if (evaluator.Nzcv != nzcv) problems.Add($"nzcv ir={evaluator.Nzcv?.ToString() ?? "?"} hw={nzcv}");
        var next = root.GetProperty("next").GetUInt64();
        if (evaluator.NextPc != next) problems.Add($"pc ir=0x{evaluator.NextPc:x} hw=0x{next:x}");

        var expected = new Dictionary<ulong, byte>();
        foreach (var write in root.GetProperty("writes").EnumerateArray())
        {
            var address = ulong.Parse(write[0].GetString()!);
            var size = write[1].GetInt32();
            var value = UInt128.Parse(write[2].GetString()!);
            for (var i = 0; i < size; i++) expected[address + (ulong)i] = (byte)(value >> (i * 8));
        }
        foreach (var (address, value) in evaluator.Written)
        {
            if (address >= pc && address < pc + 4) continue;
            if (!expected.Remove(address, out var hw)) problems.Add($"extra write 0x{address:x}");
            else if (hw != value) problems.Add($"mem 0x{address:x} ir={value:x2} hw={hw:x2}");
        }
        foreach (var address in expected.Keys.Take(2)) problems.Add($"missing write 0x{address:x}");
        return problems;
    }
}
