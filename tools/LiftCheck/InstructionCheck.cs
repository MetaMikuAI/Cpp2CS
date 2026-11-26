using Cpp2CS.Snapshot;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.LiftCheck;

/// <summary>对清单中扩展编码的每种实际指令字，在原地址独立执行一步，比较全部寄存器、标志和访存。</summary>
internal static class InstructionCheck
{
    public static void Run(Scan scan, string prefix)
    {
        var image = new Image(scan.Elf, scan.FileBytes);
        using var disassembly = new Disassembly();
        using var rows = new StreamWriter(prefix + ".steps.local.tsv");
        var remaining = new HashSet<uint>();
        foreach (var line in File.ReadLines(prefix + ".words.local.tsv"))
        {
            uint word = uint.Parse(line.AsSpan(0, 8), System.Globalization.NumberStyles.HexNumber);
            if (Decoder.Decode(word).Form >= Form.ConditionalCompare) remaining.Add(word);
        }
        foreach (var entry in scan.Target.Entries)
        {
            if (remaining.Count == 0) break;
            if (scan.Target.Unwind.Find(entry) is not Frame frame) continue;
            for (ulong pc = frame.Start; pc < frame.End; pc += 4)
            {
                uint word = scan.Target.Word(pc);
                if (!remaining.Remove(word)) continue;
                var insn = Decoder.Decode(word);
                foreach (ulong seed in EnvironmentState.Seeds)
                {
                    var builder = new SnapshotBuilder(64);
                    var inputs = new Term[Abi.Count];
                    for (int r = 0; r < inputs.Length; r++)
                    {
                        var bits = r < Abi.Negative ? EnvironmentState.Register(seed, r) :
                            EnvironmentState.Mix(seed) >> (31 - r + Abi.Negative) & 1;
                        inputs[r] = builder.Terms.Bits(bits, Abi.Width(r));
                    }
                    var outputs = scan.Target.EvaluateInstruction(pc, builder, builder.Entry, inputs);
                    builder.Return(builder.Entry);
                    var interpreter = new Interpreter(image, seed, []);
                    var interpreted = interpreter.Run(builder.Build(), new LiftLocations());
                    using var cpu = new NativeRun(image, disassembly, frame, seed, 1, []);
                    var (native, registers) = cpu.Step(pc);
                    if (native.Error == null) native.Add("Return");
                    string? reason = Execution.Compare(native, interpreted, out int first);
                    string? detail = reason == null ? null : $"{first}: {native.Events.ElementAtOrDefault(first)} / {interpreted.Events.ElementAtOrDefault(first)}";
                    for (int r = 0; r < outputs.Length && reason == null; r++)
                    {
                        var value = interpreter.Result(outputs[r]);
                        if (value.Undefined == 0 && value.Value == registers[r]) continue;
                        reason = "寄存器不符"; detail = $"{r}: {registers[r]:x} / {value.Value:x}";
                    }
                    rows.WriteLine($"{word:x8}\t{pc:x}\t{insn.Extension}\t{seed}\t{reason ?? "通过"}\t{detail}");
                }
            }
        }
        if (remaining.Count != 0) throw new InvalidDataException("指令字清单与 FDE 不一致");
    }
}
