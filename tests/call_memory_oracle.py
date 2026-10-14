"""检查调用后的栈值：未知写入必须拒绝，已确认的返回缓冲与值快照对照 ARM64。"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_CODE
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_SP, UC_ARM64_REG_X30, UC_ARM64_REG_PC

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("configuration", type=Path)
parser.add_argument("--tool", type=Path, required=True)
args = parser.parse_args()
config = json.loads(args.configuration.read_text(encoding="utf-8-sig"))
out = ROOT / "artifacts/call-memory"
out.mkdir(parents=True, exist_ok=True)
samples = []


def case(name, body, reject=False):
    samples.append(dict(Name=name, ReturnType="int32_t", Types=["int32_t"], Names=["value"],
                        Instructions=["sub sp, sp, #128", "stp x30, x19, [sp, #112]"] + body +
                        ["ldp x30, x19, [sp, #112]", "add sp, sp, #128", "ret"], Reject=reject))


for offset in (0, 12, 32, 60):
    seed = [f"str w0, [sp, #{offset}]"]
    pointer = [f"add x0, sp, #{offset}", "mov x1, xzr"]
    load = [f"ldr w0, [sp, #{offset}]"]
    case(f"WriteThroughPointer{offset}", seed + pointer + ["bl .Lmutate"] + load, True)
    case(f"PointerReloaded{offset}", seed + pointer + ["str x0, [sp, #104]", "ldr x0, [sp, #104]", "bl .Lmutate"] + load, True)
    case(f"LaterCallAfterEscape{offset}", seed + pointer + ["bl .Lretain", "mov w0, #7", f"str w0, [sp, #{offset}]", "bl .Luse_retained"] + load, True)
    case(f"OverwrittenAfterCall{offset}", seed + pointer + ["bl .Lmutate", "mov w0, #13", f"str w0, [sp, #{offset}]"] + load)
    case(f"RegisterSnapshot{offset}", seed + [f"ldr w19, [sp, #{offset}]"] + pointer + ["bl .Lmutate", "mov w0, w19"])
    case(f"NoStackArgument{offset}", seed + ["bl .Lobserve"] + load)
    case(f"IndirectReturn{offset}", [f"add x8, sp, #{offset}", "mov x1, xzr", "bl .Lproduce"] + load)
    case(f"ReturnBufferAndOtherPointer{offset}", seed + [f"add x0, sp, #{offset}", "add x8, sp, #40", "mov x1, xzr", "bl .Lproduce_and_mutate"] + load, True)
case("EscapeOnOneBranch", ["str w0, [sp]", "cbz w0, .Lmerged", "add x0, sp, #0", "mov x1, xzr", "bl .Lretain",
     ".Lmerged:", "mov w0, #7", "str w0, [sp]", "bl .Lobserve", "ldr w0, [sp]"], True)
case("SeparateReturnBuffer", ["str w0, [sp]", "add x8, sp, #40", "mov x1, xzr", "bl .Lproduce", "ldr w0, [sp]"])
case("ReturnSnapshot", ["add x8, sp, #40", "mov x1, xzr", "bl .Lproduce", "ldr w19, [sp, #40]", "mov w0, #17",
     "add x8, sp, #40", "mov x1, xzr", "bl .Lproduce", "mov w0, w19"])

source = ".text\n" + "\n".join(f".global {s['Name']}\n.type {s['Name']}, %function\n{s['Name']}:\n" +
    "\n".join(s["Instructions"]) + f"\n.size {s['Name']}, .-{s['Name']}" for s in samples)
source += """
.type Mutate, %function
Mutate:
.Lmutate:
mov w9, #29
str w9, [x0]
ret
.type Retain, %function
Retain:
.Lretain:
mov x9, #0x300000
str x0, [x9]
ret
.type UseRetained, %function
UseRetained:
.Luse_retained:
mov x9, #0x300000
ldr x9, [x9]
mov w10, #31
str w10, [x9]
ret
.type Observe, %function
Observe:
.Lobserve:
ret
.type Produce, %function
Produce:
.Lproduce:
str w0, [x8]
str wzr, [x8, #4]
stp xzr, xzr, [x8, #8]
ret
.type ProduceAndMutate, %function
ProduceAndMutate:
.Lproduce_and_mutate:
mov w9, #37
str w9, [x0]
stp xzr, xzr, [x8]
str xzr, [x8, #16]
ret
"""
(out / "cases.s").write_text(source, encoding="utf-8")
subprocess.run([config["Clang"], "-target", "aarch64-linux-gnu", "-c", str(out / "cases.s"), "-o", str(out / "cases.o")], check=True)
with (out / "cases.o").open("rb") as stream:
    elf = ELFFile(stream)
    assert not any(s["sh_type"] in ("SHT_REL", "SHT_RELA") and s["sh_size"] for s in elf.iter_sections())
    code = elf.get_section_by_name(".text").data()
    symbols = {s.name: s.entry for s in elf.get_section_by_name(".symtab").iter_symbols() if s.entry["st_info"]["type"] == "STT_FUNC"}
for sample in samples:
    symbol = symbols[sample["Name"]]
    sample.update(Offset=symbol["st_value"], Size=symbol["st_size"], Address=0x100000 + symbol["st_value"])
methods = [dict(Address=s["Address"], Name="CallFixture$$" + s["Name"], Signature="int32_t " + s["Name"] + "(int32_t value);") for s in samples]
for name, result, parameters in (("Mutate", "void", "int32_t* slot, const MethodInfo* method"),
                                 ("Retain", "void", "int32_t* slot, const MethodInfo* method"),
                                 ("UseRetained", "void", ""), ("Observe", "void", ""),
                                 ("Produce", "Payload", "int32_t value, const MethodInfo* method"),
                                 ("ProduceAndMutate", "Payload", "int32_t* slot, const MethodInfo* method")):
    methods.append(dict(Address=0x100000 + symbols[name]["st_value"], Name="CallFixture$$" + name,
                        Signature=f"{result} {name}({parameters});"))
(out / "cases.bin").write_bytes(code)
(out / "cases.json").write_text(json.dumps(samples), encoding="utf-8")
(out / "script.json").write_text(json.dumps({"ScriptMethod": methods}), encoding="utf-8")
(out / "il2cpp.h").write_text("struct MethodInfo;\nstruct Payload { int32_t first; int32_t second; int64_t third; int64_t fourth; };\n", encoding="utf-8")

rng = random.Random(24671)
rows = []
callees = {0x100000 + symbols[name]["st_value"]: name for name in ("Mutate", "Observe", "Produce")}
for sample in samples:
    for value in [0, 1, 13, 29, 0x7fffffff, 0x80000000, 0xffffffff] + [rng.getrandbits(32) for _ in range(32)]:
        uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
        uc.mem_map(0x100000, 0x10000)
        uc.mem_map(0x200000, 4096)
        uc.mem_map(0x300000, 4096)
        uc.mem_write(0x100000, code)
        uc.reg_write(UC_ARM64_REG_X0, (rng.getrandbits(32) << 32) | value)
        uc.reg_write(UC_ARM64_REG_SP, 0x200800)
        uc.reg_write(UC_ARM64_REG_X30, 0x10fff0)
        calls = []
        def observe(cpu, pc, size, _):
            if pc not in callees:
                return
            name = callees[pc]
            argument = cpu.reg_read(UC_ARM64_REG_X0)
            calls.append(name + (":" + str(argument - 0x200800) if name == "Mutate" else
                                ":" + str(argument & 0xffffffff) if name == "Produce" else ""))
        uc.hook_add(UC_HOOK_CODE, observe)
        uc.emu_start(sample["Address"], 0x10fff0, count=128)
        assert uc.reg_read(UC_ARM64_REG_PC) == 0x10fff0
        assert uc.reg_read(UC_ARM64_REG_SP) == 0x200800
        rows.append(dict(Name=sample["Name"], Value=value, Expected=uc.reg_read(UC_ARM64_REG_X0) & 0xffffffff, Reject=sample["Reject"], Calls=calls))
(out / "observations.json").write_text(json.dumps(rows), encoding="utf-8")
subprocess.run(["dotnet", str(args.tool.resolve()), "native-projection", str(args.configuration.resolve()), str(out)], cwd=ROOT, check=True)

arms = [f'"{s["Name"]}" => Recovered.{s["Name"]}(value),' for s in samples if not s["Reject"]]
fixture = """using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.Json;
var rows = JsonSerializer.Deserialize<JsonElement[]>(System.IO.File.ReadAllText(args[0]))!;
var count = 0;
foreach (var row in rows)
{
    if (row.GetProperty("Reject").GetBoolean()) continue;
    Runtime.Calls.Clear(); Runtime.Writes.Clear();
    var value = unchecked((int)row.GetProperty("Value").GetUInt32());
    var actual = row.GetProperty("Name").GetString() switch { /* ARMS */ _ => throw new Exception() };
    if (unchecked((uint)actual) != row.GetProperty("Expected").GetUInt32()) throw new Exception(row.ToString());
    if (!Runtime.Calls.SequenceEqual(row.GetProperty("Calls").EnumerateArray().Select(c => c.GetString()))) throw new Exception("call order or arguments: " + row);
    count++;
}
Console.WriteLine($"PASS: {count} generated C# / ARM64 call-memory scenarios");
public struct Payload { public int first, second; public long third, fourth; }
public static class CallFixture
{
    public static void Observe() => Runtime.Calls.Add("Observe");
    public static void Mutate(long address) { Runtime.Calls.Add("Mutate:" + address); Runtime.Writes[address] = 29; }
    public static Payload Produce(int value) { Runtime.Calls.Add("Produce:" + unchecked((uint)value)); return new() { first = value }; }
}
public static class Runtime
{
    public static List<string> Calls = [];
    public static Dictionary<long, int> Writes = [];
    public static long StackAddress(long offset) => offset;
}
""".replace("/* ARMS */", "\n".join(arms))
(out / "Program.cs").write_text(fixture, encoding="utf-8")
(out / "Fixture.csproj").write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><TreatWarningsAsErrors>true</TreatWarningsAsErrors></PropertyGroup></Project>', encoding="utf-8")
subprocess.run(["dotnet", "run", "--project", str(out / "Fixture.csproj"), "-c", "Release", "--", str(out / "observations.json")], cwd=ROOT, check=True)
report = dict(functions=len(samples), accepted=sum(not s["Reject"] for s in samples), rejected=sum(s["Reject"] for s in samples),
              nativeScenarios=len(rows), compiledScenarios=sum(not r["Reject"] for r in rows),
              codeSha256=hashlib.sha256(code).hexdigest(), sourceSha256=hashlib.sha256((out / "Recovered.cs").read_bytes()).hexdigest())
(out / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
print(json.dumps(report))
