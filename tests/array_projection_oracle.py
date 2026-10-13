"""对照 ARM64 与生成 C# 的数组读取、写入和写屏障槽位；只执行有效数组索引。"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_CODE
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_SP, UC_ARM64_REG_X30

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("configuration", type=Path)
parser.add_argument("--tool", type=Path, required=True)
args = parser.parse_args()
config = json.loads(args.configuration.read_text(encoding="utf-8-sig"))
out = ROOT / "artifacts/array-projection"
out.mkdir(parents=True, exist_ok=True)
samples = []


def case(name, kind, instructions, store=False, barrier=False, reject=False):
    element = {"Int32": "int32_t", "Int64": "int64_t", "Object": "Il2CppObject*"}[kind]
    types = [kind + "_array*", "int32_t"] + ([element] if store else [])
    samples.append(dict(Name=name, ReturnType="void" if store else element, Types=types,
                        Names=["array", "index", "value"][:len(types)], Kind=kind,
                        Store=store, Barrier=barrier, Instructions=instructions, Reject=reject))


extend = ["mov x4, #0", "add x4, x4, w1, sxtw"]
for kind, reg, scale, size in (("Int32", "w", 2, 4), ("Int64", "x", 3, 8)):
    variants = {
        "Inline": ([f"add x3, x0, w1, sxtw #{scale}"], 32),
        "Extended": (extend + [f"add x3, x0, x4, lsl #{scale}"], 32),
        "Shifted": (extend + [f"lsl x4, x4, #{scale}", "add x3, x0, x4"], 32),
        "DataFirst": (["add x3, x0, #32"] + extend + [f"add x3, x3, x4, lsl #{scale}"], 0),
        "Multiplied": (extend + [f"mov x5, #{size}", "mul x4, x4, x5", "add x3, x0, x4"], 32),
        "ZeroExtended": (["mov w4, w1", f"add x3, x0, x4, lsl #{scale}"], 32),
        "ElementAddress": (extend + [f"add x3, x0, x4, lsl #{scale}", "add x3, x3, #32"], 0),
        "NextElement": (extend + [f"add x3, x0, x4, lsl #{scale}", "add x3, x3, #32"], size),
        "Biased": (extend + [f"add x3, x0, x4, lsl #{scale}"], 32 + size * 4),
        "DataFirstBiased": ([f"add x3, x0, #{32 + size * 4}"] + extend + [f"add x3, x3, x4, lsl #{scale}"], 0),
    }
    for variant, (address, offset) in variants.items():
        case(kind + variant + "Read", kind, address + [f"ldr {reg}0, [x3, #{offset}]"])
        case(kind + variant + "Write", kind, address + [f"str {reg}2, [x3, #{offset}]"], store=True)
for variant, address in {
    "Extended": extend + ["add x0, x0, x4, lsl #3", "add x0, x0, #32"],
    "DataFirst": ["add x0, x0, #32"] + extend + ["add x0, x0, x4, lsl #3"],
    "NextElement": extend + ["add x0, x0, x4, lsl #3", "add x0, x0, #32", "add x0, x0, #8"],
    "Null": extend + ["add x0, x0, x4, lsl #3", "add x0, x0, #32", "mov x2, #0"],
}.items():
    case("Object" + variant + "Barrier", "Object", ["str x30, [sp, #-16]!"] + address +
         ["str x2, [x0]", "bl .Lwrite_barrier", "ldr x30, [sp], #16"], store=True, barrier=True)
case("Int32LoadedIndexWrite", "Int32", ["ldrsw x4, [x0, #32]", "str w2, [x0, #32]", "add x3, x0, x4, lsl #2", "str w2, [x3, #32]"], store=True)
case("UnknownHigh", "Int64", ["add x3, x0, x1, lsl #3", "ldr x0, [x3, #32]"], reject=True)
case("WrongStride", "Int64", extend + ["add x3, x0, x4, lsl #2", "ldr x0, [x3, #32]"], reject=True)
case("WrappedWordScale", "Int64", ["lsl w4, w1, #3", "add x3, x0, x4", "ldr x0, [x3, #32]"], reject=True)
case("IndexedHeader", "Int64", ["add x3, x0, w1, sxtw #3", "ldr x0, [x3, #24]"], reject=True)
case("PartialElement", "Int64", ["add x3, x0, w1, sxtw #3", "ldr w0, [x3, #32]"], reject=True)
case("MisalignedElement", "Int64", ["add x3, x0, w1, sxtw #3", "ldr x0, [x3, #33]"], reject=True)
case("UnboundAddress", "Int64", ["add x0, x0, w1, sxtw #3"], reject=True)
case("PointerToArray", "Int64", ["add x3, x0, w1, sxtw #3", "ldr x0, [x3, #32]"], reject=True)
samples[-1]["Types"][0] = "Int64_array**"
case("ArrayFieldSlot", "Int64", ["add x3, x0, #0", "add x3, x3, w1, sxtw #3", "ldr x0, [x3, #32]"], reject=True)
samples[-1]["Types"][0] = "ArrayHolder*"

source = ".text\n" + "\n".join(f".global {s['Name']}\n.type {s['Name']}, %function\n{s['Name']}:\n" +
    "\n".join(s["Instructions"] + ["ret"]) + f"\n.size {s['Name']}, .-{s['Name']}" for s in samples)
source += "\n.type fixture_write_barrier, %function\nfixture_write_barrier:\n.Lwrite_barrier:\nret\n"
(out / "cases.s").write_text(source, encoding="utf-8")
subprocess.run([config["Clang"], "-target", "aarch64-linux-gnu", "-c", str(out / "cases.s"), "-o", str(out / "cases.o")], check=True)
with (out / "cases.o").open("rb") as stream:
    elf = ELFFile(stream)
    assert not any(section["sh_type"] in ("SHT_REL", "SHT_RELA") and section["sh_size"] for section in elf.iter_sections()), "unresolved relocation"
    code = elf.get_section_by_name(".text").data()
    symbols = {s.name: s.entry for s in elf.get_section_by_name(".symtab").iter_symbols() if s.entry["st_info"]["type"] == "STT_FUNC"}
for sample in samples:
    symbol = symbols[sample["Name"]]
    sample.update(Offset=symbol["st_value"], Size=symbol["st_size"], Address=0x100000 + symbol["st_value"])
helper = 0x100000 + symbols["fixture_write_barrier"]["st_value"]
(out / "cases.bin").write_bytes(code)
(out / "cases.json").write_text(json.dumps(samples), encoding="utf-8")
(out / "helpers.json").write_text(json.dumps([dict(Address=helper, Kind="WriteBarrier", NoReturn=False)]), encoding="utf-8")
(out / "il2cpp.h").write_text("struct Il2CppObject;\n" + "\n".join(
    f"struct {kind}_array {{ void* klass; void* monitor; void* bounds; uint64_t max_length; {element} m_Items[32]; }};"
    for kind, element in (("Int32", "int32_t"), ("Int64", "int64_t"), ("Object", "Il2CppObject*"))) +
    "\nstruct ArrayHolder { Int64_array* array; };", encoding="utf-8")
(out / "script.json").write_text(json.dumps({"ScriptMethod": [dict(Address=s["Address"], Name="ArrayFixture$$" + s["Name"],
    Signature=s["ReturnType"] + " " + s["Name"] + "(" + ", ".join(t + " " + n for t, n in zip(s["Types"], s["Names"])) + ");") for s in samples]}), encoding="utf-8")
subprocess.run(["dotnet", str(args.tool.resolve()), "native-projection", str(args.configuration.resolve()), str(out)], cwd=ROOT, check=True)

rng = random.Random(19853)
rows = []
for sample in samples:
    if sample["Reject"]:
        continue
    size = 4 if sample["Kind"] == "Int32" else 8
    for index in range(-3 if "Biased" in sample["Name"] else 0, 15):
        for high in (0, 0x7fffffff, 0x80000000, 0xffffffff):
            uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
            uc.mem_map(0x100000, 4096)
            uc.mem_map(0x200000, 4096)
            uc.mem_map(0x300000, 4096)
            uc.mem_write(0x100000, code)
            before = [0x400000 + i * 16 for i in range(32)] if sample["Kind"] == "Object" else [rng.getrandbits(size * 8) for _ in range(32)]
            if "LoadedIndex" in sample["Name"]:
                before[0] = index
            value = 0x400200 if sample["Kind"] == "Object" else rng.getrandbits(size * 8)
            if "Null" in sample["Name"]:
                value = 0
            uc.mem_write(0x300018, (32).to_bytes(8, "little"))
            uc.mem_write(0x300020, b"".join(v.to_bytes(size, "little") for v in before))
            uc.reg_write(UC_ARM64_REG_X0, 0x300000)
            uc.reg_write(UC_ARM64_REG_X0 + 1, (high << 32) | (index & 0xffffffff))
            uc.reg_write(UC_ARM64_REG_X0 + 2, value)
            uc.reg_write(UC_ARM64_REG_SP, 0x200800)
            uc.reg_write(UC_ARM64_REG_X30, 0x100ff0)
            slots = []
            uc.hook_add(UC_HOOK_CODE, lambda cpu, pc, length, _: slots.append(cpu.reg_read(UC_ARM64_REG_X0)) if pc == helper else None)
            uc.emu_start(sample["Address"], 0x100ff0, count=64)
            assert uc.reg_read(UC_ARM64_REG_SP) == 0x200800
            after = [int.from_bytes(uc.mem_read(0x300020 + i * size, size), "little") for i in range(32)]
            rows.append(dict(Name=sample["Name"], Kind=sample["Kind"], Index=index, High=high, Value=value, Before=before, After=after,
                             Expected=0 if sample["Store"] else uc.reg_read(UC_ARM64_REG_X0) & ((1 << (size * 8)) - 1),
                             Slots=[(slot - 0x300020) // size for slot in slots]))
(out / "observations.json").write_text(json.dumps(rows), encoding="utf-8")

arms = []
for sample in samples:
    if sample["Reject"]:
        continue
    kind = sample["Kind"]
    array = {"Int32": "ints", "Int64": "longs", "Object": "objects"}[kind]
    value = {"Int32": "unchecked((int)value)", "Int64": "unchecked((long)value)", "Object": "identities[value]"}[kind]
    call = f"Recovered.{sample['Name']}({array}, index" + (", " + value if sample["Store"] else "") + ")"
    body = call + "; actual = 0;" if sample["Store"] else "actual = unchecked((ulong)" + call + ");"
    arms.append(f'case "{sample["Name"]}": {body} break;')
fixture = '''using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Text.Json;
var rows = JsonSerializer.Deserialize<JsonElement[]>(System.IO.File.ReadAllText(args[0]))!;
foreach (var row in rows)
{
    var name = row.GetProperty("Name").GetString(); var kind = row.GetProperty("Kind").GetString();
    var index = row.GetProperty("Index").GetInt32(); var value = row.GetProperty("Value").GetUInt64();
    var before = row.GetProperty("Before").EnumerateArray().Select(v => v.GetUInt64()).ToArray();
    var expected = row.GetProperty("After").EnumerateArray().Select(v => v.GetUInt64()).ToArray();
    var identities = before.Append(value).Distinct().ToDictionary(v => v, v => v == 0 ? null : new object());
    var reverse = identities.Where(p => p.Key != 0).ToDictionary(p => p.Value, p => p.Key);
    var ints = before.Select(v => unchecked((int)v)).ToArray();
    var longs = before.Select(v => unchecked((long)v)).ToArray();
    var objects = before.Select(v => identities[v]).ToArray();
    Runtime.Array = objects; Runtime.Slots.Clear();
    ulong actual;
    switch (name) { /* ARMS */ default: throw new Exception(name); }
    if (kind == "Int32") actual &= uint.MaxValue;
    if (actual != row.GetProperty("Expected").GetUInt64()) throw new Exception(name + ": return");
    var after = kind == "Int32" ? ints.Select(v => (ulong)unchecked((uint)v)).ToArray() :
        kind == "Int64" ? longs.Select(v => unchecked((ulong)v)).ToArray() : objects.Select(v => v is null ? 0 : reverse[v]).ToArray();
    if (!after.SequenceEqual(expected)) throw new Exception(name + ": array mutation");
    if (!Runtime.Slots.SequenceEqual(row.GetProperty("Slots").EnumerateArray().Select(v => v.GetInt32()))) throw new Exception(name + ": write barrier slot");
}
Console.WriteLine($"PASS: {rows.Length} generated C# / ARM64 array scenarios");
static class Runtime
{
    public static object[] Array = [];
    public static List<int> Slots = [];
    public static void GCWriteBarrier(ref object slot)
    {
        var matches = new List<int>();
        for (var i = 0; i < Array.Length; i++) if (Unsafe.AreSame(ref slot, ref Array[i])) matches.Add(i);
        if (matches.Count != 1) throw new Exception("write barrier does not reference one array slot");
        Slots.Add(matches[0]);
    }
}
'''
(out / "Program.cs").write_text(fixture.replace("/* ARMS */", "\n".join(arms)), encoding="utf-8")
(out / "ArrayFixture.csproj").write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><Nullable>disable</Nullable></PropertyGroup></Project>', encoding="utf-8")
subprocess.run(["dotnet", "restore", str(out / "ArrayFixture.csproj"), "--source", str(ROOT / "artifacts")], cwd=ROOT, check=True)
subprocess.run(["dotnet", "run", "--project", str(out / "ArrayFixture.csproj"), "-c", "Release", "--no-restore", "--", str(out / "observations.json")], cwd=ROOT, check=True)
report = dict(functions=len(samples), rejected=sum(s["Reject"] for s in samples), cases=len(rows),
              barriers=sum(len(row["Slots"]) for row in rows), codeSha256=hashlib.sha256(code).hexdigest(),
              generatedSha256=hashlib.sha256((out / "Recovered.cs").read_bytes()).hexdigest(),
              scope="synthetic ARM64 and actual generated C#; valid array accesses; explicit helper stub; no game runtime claim")
(out / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
print(json.dumps(report))
