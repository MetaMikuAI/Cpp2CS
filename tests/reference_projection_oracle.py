"""对照 ARM64 与生成 C# 的引用合流、空值和循环边复制，检查对象身份。"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_SP, UC_ARM64_REG_X30, UC_ARM64_REG_PC

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("configuration", type=Path)
parser.add_argument("--tool", type=Path, required=True)
args = parser.parse_args()
config = json.loads(args.configuration.read_text(encoding="utf-8-sig"))
out = ROOT / "artifacts/reference-projection"
out.mkdir(parents=True, exist_ok=True)
samples = []


def case(name, kind, instructions, reject=False, right=None):
    samples.append(dict(Name=name, ReturnType=kind, Types=[kind, right or kind, "int32_t"], Names=["left", "right", "count"], Instructions=instructions, Reject=reject))


for kind, prefix in (("Il2CppObject*", "Object"), ("System_String_o*", "String")):
    case(prefix + "Join", kind, ["cbz w2, 1f", "mov x0, x1", "1:"])
    case(prefix + "NullJoin", kind, ["cbz w2, 1f", "mov x0, xzr", "1:"])
    case(prefix + "ReverseNullJoin", kind, ["cbz w2, 1f", "b 2f", "1: mov x0, xzr", "2:"])
    case(prefix + "Nested", kind, ["cbz w2, 1f", "mov x3, x1", "b 2f", "1: mov x3, xzr", "2: cbz x3, 3f", "mov x0, x3", "3:"])
    case(prefix + "SelectNull", kind, ["cmp w2, #0", "csel x0, x0, xzr, eq"])
    case(prefix + "AllNull", kind, ["cbz w2, 1f", "mov x0, xzr", "b 2f", "1: mov x0, #0", "2:"])
    case(prefix + "LoopSwap", kind, ["mov w2, w2", "b 2f", "1: mov x3, x0", "mov x0, x1", "mov x1, x3", "sub w2, w2, #1", "2: cbnz w2, 1b"])
    case(prefix + "LoopNull", kind, ["mov w2, w2", "b 2f", "1: mov x0, xzr", "sub w2, w2, #1", "2: cbnz w2, 1b"])
case("ObjectStringJoin", "Il2CppObject*", ["cbz w2, 1f", "mov x0, x1", "1:"], right="System_String_o*")
case("ObjectStringSelect", "Il2CppObject*", ["cmp w2, #0", "csel x0, x0, x1, eq"], right="System_String_o*")
case("UnrelatedJoin", "System_String_o*", ["cbz w2, 1f", "mov x0, x1", "1:"], True, "Int32_array*")
case("IntegerJoin", "Il2CppObject*", ["cbz w2, 1f", "mov x0, x1", "1:"], True, "int64_t")
case("NonzeroJoin", "Il2CppObject*", ["cbz w2, 1f", "mov x0, #1", "1:"], True)
case("UndefinedWordJoin", "Il2CppObject*", ["cbz w2, 1f", "mov x0, x1", "1:"], True, "int32_t")
case("TruncatedNullJoin", "Il2CppObject*", ["cbz w2, 1f", "mov w0, w0", "b 2f", "1: mov x0, xzr", "2:"], True)
case("TruncatedSelect", "Il2CppObject*", ["mov w0, w0", "cmp w2, #0", "csel x0, x0, x1, eq"], True)
case("TruncatedReturn", "Il2CppObject*", ["mov w0, w0"], True)

source = ".text\n" + "\n".join(f".global {s['Name']}\n.type {s['Name']}, %function\n{s['Name']}:\n" +
    "\n".join(s["Instructions"] + ["ret"]) + f"\n.size {s['Name']}, .-{s['Name']}" for s in samples)
(out / "cases.s").write_text(source, encoding="utf-8")
subprocess.run([config["Clang"], "-target", "aarch64-linux-gnu", "-c", str(out / "cases.s"), "-o", str(out / "cases.o")], check=True)
with (out / "cases.o").open("rb") as stream:
    elf = ELFFile(stream)
    assert not any(section["sh_type"] in ("SHT_REL", "SHT_RELA") and section["sh_size"] for section in elf.iter_sections())
    code = elf.get_section_by_name(".text").data()
    symbols = {s.name: s.entry for s in elf.get_section_by_name(".symtab").iter_symbols() if s.entry["st_info"]["type"] == "STT_FUNC"}
for sample in samples:
    symbol = symbols[sample["Name"]]
    sample.update(Offset=symbol["st_value"], Size=symbol["st_size"], Address=0x100000 + symbol["st_value"])
(out / "cases.bin").write_bytes(code)
(out / "cases.json").write_text(json.dumps(samples), encoding="utf-8")
(out / "il2cpp.h").write_text("struct Il2CppObject; struct System_String_o; struct Int32_array;", encoding="utf-8")
(out / "script.json").write_text(json.dumps({"ScriptMethod": [dict(Address=s["Address"], Name="ReferenceFixture$$" + s["Name"],
    Signature=s["ReturnType"] + " " + s["Name"] + "(" + ", ".join(t + " " + n for t, n in zip(s["Types"], s["Names"])) + ");") for s in samples]}), encoding="utf-8")
subprocess.run(["dotnet", str(args.tool.resolve()), "native-projection", str(args.configuration.resolve()), str(out)], cwd=ROOT, check=True)

rows = []
for sample in samples:
    if sample["Reject"]:
        continue
    for left in (0, 0x300000, 0x300010):
        for right in (0, 0x300000, 0x300010):
            for count in (0, 1, 2, 3, 4, 7, 16):
                for high in (0, 0xffffffff):
                    uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
                    uc.mem_map(0x100000, 4096)
                    uc.mem_write(0x100000, code)
                    uc.reg_write(UC_ARM64_REG_X0, left)
                    uc.reg_write(UC_ARM64_REG_X0 + 1, right)
                    uc.reg_write(UC_ARM64_REG_X0 + 2, (high << 32) | count)
                    uc.reg_write(UC_ARM64_REG_SP, 0x200800)
                    uc.reg_write(UC_ARM64_REG_X30, 0x100ff0)
                    uc.emu_start(sample["Address"], 0x100ff0, count=512)
                    assert uc.reg_read(UC_ARM64_REG_PC) == 0x100ff0, sample["Name"] + ": execution did not return"
                    assert uc.reg_read(UC_ARM64_REG_X30) == 0x100ff0
                    rows.append(dict(Name=sample["Name"], Left=left, Right=right, Count=count, High=high, Expected=uc.reg_read(UC_ARM64_REG_X0)))
(out / "observations.json").write_text(json.dumps(rows), encoding="utf-8")
arms = []
for sample in samples:
    if sample["Reject"]:
        continue
    arguments = [f"(string){name}" if kind == "System_String_o*" else name for kind, name in zip(sample["Types"], sample["Names"])]
    arms.append(f'"{sample["Name"]}" => Recovered.{sample["Name"]}(' + ", ".join(arguments) + ")")
fixture = '''using System;
using System.Collections.Generic;
using System.Text.Json;
var rows = JsonSerializer.Deserialize<JsonElement[]>(System.IO.File.ReadAllText(args[0]))!;
var identities = new Dictionary<ulong, string> { [0] = null, [0x300000] = new string('x', 3), [0x300010] = new string('x', 3) };
if (ReferenceEquals(identities[0x300000], identities[0x300010])) throw new Exception("distinct string identities required");
foreach (var row in rows)
{
    object left = identities[row.GetProperty("Left").GetUInt64()], right = identities[row.GetProperty("Right").GetUInt64()];
    var count = row.GetProperty("Count").GetInt32(); var name = row.GetProperty("Name").GetString();
    object actual = name switch { /* ARMS */, _ => throw new Exception(name) };
    if (!ReferenceEquals(actual, identities[row.GetProperty("Expected").GetUInt64()])) throw new Exception(name + ": reference identity");
}
Console.WriteLine($"PASS: {rows.Length} generated C# / ARM64 reference scenarios");
'''
(out / "Program.cs").write_text(fixture.replace("/* ARMS */", ",\n".join(arms)), encoding="utf-8")
(out / "ReferenceFixture.csproj").write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><Nullable>disable</Nullable></PropertyGroup></Project>', encoding="utf-8")
subprocess.run(["dotnet", "restore", str(out / "ReferenceFixture.csproj"), "--source", str(ROOT / "artifacts")], cwd=ROOT, check=True)
subprocess.run(["dotnet", "run", "--project", str(out / "ReferenceFixture.csproj"), "-c", "Release", "--no-restore", "--", str(out / "observations.json")], cwd=ROOT, check=True)
report = dict(functions=len(samples), rejected=sum(s["Reject"] for s in samples), cases=len(rows),
              codeSha256=hashlib.sha256(code).hexdigest(), generatedSha256=hashlib.sha256((out / "Recovered.cs").read_bytes()).hexdigest(),
              scope="synthetic ARM64 and actual generated C#; reference identity, nulls and bounded loop scenarios; no game runtime claim")
(out / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
print(json.dumps(report))
