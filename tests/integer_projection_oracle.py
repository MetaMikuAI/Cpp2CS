"""组装通用整数函数，对照真实 ARM64 与恢复后编译执行的 C#。"""
import argparse
import hashlib
import json
from pathlib import Path
import random
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
out = ROOT / "artifacts/integer-projection"
out.mkdir(parents=True, exist_ok=True)
samples = []


def case(name, result, types, instructions, reject=False):
    samples.append(dict(Name=name, ReturnType=result, Types=types, Names=list("abc")[:len(types)],
                        Instructions=instructions, Reject=reject))


for width, reg in ((32, "w"), (64, "x")):
    kind = f"int{width}_t"
    for shift in (0, 1, width // 2, width - 1):
        for op in ("lsl", "lsr", "asr"):
            case(f"{op}{width}_{shift}", kind, [kind], [f"{op} {reg}0, {reg}0, #{shift}"])
    for op in ("and", "orr", "eor"):
        case(f"{op}{width}", kind, [kind, kind], [f"{op} {reg}0, {reg}0, {reg}1"])
    for op in ("mul", "mneg"):
        case(f"{op}{width}", kind, [kind, kind], [f"{op} {reg}0, {reg}0, {reg}1"])
    for op in ("madd", "msub"):
        case(f"{op}{width}", kind, [kind, kind, kind], [f"{op} {reg}0, {reg}0, {reg}1, {reg}2"])
    case(f"multiplyOverlap{width}", kind, [kind, kind], [f"msub {reg}1, {reg}0, {reg}1, {reg}1", f"mov {reg}0, {reg}1"])
    for suffix in ("b", "h", "w"):
        case(f"extend{suffix}{width}", kind, ["int32_t"], [f"mov {reg}1, #0", f"add {reg}0, {reg}1, w0, sxt{suffix}"])
    for lsb, count in [(0, 1), (0, 3), (0, width), (1, 7), (5, 11), (width // 2, width // 2), (width - 1, 1)]:
        for op in ('ubfx', 'sbfx', 'ubfiz', 'sbfiz'):
            case(f'{op}{width}_{lsb}_{count}', kind, [kind], [f'{op} {reg}0, {reg}0, #{lsb}, #{count}'])
        for op in ('bfi', 'bfxil'):
            case(f'{op}{width}_{lsb}_{count}', kind, [kind, kind], [f'{op} {reg}0, {reg}1, #{lsb}, #{count}'])
        case(f'bfc{width}_{lsb}_{count}', kind, [kind], [f'bfc {reg}0, #{lsb}, #{count}'])
    case(f'insertOverlap{width}', kind, [kind], [f'bfi {reg}0, {reg}0, #7, #13'])
    case(f'neg{width}', kind, [kind], [f'neg {reg}0, {reg}0'])
    case(f'negShift{width}', kind, [kind], [f'neg {reg}0, {reg}0, lsl #3'])
    case(f'negs{width}', 'int32_t', [kind], [f'negs {reg}1, {reg}0', 'cset w0, eq'])
    case(f'extractConstant{width}', kind, [], [f'mov {reg}0, #-1', f'ubfx {reg}0, {reg}0, #4, #3'])
    for size, suffix in [(8, 'b'), (16, 'h')]:
        for signed in ['int', 'uint']:
            source_type = f'{signed}{size}_t'
            case(f'sxt{suffix}{width}_{signed}', kind, [source_type], [f'sxt{suffix} {reg}0, w0'])
            case(f'narrowExtract{size}_{width}_{signed}', kind, [source_type], [f'ubfx {reg}0, {reg}0, #2, #3'])
            case(f'narrowSignedExtract{size}_{width}_{signed}', kind, [source_type], [f'sbfx {reg}0, {reg}0, #2, #3'])
    case(f'undefinedExtract{width}', kind, ['uint8_t'], [f'ubfx {reg}0, {reg}0, #7, #2'], True)
    case(f'referenceExtract{width}', kind, ['Il2CppObject*'], [f'ubfx {reg}0, {reg}0, #3, #5'], True)
case('sxtw', 'int64_t', ['uint32_t'], ['sxtw x0, w0'])
case('uxtb', 'int32_t', ['int32_t'], ['uxtb w0, w0'])
case('uxth', 'int32_t', ['int32_t'], ['uxth w0, w0'])
case("signedCompare", "int32_t", ["uint32_t", "uint32_t"], ["cmp w0, w1", "cset w0, lt"])
case("unsignedCompare", "int32_t", ["int64_t", "int64_t"], ["cmp x0, x1", "cset w0, hi"])
case("truncate", "int32_t", ["int64_t"], [])
case("zeroExtendedReturn", "int64_t", ["int32_t"], ["mov w0, w0"])
case("zeroExtendedShift", "int64_t", ["int32_t"], ["mov w0, w0", "lsl x0, x0, #17"])
case("zeroExtendedAdd", "int64_t", ["int32_t", "int64_t"], ["mov w0, w0", "add x0, x0, x1"])
case("zeroExtendedMultiply", "int64_t", ["int32_t", "int64_t"], ["mov w0, w0", "mul x0, x0, x1"])
case("zeroExtendedEqual", "int32_t", ["int32_t", "int64_t"], ["mov w0, w0", "cmp x0, x1", "cset w0, eq"])
case("zeroExtendedSelect", "int64_t", ["int32_t", "int64_t", "int64_t"], ["mov w0, w0", "cmp x2, #0", "csel x0, x0, x1, eq"])
case("signedStackLoad", "int64_t", ["int32_t"], ["str w0, [sp, #-16]!", "ldrsw x0, [sp]", "add sp, sp, #16"])
case("largeConstantAdd", "int64_t", ["int64_t"], ["mov x1, #0x100000000", "add x0, x0, x1"])
case("largeNegativeAdd", "int64_t", ["int64_t"], ["mov x1, #-0x100000000", "add x0, x0, x1"])
case("undefinedHighAdd", "int64_t", ["int32_t"], ["add x0, x0, #1"], True)
case("undefinedHighCompare", "int32_t", ["int32_t", "int64_t"], ["cmp x0, x1", "cset w0, eq"], True)
case("referenceShift", "int64_t", ["Il2CppObject*"], ["lsl x0, x0, #1"], True)
case("largePointerOffset", "int64_t", ["Il2CppObject*"], ["mov x1, #0x100000000", "add x0, x0, x1"], True)
case("undefinedHighMultiply", "int64_t", ["int32_t", "int64_t"], ["mul x0, x0, x1"], True)
case("referenceMultiply", "int64_t", ["Il2CppObject*", "int64_t"], ["mul x0, x0, x1"], True)
case('replaceUndefinedHigh', 'int32_t', ['uint8_t', 'int32_t'], ['bfi w0, w1, #8, #24'])
case('constantZeroExtendByte', 'int64_t', [], ['mov x0, #-1', 'uxtb w0, w0'])
case('zeroExtendedCrossExtract', 'int64_t', ['int32_t'], ['mov w0, w0', 'ubfx x0, x0, #24, #16'])
case('zeroExtendedHighExtract', 'int64_t', ['int32_t'], ['mov w0, w0', 'ubfx x0, x0, #32, #17'])
case('undefinedCrossExtract', 'int64_t', ['int32_t'], ['ubfx x0, x0, #24, #16'], True)

source = ".text\n" + "\n".join(f".global {s['Name']}\n.type {s['Name']}, %function\n{s['Name']}:\n" +
    "\n".join(s["Instructions"] + ["ret"]) + f"\n.size {s['Name']}, .-{s['Name']}" for s in samples)
(out / "cases.s").write_text(source, encoding="utf-8")
subprocess.run([config["Clang"], "-target", "aarch64-linux-gnu", "-c", str(out / "cases.s"), "-o", str(out / "cases.o")], check=True)
with (out / "cases.o").open("rb") as stream:
    elf = ELFFile(stream)
    code = elf.get_section_by_name(".text").data()
    symbols = {s.name: s.entry for s in elf.get_section_by_name(".symtab").iter_symbols() if s.entry["st_info"]["type"] == "STT_FUNC"}
for sample in samples:
    symbol = symbols[sample["Name"]]
    sample.update(Offset=symbol["st_value"], Size=symbol["st_size"], Address=0x100000 + symbol["st_value"])
(out / "cases.bin").write_bytes(code)
(out / "cases.json").write_text(json.dumps(samples), encoding="utf-8")
(out / "il2cpp.h").write_text("// Synthetic integer signatures only.\n", encoding="utf-8")
(out / "script.json").write_text(json.dumps({"ScriptMethod": [dict(Address=s["Address"], Name="IntegerFixture$$" + s["Name"],
    Signature=s["ReturnType"] + " " + s["Name"] + "(" + ", ".join(t + " " + n for t, n in zip(s["Types"], s["Names"])) + ");") for s in samples]}), encoding="utf-8")
subprocess.run(["dotnet", str(args.tool.resolve()), "integer-projection", str(args.configuration.resolve()), str(out)], cwd=ROOT, check=True)

rng = random.Random(18463)
edges = [0, 1, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0xffff, 0x7fffffff, 0x80000000, 0xffffffff,
         0x100000000, 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff]
rows = []
for sample in samples:
    if sample["Reject"]:
        continue
    for a, b, c in [(a, b, c) for a in edges for b in edges for c in (0, 1)] + [(rng.getrandbits(64), rng.getrandbits(64), rng.getrandbits(64)) for _ in range(64)]:
        uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
        uc.mem_map(0x100000, (len(code) + 8191) & ~4095)
        uc.mem_map(0x200000, 4096)
        uc.mem_write(0x100000, code)
        for index, value in enumerate((a, b, c)):
            uc.reg_write(UC_ARM64_REG_X0 + index, value)
        uc.reg_write(UC_ARM64_REG_SP, 0x200800)
        stop = 0x100000 + ((len(code) + 4095) & ~4095)
        uc.reg_write(UC_ARM64_REG_X30, stop)
        uc.emu_start(sample["Address"], stop, count=64)
        assert uc.reg_read(UC_ARM64_REG_PC) == stop, sample['Name']
        width = 32 if sample["ReturnType"].endswith("32_t") else 64
        expected = uc.reg_read(UC_ARM64_REG_X0) & ((1 << width) - 1)
        rows.append(dict(Name=sample["Name"], A=a, B=b, C=c, Width=width, Expected=expected))
(out / "observations.json").write_text(json.dumps(rows), encoding="utf-8")
types = {"int8_t": "sbyte", "uint8_t": "byte", "int16_t": "short", "uint16_t": "ushort", "int32_t": "int", "uint32_t": "uint", "int64_t": "long", "uint64_t": "ulong"}
arms = [f'"{s["Name"]}" => unchecked((ulong)Recovered.{s["Name"]}(' + ", ".join(f"unchecked(({types[t]}){n})" for t, n in zip(s["Types"], s["Names"])) + "))" for s in samples if not s["Reject"]]
fixture = '''using System.Text.Json;
var rows = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(args[0]))!;
foreach (var row in rows)
{
    var a = row.GetProperty("A").GetUInt64(); var b = row.GetProperty("B").GetUInt64(); var c = row.GetProperty("C").GetUInt64();
    var name = row.GetProperty("Name").GetString();
    var actual = name switch { /* ARMS */, _ => throw new Exception(name) };
    if (row.GetProperty("Width").GetInt32() == 32) actual &= uint.MaxValue;
    if (actual != row.GetProperty("Expected").GetUInt64()) throw new Exception($"{name}: {a:x}/{b:x}/{c:x}: {actual:x} != {row}");
}
Console.WriteLine($"PASS: {rows.Length} generated C# / ARM64 integer scenarios");
'''
(out / "Program.cs").write_text(fixture.replace("/* ARMS */", ",\n".join(arms)), encoding="utf-8")
(out / "IntegerFixture.csproj").write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>', encoding="utf-8")
subprocess.run(["dotnet", "restore", str(out / "IntegerFixture.csproj"), "--source", str(ROOT / "artifacts")], cwd=ROOT, check=True)
subprocess.run(["dotnet", "run", "--project", str(out / "IntegerFixture.csproj"), "-c", "Release", "--no-restore", "--", str(out / "observations.json")], cwd=ROOT, check=True)
report = dict(functions=len(samples), rejected=sum(s["Reject"] for s in samples), cases=len(rows),
              codeSha256=hashlib.sha256(code).hexdigest(), generatedSha256=hashlib.sha256((out / "Recovered.cs").read_bytes()).hexdigest(),
              scope="assembled synthetic ARM64 functions and actual generated C#; no game runtime claim")
(out / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
print(json.dumps(report))
