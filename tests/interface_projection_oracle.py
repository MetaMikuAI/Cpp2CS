"""以独立 ARM64 执行核对两条恢复路径的入口、间接聚合、返回和尾调用。"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import shutil
import struct
import subprocess
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn import arm64_const as reg

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("configuration", type=Path)
parser.add_argument("--tool", type=Path, required=True)
args = parser.parse_args()
config = json.loads(args.configuration.read_text(encoding="utf-8-sig"))
out = ROOT / "artifacts/interface-projection"
out.mkdir(parents=True, exist_ok=True)
samples = []
shapes = {"Payload8": (8, "int32_t"), "Payload24": (24, "int32_t"), "Payload40": (40, "int32_t"),
          "Payload84": (84, "int32_t"), "Hfa3": (12, "float")}


def case(name, types, body, result="int32_t", reject=False, fallback_reject=False):
    for ssa in (False, True):
        samples.append(dict(Name=name + ("Ssa" if ssa else "Projection"), Types=types,
                            Names=["a" + str(i) for i in range(len(types))], Instructions=body,
                            ReturnType=result, Reject=reject or fallback_reject and not ssa, Ssa=ssa))


for prefix in (0, 7, 8, 9):
    case(f"Integer{prefix}", ["int32_t"] * (prefix + 1),
         ([f"mov w0, w{prefix}"] if prefix < 8 else [f"ldr w0, [sp, #{(prefix - 8) * 8}]"]) + ["ret"])
    case(f"Float{prefix}", ["float"] * (prefix + 1),
         ([f"fmov s0, s{prefix}"] if prefix < 8 else [f"ldr s0, [sp, #{(prefix - 8) * 8}]"]) + ["ret"], "float")
    for shape, (size, scalar) in shapes.items():
        types = [scalar] * prefix + [shape]
        for field in (0, size // 4 - 1):
            if shape == "Hfa3":
                load = [f"fmov s0, s{prefix + field}"] if prefix + 3 <= 8 else [f"ldr s0, [sp, #{max(0, prefix - 8) * 8 + field * 4}]"]
            elif size <= 16:
                load = ([f"str x{prefix}, [sp, #-16]!", f"ldr w0, [sp, #{field * 4}]", "add sp, sp, #16"] if prefix < 8 else
                        [f"ldr w0, [sp, #{(prefix - 8) * 8 + field * 4}]"])
            else:
                load = ([f"mov x10, x{prefix}"] if prefix < 8 else [f"ldr x10, [sp, #{(prefix - 8) * 8}]"])
                load += ["add x10, x10, #16", f"ldr w0, [x10, #{field * 4 - 16}]"]
            case(f"{shape}P{prefix}F{field}", types, load + ["ret"], scalar)
    case(f"FrameScalar{prefix}", ["int32_t"] * (prefix + 1), ["sub sp, sp, #32"] +
         ([f"mov w0, w{prefix}"] if prefix < 8 else [f"ldr w0, [sp, #{32 + (prefix - 8) * 8}]"]) + ["add sp, sp, #32", "ret"])

case("AggregateIdentity", ["Payload8"], ["ret"], "Payload8")
case("HfaIdentity", ["Hfa3"], ["ret"], "Hfa3")
case("WriteParameter", ["Payload24"], ["mov w9, #321", "str w9, [x0, #20]", "ldr w0, [x0, #20]", "ret"])
case("ParameterSnapshot", ["Payload24"], ["ldr w9, [x0, #20]", "mov w10, #321", "str w10, [x0, #20]", "mov w0, w9", "ret"])
case("TailInteger", ["int32_t"], ["b .Lidentity"])
case("TailFloat", ["float"], ["b .Lfloat"], "float")
case("TailAfterCall", ["int32_t"], ["str x30, [sp, #-16]!", "bl .Lidentity", "ldr x30, [sp], #16", "b .Lidentity"])
case("TailAggregate", ["Payload24"], ["b .Lread"])
case("TailStack", ["int32_t"] * 9, ["b .Lstack"])
case("CallFloat", ["float"], ["str x30, [sp, #-16]!", "bl .Lfloat", "ldr x30, [sp], #16", "ret"], "float")
case("CallAggregate", ["Payload24"], ["str x30, [sp, #-16]!", "bl .Lread", "ldr x30, [sp], #16", "ret"])
case("CopiedParameterSnapshot", ["Payload24"], ["sub sp, sp, #48", "str x30, [sp, #32]", "ldp x9, x10, [x0]", "ldr x11, [x0, #16]",
     "stp x9, x10, [sp]", "str x11, [sp, #16]", "mov w9, #321", "str w9, [x0, #20]", "mov x0, sp", "bl .Lread",
     "ldr x30, [sp, #32]", "add sp, sp, #48", "ret"], fallback_reject=True)
case("AfterMutatingCall", ["Payload24"], ["stp x19, x30, [sp, #-16]!", "mov x19, x0", "bl .Loverwrite",
     "ldr w0, [x19, #20]", "ldp x19, x30, [sp], #16", "ret"], reject=True)
case("TailBadStack", ["int32_t"], ["sub sp, sp, #16", "b .Lidentity"], reject=True)
case("TailBadPreserved", ["int32_t"], ["mov x19, xzr", "b .Lidentity"], reject=True)
case("TailBadFloatPreserved", ["int32_t"], ["fmov d8, x0", "b .Lidentity"], reject=True)
case("TailBadLink", ["int32_t"], ["mov x30, xzr", "b .Lidentity"], reject=True)
case("TailExtraStack", ["int32_t"] * 8, ["b .Lstack"], reject=True)
case("StackPadding", ["int32_t"] * 9, ["ldr x0, [sp]", "ret"], "int64_t", True)
case("TailWrongResult", ["float"], ["b .Lfloat"], reject=True)
case("ParameterUnknownAlias", ["Payload24", "int32_t*"], ["mov w9, #321", "str w9, [x1]", "ldr w0, [x0, #20]", "ret"], reject=True)
case("TailLocalBuffer", ["Payload24"], ["ldp x9, x10, [x0]", "ldr x11, [x0, #16]", "stp x9, x10, [sp, #-32]",
     "str x11, [sp, #-16]", "sub x0, sp, #32", "b .Lread"], reject=True)

callees = [("Identity", "int32_t", ["int32_t"], ".Lidentity:\nret"),
           ("FloatIdentity", "float", ["float"], ".Lfloat:\nret"),
           ("Read", "int32_t", ["Payload24"], ".Lread:\nldr w0, [x0, #20]\nret"),
           ("Overwrite", "void", ["Payload24"], ".Loverwrite:\nmov w9, #321\nstr w9, [x0, #20]\nret"),
           ("Stack", "int32_t", ["int32_t"] * 9, ".Lstack:\nldr w0, [sp]\nret")]
source = ".text\n" + "\n".join(f".type {s['Name']}, %function\n{s['Name']}:\n" + "\n".join(s["Instructions"]) +
    f"\n.size {s['Name']}, .-{s['Name']}" for s in samples)
source += "\n" + "\n".join(f".type {name}, %function\n{name}:\n{body}\n.size {name}, .-{name}" for name, _, _, body in callees)
(out / "cases.s").write_text(source, encoding="utf-8")
subprocess.run([config["Clang"], "-target", "aarch64-linux-gnu", "-c", str(out / "cases.s"), "-o", str(out / "cases.o")], check=True)
with (out / "cases.o").open("rb") as stream:
    elf = ELFFile(stream)
    assert not any(s["sh_type"] in ("SHT_REL", "SHT_RELA") and s["sh_size"] for s in elf.iter_sections())
    code = elf.get_section_by_name(".text").data()
    symbols = {s.name: s.entry for s in elf.get_section_by_name(".symtab").iter_symbols() if s.entry["st_info"]["type"] == "STT_FUNC"}
methods = []
for sample in samples:
    symbol = symbols[sample["Name"]]
    sample.update(Offset=symbol["st_value"], Size=symbol["st_size"], Address=0x100000 + symbol["st_value"])
    signature = ", ".join(t + " " + n for t, n in zip(sample["Types"], sample["Names"]))
    methods.append(dict(Address=sample["Address"], Name="Fixture$$" + sample["Name"], Signature=f"{sample['ReturnType']} {sample['Name']}({signature});"))
for name, result, types, _ in callees:
    methods.append(dict(Address=0x100000 + symbols[name]["st_value"], Name="Fixture$$" + name,
                        Signature=f"{result} {name}(" + ", ".join(t + " a" + str(i) for i, t in enumerate(types)) + ");"))
(out / "cases.bin").write_bytes(code)
(out / "cases.json").write_text(json.dumps(samples), encoding="utf-8")
(out / "script.json").write_text(json.dumps({"ScriptMethod": methods}), encoding="utf-8")
(out / "il2cpp.h").write_text("\n".join("struct " + name + " { " + " ".join(f"{scalar} f{i};" for i in range(size // 4)) + " };"
    for name, (size, scalar) in shapes.items()), encoding="utf-8")

model = out / "model"
model.mkdir(exist_ok=True)
(model / "Model.cs").write_text("\n".join("public struct " + name + " { " + " ".join(f"public {'float' if scalar == 'float' else 'int'} f{i};" for i in range(size // 4)) + " }"
    for name, (size, scalar) in shapes.items()) + """
public static class Fixture {
 public static int Identity(int a0) => a0;
 public static float FloatIdentity(float a0) => a0;
 public static int Read(Payload24 a0) => a0.f5;
 public static void Overwrite(Payload24 a0) { a0.f5 = 321; }
 public static int Stack(int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int a8) => a8;
}
""", encoding="utf-8")
(model / "Model.csproj").write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>Managed</AssemblyName></PropertyGroup></Project>', encoding="utf-8")
subprocess.run(["dotnet", "build", str(model / "Model.csproj"), "-c", "Release", "-p:RestoreSources=" + str(model)], cwd=ROOT, check=True)
shutil.copyfile(model / "bin/Release/net10.0/Managed.dll", out / "Managed.dll")

rng = random.Random(20261014)
rows = []
for sample in samples:
    if sample["Reject"]:
        continue
    for iteration in range(24):
        uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
        uc.mem_map(0x100000, 0x10000)
        uc.mem_map(0x200000, 0x20000)
        uc.mem_write(0x100000, code)
        sp = 0x208000
        uc.mem_write(sp, rng.randbytes(2048))
        uc.reg_write(reg.UC_ARM64_REG_SP, sp)
        uc.reg_write(reg.UC_ARM64_REG_X30, 0x10fff0)
        for i in range(8):
            uc.reg_write(getattr(reg, "UC_ARM64_REG_X" + str(i)), rng.getrandbits(64))
            uc.reg_write(getattr(reg, "UC_ARM64_REG_Q" + str(i)), rng.getrandbits(128))
        preserved = {getattr(reg, "UC_ARM64_REG_X" + str(i)): rng.getrandbits(64) for i in range(19, 30)}
        for register, value in preserved.items(): uc.reg_write(register, value)
        general = floating = stack = 0
        values = []
        for index, t in enumerate(sample["Types"]):
            size, scalar = shapes.get(t, (4, t))
            data = [struct.unpack("<I", struct.pack("<f", rng.uniform(-1000, 1000)))[0] if scalar == "float" else rng.getrandbits(32) for _ in range(size // 4)]
            if iteration == 0: data = [0] * len(data)
            if iteration == 1 and scalar != "float": data = [0xffffffff] * len(data)
            if scalar == "float" and iteration in (1, 2, 3, 4): data = [{1: 0x80000000, 2: 0x7f800000, 3: 0x7fc00001, 4: 0x7f800001}[iteration]] * len(data)
            values.append(data)
            raw = b"".join(struct.pack("<I", v) for v in data)
            if scalar == "float":
                if floating + len(data) <= 8:
                    for part in data:
                        uc.reg_write(getattr(reg, "UC_ARM64_REG_Q" + str(floating)), (rng.getrandbits(96) << 32) | part)
                        floating += 1
                    continue
                floating = 8
            else:
                if size > 16:
                    address = 0x210000 + index * 256
                    uc.mem_write(address, raw)
                    raw = struct.pack("<Q", address)
                if general < 8:
                    uc.reg_write(getattr(reg, "UC_ARM64_REG_X" + str(general)), int.from_bytes(raw, "little") | (rng.getrandbits(32) << 32 if len(raw) == 4 else 0))
                    general += 1
                    continue
            uc.mem_write(sp + stack, raw)
            stack += (len(raw) + 7) // 8 * 8
        uc.emu_start(sample["Address"], 0x10fff0, count=128)
        assert uc.reg_read(reg.UC_ARM64_REG_PC) == 0x10fff0
        assert uc.reg_read(reg.UC_ARM64_REG_SP) == sp
        assert all(uc.reg_read(register) == value for register, value in preserved.items())
        result = sample["ReturnType"]
        if result == "Hfa3": expected = [uc.reg_read(getattr(reg, "UC_ARM64_REG_S" + str(i))) for i in range(3)]
        elif result == "Payload8": expected = [(uc.reg_read(reg.UC_ARM64_REG_X0) >> (32 * i)) & 0xffffffff for i in range(2)]
        else: expected = [uc.reg_read(reg.UC_ARM64_REG_S0) if result == "float" else uc.reg_read(reg.UC_ARM64_REG_X0) & 0xffffffff]
        rows.append(dict(Name=sample["Name"], Values=values, Expected=expected))
(out / "observations.json").write_text(json.dumps(rows), encoding="utf-8")
subprocess.run(["dotnet", str(args.tool.resolve()), "native-projection", str(args.configuration.resolve()), str(out)], cwd=ROOT, check=True)


def scalar_value(scalar, text):
    return f"BitConverter.Int32BitsToSingle(unchecked((int){text}))" if scalar == "float" else f"unchecked((int){text})"


arms = []
for sample in samples:
    if sample["Reject"]: continue
    arguments = []
    for index, t in enumerate(sample["Types"]):
        if t in shapes:
            size, scalar = shapes[t]
            arguments.append("new " + t + " { " + ", ".join(f"f{i} = " + scalar_value(scalar, f"values[{index}][{i}]") for i in range(size // 4)) + " }")
        else: arguments.append(scalar_value(t, f"values[{index}][0]"))
    call = f"Recovered.{sample['Name']}(" + ", ".join(arguments) + ")"
    result = sample["ReturnType"]
    converted = "Bits(result)" if result not in shapes else "new uint[] { " + ", ".join(f"Bits(result.f{i})" for i in range(shapes[result][0] // 4)) + " }"
    if result not in shapes: converted = "new uint[] { " + converted + " }"
    arms.append(f'case "{sample["Name"]}": {{ var result = {call}; actual = {converted}; break; }}')
(out / "Program.cs").write_text("""
using System;
using System.Linq;
using System.Text.Json;
public static class Program {
 public static uint Bits(int value) => unchecked((uint)value);
 public static uint Bits(float value) => unchecked((uint)BitConverter.SingleToInt32Bits(value));
 public static void Main(string[] args) {
 var rows = JsonSerializer.Deserialize<JsonElement[]>(System.IO.File.ReadAllText(args[0]))!;
 foreach (var row in rows) {
 var values = row.GetProperty("Values").EnumerateArray().Select(a => a.EnumerateArray().Select(v => v.GetUInt32()).ToArray()).ToArray();
 uint[] actual;
 switch (row.GetProperty("Name").GetString()) { /* CASES */ default: throw new Exception(row.ToString()); }
 if (!actual.SequenceEqual(row.GetProperty("Expected").EnumerateArray().Select(v => v.GetUInt32()))) throw new Exception(row.ToString());
 }
 Console.WriteLine($"PASS: {rows.Length} generated C# / ARM64 interface scenarios");
 }
}
""".replace("/* CASES */", "\n".join(arms)), encoding="utf-8")
(out / "Fixture.csproj").write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><EnableDefaultCompileItems>false</EnableDefaultCompileItems></PropertyGroup><ItemGroup><Compile Include="Program.cs"/><Compile Include="Recovered.cs"/><Reference Include="Managed"><HintPath>Managed.dll</HintPath></Reference></ItemGroup></Project>', encoding="utf-8")
subprocess.run(["dotnet", "run", "--project", str(out / "Fixture.csproj"), "-c", "Release", "-p:RestoreSources=" + str(out), "--", str(out / "observations.json")], cwd=ROOT, check=True)
report = dict(functions=len(samples), accepted=sum(not s["Reject"] for s in samples), rejected=sum(s["Reject"] for s in samples),
              compiledNativeComparisons=len(rows), codeSha256=hashlib.sha256(code).hexdigest(), sourceSha256=hashlib.sha256((out / "Recovered.cs").read_bytes()).hexdigest())
(out / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
print(json.dumps(report))
