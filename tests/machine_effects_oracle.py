"""将统一机器效果逐条与 Unicorn 的真实 ARM64 执行比较，不使用游戏特例。"""
import argparse
import json
import math
import random
import struct
import subprocess
from pathlib import Path
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import *

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("configuration", type=Path, nargs="?", default=ROOT / "native.local.json")
parser.add_argument("--tool", type=Path, default=ROOT / "tests/Cpp2CS.Tests/bin/Release/net10.0/Cpp2CS.Tests.dll")
args = parser.parse_args()
CFG = json.loads(args.configuration.read_text(encoding="utf-8-sig"))
OUT = ROOT / "artifacts" / "machine-effects"
OUT.mkdir(parents=True, exist_ok=True)
subprocess.run([CFG["Clang"], "-target", "aarch64-linux-gnu", "-c", str(ROOT / "tests/machine_effects.s"), "-o", str(OUT / "cases.o")], check=True)
with (OUT / "cases.o").open("rb") as stream:
    code = ELFFile(stream).get_section_by_name(".text").data()
(OUT / "cases.bin").write_bytes(code)
subprocess.run(["dotnet", str(args.tool.resolve()),
                "machine-effects", str(args.configuration.resolve()), str(OUT / "cases.bin"), str(OUT / "effects.json")], check=True)
effects = json.loads((OUT / "effects.json").read_text(encoding="utf-8"))
BASE, MEMORY = 0x100000, 0x200000

def reg(name):
    if name == "sp": return UC_ARM64_REG_SP
    if name == "nzcv": return UC_ARM64_REG_NZCV
    if name.startswith("v"): return UC_ARM64_REG_Q0 + int(name[1:])
    n = int(name[1:])
    return UC_ARM64_REG_X0 + n if n < 29 else UC_ARM64_REG_X29 if n == 29 else UC_ARM64_REG_X30

def signed(number, width):
    return number - (1 << width) if number & (1 << (width - 1)) else number

def floating(number, width):
    return struct.unpack("<f" if width == 32 else "<d", number.to_bytes(width // 8, "little"))[0]

def bits(number, width):
    return int.from_bytes(struct.pack("<f" if width == 32 else "<d", number), "little")

def evaluate(node, registers, memory):
    op, width, immediate = node["Operation"], node["Width"], node["Immediate"]
    args = node["Inputs"]
    values = [evaluate(a, registers, memory) for a in args]
    if op == "read": answer = registers[node["Register"]]
    elif op == "constant": answer = immediate
    elif op in ("zero-extend", "reinterpret"): answer = values[0]
    elif op == "slice": answer = values[0] >> immediate
    elif op == "sign-extend": answer = signed(values[0], args[0]["Width"])
    elif op == "add": answer = values[0] + values[1]
    elif op == "sub": answer = values[0] - values[1]
    elif op == "multiply": answer = values[0] * values[1]
    elif op == "and": answer = values[0] & values[1]
    elif op == "orr": answer = values[0] | values[1]
    elif op == "eor": answer = values[0] ^ values[1]
    elif op == "shift-left": answer = values[0] << immediate
    elif op == "shift-right": answer = values[0] >> immediate
    elif op == "shift-arithmetic": answer = signed(values[0], width) >> immediate
    elif op == "address": answer = values[0] + immediate
    elif op == "load": answer = int.from_bytes(memory[values[0]-MEMORY:values[0]-MEMORY+width//8], "little")
    elif op in ("compare", "compare-add", "compare-and"):
        a, b = values
        w = args[0]["Width"]
        full = a + b if op == "compare-add" else a & b if op == "compare-and" else a - b
        result = full & ((1 << w) - 1)
        carry = int(full >= (1 << w)) if op == "compare-add" else 0 if op == "compare-and" else int(a >= b)
        overflow = ((~(a ^ b) if op == "compare-add" else a ^ b) & (a ^ result)) >> (w-1) & 1
        answer = ((result >> (w-1)) << 3) | (int(result == 0) << 2) | (carry << 1) | (0 if op == "compare-and" else overflow)
    elif op == "condition-value":
        n, z, c, v = (bool(values[0] & bit) for bit in (8, 4, 2, 1))
        answer = int([z, not z, c, not c, n, not n, v, not v, c and not z, not c or z,
                      n == v, n != v, not z and n == v, z or n != v][immediate-1])
    elif op == "select": answer = values[1] if values[0] else values[2]
    elif op == "signed-to-float": answer = bits(float(signed(values[0], args[0]["Width"])), width)
    elif op == "float-divide": answer = bits(floating(values[0], width) / floating(values[1], width), width)
    elif op == "float-ceiling": answer = bits(float(math.ceil(floating(values[0], width))), width)
    elif op == "float-to-signed-ceiling": answer = math.ceil(floating(values[0], args[0]["Width"]))
    elif op == "compare-float":
        a, b = (floating(v, args[i]["Width"]) for i, v in enumerate(values))
        answer = 3 if math.isnan(a) or math.isnan(b) else 6 if a == b else 8 if a < b else 2
    else: raise AssertionError(op)
    return answer & ((1 << width) - 1)

rng = random.Random(7341)
checks = 0
for effect in effects:
    pc = effect["Source"]["Address"]
    for case in range(32):
        uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
        uc.mem_map(BASE, 4096)
        uc.mem_map(MEMORY, 8192)
        uc.mem_write(BASE, code)
        memory = rng.randbytes(8192)
        uc.mem_write(MEMORY, memory)
        registers = {f"x{i}": rng.getrandbits(64) for i in range(31)}
        registers.update({f"v{i}": rng.getrandbits(128) for i in range(32)})
        registers.update(sp=MEMORY+4096, x3=MEMORY+1024, x4=case, nzcv=case % 16)
        if effect["Source"]["Mnemonic"] in ("fdiv", "frintp", "fcvtps", "fcmp"):
            scalar = 64 if effect["Source"]["Mnemonic"] == "frintp" else 32
            registers["v1"] = bits((-1 if case % 2 else 1) * (case + 0.25), scalar)
            registers["v2"] = bits(3.0, scalar)
        for name, value in registers.items():
            uc.reg_write(reg(name), value << 28 if name == "nzcv" else value)
        assigned = [(w["Register"], evaluate(w["Value"], registers, memory)) for w in effect["Assignments"]]
        stored = [(evaluate(s["Address"], registers, memory), evaluate(s["Value"], registers, memory).to_bytes(s["Value"]["Width"]//8, "little")) for s in effect["Stores"]]
        uc.emu_start(pc, pc+4, count=1)
        for name, expected in assigned:
            actual = uc.reg_read(reg(name))
            if name == "nzcv": actual >>= 28
            assert actual == expected, (effect["Source"]["Mnemonic"], effect["Source"]["Display"], case, name, hex(actual), hex(expected))
            checks += 1
        for address, expected in stored:
            assert bytes(uc.mem_read(address, len(expected))) == expected, (effect["Source"], case)
            checks += 1
        if effect["Source"]["Mnemonic"] in ("mul", "mneg", "madd", "msub"):
            assert uc.reg_read(UC_ARM64_REG_NZCV) >> 28 == registers["nzcv"], (effect["Source"], case, "NZCV changed")
            checks += 1
print(f"PASS: {len(effects)} ARM64 instructions x 32 states; {checks} independent register/memory comparisons")
