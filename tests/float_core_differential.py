import json
from pathlib import Path
import random
import subprocess
import sys
import argparse
import hashlib
from collections import Counter
import capstone
import unicorn
from unicorn import arm64_const as arm

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tests"))
from x64_float_native import NativeFloatOracle

DLL = Path(__file__).parent / "FloatCoreHarness/bin/Release/net10.0/FloatCoreHarness.dll"
parser = argparse.ArgumentParser()
parser.add_argument("--output", type=Path, default=ROOT / "artifacts/float-core-differential.json")
parser.add_argument("--harness", type=Path, default=DLL)
args = parser.parse_args()
DLL = args.harness
core_checks = int(subprocess.check_output(["dotnet", str(DLL), "selftest"], text=True))
server = subprocess.Popen(["dotnet", str(DLL)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
rng = random.Random(0xF108)
count = 0
native_counts = Counter()
arm_counts = Counter()


def request(kind, width, result_width, a, b, control, rounding="Current", arch="X64"):
    server.stdin.write(json.dumps(dict(arch=arch, kind=kind, width=width,
        resultWidth=result_width, a=f"{a:x}", b=f"{b:x}", control=control, rounding=rounding)) + "\n")
    server.stdin.flush()
    return json.loads(server.stdout.readline())


def flags(csr):
    return sum(((csr >> source) & 1) << target for target, source in enumerate([0, 2, 3, 4, 5, 1]))


def conversion_edges(width):
    fraction, bias = (23, 127) if width == 32 else (52, 1023)
    sign = 1 << (width - 1)
    infinity = (2 * bias + 1) << fraction
    result = [0, sign, 1, sign | 1, (1 << fraction) - 1, 1 << fraction,
              infinity - 1, infinity, sign | infinity, infinity | 1,
              sign | infinity | 7, infinity | (1 << (fraction - 1)) | 11]
    for exponent in (-1, 0, 1, 23, 24, 31, 32, 52, 53, 63, 64):
        bits = (bias + exponent) << fraction
        result.extend((bits - 1, bits, bits + 1, sign | (bits - 1), sign | bits, sign | (bits + 1)))
    if width == 64:
        result.extend((0x380FFFFFE1000000, 0x380FFFFFEFFFFFFF, 0x380FFFFFF0000000,
                       0x36A0000000000000, 0x3690000000000000, 0x47EFFFFFEFFFFFFF,
                       0x47EFFFFFF0000000, 0x3FF0000010000000, 0x3FF0000030000000))
    return result


def check_native(kind, width, result_width, a, b, control, code, *, rounding="Current", integer=False):
    global count
    actual = request(kind, width, result_width, a, b, control, rounding)
    expected = native.run(code, xmm0=a, xmm1=a if kind in ("Sqrt", "Convert", "ToSigned") else b,
                          rbx=a, mxcsr=control)
    bits = expected["rax" if integer else "xmm0"] & ((1 << result_width) - 1)
    assert int(actual["bits"], 16) == bits and actual["Flags"] == flags(expected["mxcsr"]), (
        kind, width, result_width, hex(a), hex(b), hex(control), rounding, actual, expected)
    assert actual["TrapFlags"] == actual["Flags"], actual
    count += 1
    native_counts[kind] += 1


class ArmOracle:
    def __init__(self):
        self.cpu = unicorn.Uc(unicorn.UC_ARCH_ARM64, unicorn.UC_MODE_ARM)
        self.cpu.mem_map(0x10000, 0x10000)
        self.cpu.reg_write(arm.UC_ARM64_REG_CPACR_EL1, 0x300000)
        self.instructions = {}
        self.decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM)

    def run(self, word, mnemonic, a, b, control, kind):
        if word not in self.instructions:
            address = 0x10000 + 4 * len(self.instructions)
            code = word.to_bytes(4, "little")
            decoded = list(self.decoder.disasm(code, address))
            assert len(decoded) == 1 and decoded[0].mnemonic == mnemonic, (hex(word), mnemonic, decoded)
            self.cpu.mem_write(address, code)
            self.instructions[word] = address
        address = self.instructions[word]
        self.cpu.reg_write(arm.UC_ARM64_REG_Q0, (1 << 128) - 1)
        self.cpu.reg_write(arm.UC_ARM64_REG_Q1, a)
        self.cpu.reg_write(arm.UC_ARM64_REG_Q2, b)
        self.cpu.reg_write(arm.UC_ARM64_REG_X0, (1 << 64) - 1)
        self.cpu.reg_write(arm.UC_ARM64_REG_X1, a)
        self.cpu.reg_write(arm.UC_ARM64_REG_FPCR, control)
        self.cpu.reg_write(arm.UC_ARM64_REG_FPSR, 0)
        self.cpu.reg_write(arm.UC_ARM64_REG_NZCV, 0)
        self.cpu.emu_start(address, address + 4, count=1)
        result_register = arm.UC_ARM64_REG_X0 if kind in ("ToSigned", "ToUnsigned") else arm.UC_ARM64_REG_Q0
        bits = self.cpu.reg_read(result_register)
        if kind in ("Compare", "CompareSignal"):
            bits = self.cpu.reg_read(arm.UC_ARM64_REG_NZCV) >> 28
        fpsr = self.cpu.reg_read(arm.UC_ARM64_REG_FPSR)
        status = sum(((fpsr >> source) & 1) << target for target, source in enumerate([0, 1, 2, 3, 4, 7]))
        return bits, status


def check_arm(kind, width, result_width, a, b, control, word, mnemonic, rounding="Current"):
    actual = request(kind, width, result_width, a, b, control, rounding, arch="Arm64")
    bits, status = arm_oracle.run(word, mnemonic, a, b, control, kind)
    assert int(actual["bits"], 16) == bits & ((1 << result_width) - 1) and actual["Flags"] == status, (
        kind, width, result_width, hex(word), hex(a), hex(b), hex(control), rounding, actual, hex(bits), status)
    expected_traps = status & ~8 if control & (1 << 24) else status
    assert actual["TrapFlags"] == expected_traps, (kind, actual, expected_traps)
    arm_counts[kind] += 1


with NativeFloatOracle() as native:
    for width in (32, 64):
        prefix = "f3" if width == 32 else "f2"
        sign = 1 << (width - 1)
        fraction = 23 if width == 32 else 52
        infinity = ((1 << (width - fraction - 1)) - 1) << fraction
        one = (127 if width == 32 else 1023) << fraction
        quiet = 1 << (fraction - 1)
        edges = [0, sign, one, sign | one, infinity, sign | infinity,
                 infinity | quiet | 1, infinity | 17, sign | infinity | quiet | 31,
                 sign | infinity | 47, 1, sign | 1, (1 << fraction) - 1,
                 1 << fraction, infinity - 1, one + 1]
        for rc in range(4):
            for daz in (0, 0x40):
                for ftz in (0, 0x8000):
                    control = 0x1F80 | (rc << 13) | daz | ftz
                    cases = [(a, b) for a in edges for b in edges]
                    cases += [(rng.getrandbits(width), rng.getrandbits(width)) for _ in range(100)]
                    for kind, opcode in (("Add", "58"), ("Sub", "5c"), ("Mul", "59"),
                                         ("Div", "5e"), ("Min", "5d"), ("Max", "5f")):
                        for a, b in cases:
                            check_native(kind, width, width, a, b, control, prefix + "0f" + opcode + "c1")
                    for a in edges + [rng.getrandbits(width) for _ in range(100)]:
                        check_native("Sqrt", width, width, a, 0, control, prefix + "0f51c1")
                    for kind, opcode in (("Compare", "2e"), ("CompareSignal", "2f")):
                        for a, b in cases:
                            actual = request(kind, width, 4, a, b, control)
                            expected = native.run(("" if width == 32 else "66") + "0f" + opcode + "c1", xmm0=a, xmm1=b, mxcsr=control)
                            ef = expected["eflags"]
                            comparison = 3 if ef & 4 else 6 if ef & 64 else 8 if ef & 1 else 2
                            assert int(actual["bits"], 16) == comparison and actual["Flags"] == flags(expected["mxcsr"]), (kind, width, hex(a), hex(b), hex(control), actual, expected)
                            assert actual["TrapFlags"] == actual["Flags"], actual
                            count += 1
                            native_counts[kind] += 1
                    conversions = conversion_edges(width) + [rng.getrandbits(width) for _ in range(100)]
                    for a in conversions:
                        check_native("Convert", width, 96 - width, a, 0, control, prefix + "0f5ac1")
                    for integer_width in (32, 64):
                        rex = "48" if integer_width == 64 else ""
                        for rounding, opcode in (("Current", "2d"), ("TowardZero", "2c")):
                            for a in conversions:
                                check_native("ToSigned", width, integer_width, a, 0, control,
                                             prefix + rex + "0f" + opcode + "c1", rounding=rounding, integer=True)
                        integers = [0, 1, (1 << integer_width) - 1, 1 << (integer_width - 1),
                                    (1 << (integer_width - 1)) - 1]
                        for exponent in (23, 24, 31, 32, 52, 53, 63):
                            if exponent < integer_width:
                                integers.extend((1 << exponent) + d for d in (-1, 0, 1))
                        integers += [rng.getrandbits(integer_width) for _ in range(100)]
                        for a in integers:
                            check_native("FromSigned", integer_width, width, a, 0, control, prefix + rex + "0f2ac3")
        print(f"width {width}: {count} native cases passed", flush=True)

arm_oracle = ArmOracle()
for width in (32, 64):
    size = 0x400000 if width == 64 else 0
    fraction, bias = (23, 127) if width == 32 else (52, 1023)
    sign = 1 << (width - 1)
    infinity = (2 * bias + 1) << fraction
    one = bias << fraction
    edges = [0, sign, one, sign | one, infinity, sign | infinity,
             infinity | (1 << (fraction - 1)) | 1, infinity | 17,
             sign | infinity | (1 << (fraction - 1)) | 31, sign | infinity | 47,
             1, sign | 1, (1 << fraction) - 1, 1 << fraction, infinity - 1, one + 1]
    for rc in range(4):
        for fz in (0, 1 << 24):
            for dn in (0, 1 << 25):
                control = (rc << 22) | fz | dn
                pairs = [(a, b) for a in edges for b in edges]
                pairs += [(rng.getrandbits(width), rng.getrandbits(width)) for _ in range(100)]
                for kind, opcode, mnemonic in (
                        ("Mul", 0, "fmul"), ("Div", 1, "fdiv"), ("Add", 2, "fadd"), ("Sub", 3, "fsub"),
                        ("Max", 4, "fmax"), ("Min", 5, "fmin"), ("MaxNumber", 6, "fmaxnm"),
                        ("MinNumber", 7, "fminnm"), ("NegMul", 8, "fnmul")):
                    word = 0x1E220820 | size | (opcode << 12)
                    for a, b in pairs:
                        check_arm(kind, width, width, a, b, control, word, mnemonic)
                for a, b in pairs:
                    check_arm("AbsDiff", width, width, a, b, control, 0x7EA2D420 | size, "fabd")
                for kind, low, mnemonic in (("Compare", 0, "fcmp"), ("CompareSignal", 16, "fcmpe")):
                    for a, b in pairs:
                        check_arm(kind, width, 4, a, b, control, 0x1E222020 | size | low, mnemonic)
                unary = conversion_edges(width) + [rng.getrandbits(width) for _ in range(100)]
                for a in unary:
                    check_arm("Sqrt", width, width, a, 0, control, 0x1E21C020 | size, "fsqrt")
                    check_arm("Convert", width, 96 - width, a, 0, control,
                              0x1E22C020 if width == 32 else 0x1E624020, "fcvt")
                for rounding, opcode, mnemonic in (
                        ("TiesEven", 8, "frintn"), ("PlusInfinity", 9, "frintp"), ("MinusInfinity", 10, "frintm"),
                        ("TowardZero", 11, "frintz"), ("TiesAway", 12, "frinta"),
                        ("Current", 14, "frintx"), ("Current", 15, "frinti")):
                    kind = "RoundIntegralExact" if opcode == 14 else "RoundIntegral"
                    for a in unary:
                        check_arm(kind, width, width, a, 0, control, 0x1E204020 | size | (opcode << 15), mnemonic, rounding)
                for integer_width in (32, 64):
                    sf = 0x80000000 if integer_width == 64 else 0
                    for unsigned in (False, True):
                        u = 0x10000 if unsigned else 0
                        suffix = "u" if unsigned else "s"
                        kind = "ToUnsigned" if unsigned else "ToSigned"
                        for rounding, opcode, mnemonic in (
                                ("TiesEven", 0x1E200020, "fcvtn" + suffix),
                                ("PlusInfinity", 0x1E280020, "fcvtp" + suffix),
                                ("MinusInfinity", 0x1E300020, "fcvtm" + suffix),
                                ("TowardZero", 0x1E380020, "fcvtz" + suffix),
                                ("TiesAway", 0x1E240020, "fcvta" + suffix)):
                            for a in unary:
                                check_arm(kind, width, integer_width, a, 0, control, opcode | sf | size | u, mnemonic, rounding)
                        integers = [0, 1, (1 << integer_width) - 1, 1 << (integer_width - 1),
                                    (1 << (integer_width - 1)) - 1]
                        for exponent in (23, 24, 31, 32, 52, 53, 63):
                            if exponent < integer_width:
                                integers.extend((1 << exponent) + d for d in (-1, 0, 1))
                        integers += [rng.getrandbits(integer_width) for _ in range(100)]
                        for a in integers:
                            check_arm("FromUnsigned" if unsigned else "FromSigned", integer_width, width, a, 0,
                                      control, 0x1E220020 | sf | size | u, "ucvtf" if unsigned else "scvtf")
    print(f"width {width}: {sum(arm_counts.values())} Arm64 simulator cases passed", flush=True)
server.stdin.close()
assert server.wait() == 0
sources = ["src/Cpp2CS/Architecture.cs", "src/Cpp2CS/Ir/Model.cs", "src/Cpp2CS/Ir/MemoryModel.cs", "src/Cpp2CS/Ir/FloatEvaluator.cs", "src/Cpp2CS/Ir/FloatFused.cs",
           "src/Cpp2CS/Ir/MirValidator.cs",
           "src/Cpp2CS/Validation/FloatChecks.cs", "tests/FloatCoreHarness/FloatCoreHarness.csproj",
           "tests/FloatCoreHarness/Program.cs", "tests/float_core_differential.py", "tests/x64_float_native.py"]
report = {"nativeCases": count, "nativeCasesByKind": native_counts,
          "armSimulatorCases": sum(arm_counts.values()), "armSimulatorCasesByKind": arm_counts,
          "unicornVersion": unicorn.__version__, "capstoneVersion": capstone.__version__, "coreChecks": core_checks,
          "harnessSha256": hashlib.sha256(DLL.read_bytes()).hexdigest(),
          "sourceSha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in sources},
          "scope": "Direct core, independent of lifter/MIR interpreter: Windows x64 synthetic legacy SSE hardware result+MXCSR; Arm64 synthetic instruction Unicorn result+FPSR; all exceptions masked. Arm64 is simulator evidence, not physical hardware or proof over all inputs."}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(f"native core cases passed: {count}; report: {args.output}")
