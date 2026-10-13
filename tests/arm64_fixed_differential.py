"""ARM64 定点转换：直接核心、生产 MIR 与独立 Unicorn 合成指令对照。"""

import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess

import capstone
import unicorn
from unicorn import arm64_const as ar
from arm64_fixture import with_arm_fixture_environment, checked_arm_fixture_result


ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--dll", type=Path, default=ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll")
parser.add_argument("--core-dll", type=Path, default=ROOT / "tests/FloatCoreHarness/bin/Release/net10.0/FloatCoreHarness.dll")
parser.add_argument("--output", type=Path, default=ROOT / "artifacts/arm64-fixed-differential.json")
args = parser.parse_args()
product = subprocess.Popen(["dotnet", str(args.dll), "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
core = subprocess.Popen(["dotnet", str(args.core_dll)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
cpu = unicorn.Uc(unicorn.UC_ARCH_ARM64, unicorn.UC_MODE_ARM)
cpu.mem_map(0x10000, 0x20000)
cpu.reg_write(ar.UC_ARM64_REG_CPACR_EL1, 0x300000)
decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM)
addresses = {}
rng = random.Random(0xF1CED04)
counts = Counter()
core_cases = 0
classification = Counter()
controls = [(rc << 22) | (fz << 24) | (dn << 25)
            for rc, fz, dn in itertools.product(range(4), range(2), range(2))]


def exchange(server, request):
    server.stdin.write(json.dumps(with_arm_fixture_environment(request)) + "\n")
    server.stdin.flush()
    response = server.stdout.readline()
    assert response, ("server exited", server.poll(), request)
    return checked_arm_fixture_result(request, json.loads(response))


def float_values(width, integer_width, fraction):
    precision, bias = (23, 127) if width == 32 else (52, 1023)
    sign = 1 << (width - 1)
    infinity = (2 * bias + 1) << precision
    values = [0, sign, 1, sign | 1, (1 << precision) - 1, 1 << precision,
              infinity, sign | infinity, infinity | 1, sign | infinity | 3,
              infinity | (1 << (precision - 1)) | 11, infinity - 1]
    for exponent in (-fraction - 1, -fraction, integer_width - fraction - 1, integer_width - fraction):
        bits = (bias + exponent) << precision
        values.extend((bits - 1, bits, bits + 1, sign | (bits - 1), sign | bits, sign | (bits + 1)))
    return values


def integer_values(width):
    mask = (1 << width) - 1
    values = [0, 1, 2, 3, mask, mask - 1, 1 << (width - 1), (1 << (width - 1)) - 1]
    for exponent in (23, 24, 31, 32, 52, 53, 63):
        if exponent < width:
            values.extend(((1 << exponent) + delta) & mask for delta in (-1, 1))
    return values


def core_result(kind, input_width, output_width, fraction, value, control):
    global core_cases
    result = exchange(core, dict(arch="Arm64", kind=kind, width=input_width, resultWidth=output_width,
                                a=f"{value:x}", b="0", control=control, fractionBits=fraction,
                                rounding="Current" if kind.startswith("From") else "TowardZero"))
    core_cases += 1
    assert result["TrapFlags"] == result["Flags"], result
    return int(result["bits"], 16), result["Flags"]


def execute(word, kind, input_width, output_width, fraction, values, control, general, rd, source_zero=False):
    code = word.to_bytes(4, "little")
    if word not in addresses:
        address = 0x10000 + 4 * len(addresses)
        assert address < 0x30000
        decoded = list(decoder.disasm(code, address))
        mnemonic = {"FromSigned": "scvtf", "FromUnsigned": "ucvtf", "ToSigned": "fcvtzs", "ToUnsigned": "fcvtzu"}[kind]
        assert len(decoded) == 1 and decoded[0].mnemonic == mnemonic, (hex(word), mnemonic, decoded)
        cpu.mem_write(address, code)
        addresses[word] = address
    address = addresses[word]
    from_integer = kind.startswith("From")
    rn = (word >> 5) & 31
    packed_source = sum(value << (input_width * index) for index, value in enumerate(values))
    slots = {"x0": rng.getrandbits(64), "x1": rng.getrandbits(64), "x8": rng.getrandbits(64),
             "v0": rng.getrandbits(128), "v1": rng.getrandbits(128), "v31": rng.getrandbits(128),
             "fpcr": control, "fpsr": rng.getrandbits(8) & 0x9F | (rng.getrandbits(1) << 27)}
    if general and from_integer:
        if not source_zero:
            slots[f"x{rn}"] = values[0] | (rng.getrandbits(32) << 32 if input_width == 32 else 0)
    else:
        slots[f"v{rn}"] = packed_source | (rng.getrandbits(128 - len(values) * input_width) << (len(values) * input_width))
    for slot, value in slots.items():
        register = getattr(ar, "UC_ARM64_REG_Q" + slot[1:]) if slot.startswith("v") else getattr(ar, "UC_ARM64_REG_" + slot.upper())
        cpu.reg_write(register, value)
    cpu.emu_start(address, address + 4, count=1)
    destination = f"x{rd}" if general and not from_integer else f"v{rd}"
    expected_data, flags = 0, 0
    for index, value in enumerate(values):
        bits, lane_flags = core_result(kind, input_width, output_width, fraction, 0 if source_zero else value, control)
        expected_data |= bits << (output_width * index)
        flags |= lane_flags
    expected_fpsr = slots["fpsr"] | (flags & 31) | ((flags & 32) << 2)
    actual_fpsr = cpu.reg_read(ar.UC_ARM64_REG_FPSR)
    assert actual_fpsr == expected_fpsr, (hex(word), kind, fraction, values, hex(control), flags, hex(actual_fpsr), hex(expected_fpsr))
    if not (general and not from_integer and rd == 31):
        register = getattr(ar, "UC_ARM64_REG_X" + str(rd)) if general and not from_integer else getattr(ar, "UC_ARM64_REG_Q" + str(rd))
        hardware = cpu.reg_read(register)
        assert hardware == expected_data, (hex(word), kind, fraction, values, hex(control), hex(hardware), hex(expected_data))
    response = exchange(product, dict(arch="arm64", bytes=code.hex(), address=hex(address),
                        slots={name: hex(value) for name, value in slots.items()}, roundtrip=sum(counts.values()) % 19 == 0))
    assert response["supported"] and response["Outcome"] == "Normal", (hex(word), response)
    assert int(response["next"], 16) == address + 4, response
    expected_slots = dict(slots, fpsr=expected_fpsr)
    if not (general and not from_integer and rd == 31):
        expected_slots[destination] = expected_data
    actual_slots = {name: int(value, 16) for name, value in response["slots"].items()}
    assert actual_slots == expected_slots, (hex(word), kind, fraction, values, control, actual_slots, expected_slots)
    assert response["Accesses"] == [], response
    counts[("general." if general else "simd.") + kind] += 1


for integer_width, float_width, from_integer, unsigned in itertools.product((32, 64), (32, 64), (False, True), (False, True)):
    kind = ("From" if from_integer else "To") + ("Unsigned" if unsigned else "Signed")
    input_width, output_width = (integer_width, float_width) if from_integer else (float_width, integer_width)
    for fraction in range(1, integer_width + 1):
        base = (0x1E020000 if from_integer else 0x1E180000) | ((integer_width == 64) << 31) | ((float_width == 64) << 22) | (unsigned << 16) | ((64 - fraction) << 10)
        values = integer_values(integer_width) if from_integer else float_values(float_width, integer_width, fraction)
        values += [rng.getrandbits(input_width) for _ in range(4)]
        selected_controls = controls if fraction in (1, 10, integer_width - 1, integer_width) else [0]
        for control in selected_controls:
            for index, value in enumerate(values):
                rd = 31 if index % 11 == 0 else 1 if from_integer and index % 3 == 0 else 0 if from_integer else 8
                source_zero = from_integer and index % 13 == 0
                word = base | ((31 if source_zero else 1) << 5) | rd
                execute(word, kind, input_width, output_width, fraction, [value], control, True, rd, source_zero)
    print(f"fixed general {integer_width}/{float_width} {kind}: {sum(counts.values())} passed", flush=True)

for width, scalar, q, from_integer, unsigned in itertools.product((32, 64), (False, True), range(2), (False, True), (False, True)):
    if scalar and not q or not scalar and width == 64 and not q:
        continue
    kind = ("From" if from_integer else "To") + ("Unsigned" if unsigned else "Signed")
    lanes = 1 if scalar else (128 if q else 64) // width
    for fraction in range(1, width + 1):
        base = (0x0F00E400 if from_integer else 0x0F00FC00) | (q << 30) | (scalar << 28) | (unsigned << 29) | ((width * 2 - fraction) << 16) | (1 << 5)
        values = integer_values(width) if from_integer else float_values(width, width, fraction)
        values += [rng.getrandbits(width) for _ in range(4)]
        selected_controls = controls if fraction in (1, 10, width - 1, width) else [0]
        for control in selected_controls:
            for index in range(len(values)):
                rd = (0, 1, 31)[index % 3]
                execute(base | rd, kind, width, width, fraction,
                        [values[(index + lane * 5) % len(values)] for lane in range(lanes)], control, False, rd)
    print(f"fixed SIMD {width} scalar={scalar} Q={q} {kind}: {sum(counts.values())} passed", flush=True)

# The sampled game's FCVTZS W8, S0, #10 is executed with synthetic input.
execute(0x1E18D808, "ToSigned", 32, 32, 10, [0x3FC00000], 0, True, 8)

# Exhaust the immediate and size fields, including FP16 and reserved forms.
for sf, ftype, opcode, scale in itertools.product(range(2), range(4), (2, 3, 24, 25), range(64)):
    word = 0x1E000020 | (sf << 31) | (ftype << 22) | (opcode << 16) | (scale << 10)
    result = exchange(product, dict(arch="arm64", bytes=word.to_bytes(4, "little").hex(), address="0x10000", evaluate=False))
    expected = ftype < 2 and (sf or scale >= 32)
    assert result["supported"] == bool(expected), (hex(word), result, expected)
    classification["general.accepted" if expected else "general.rejected"] += 1
for scalar, q, unsigned, opcode, immediate in itertools.product(range(2), range(2), range(2), (57, 63), range(128)):
    word = 0x0F000020 | (scalar << 28) | (q << 30) | (unsigned << 29) | (immediate << 16) | (opcode << 10)
    result = exchange(product, dict(arch="arm64", bytes=word.to_bytes(4, "little").hex(), address="0x10000", evaluate=False))
    expected = immediate >= 32 and (q or not scalar and immediate < 64)
    if immediate < 8 and result["supported"] and not result["Form"].endswith("fp.fixed-simd"):
        classification["simd.modified-immediate-alias"] += 1
        continue
    assert result["supported"] == bool(expected), (hex(word), result, expected)
    classification["simd.accepted" if expected else "simd.rejected"] += 1

guard_cases = [
    (0x1E18D828, {"v1": 0x7FC12345}, 1 << 8),
    (0x1E02FC20, {"x1": (1 << 24) + 1}, 1 << 12),
    (0x9E180020, {"v1": 1}, (1 << 24) | (1 << 15)),
    (0x4F36FC20, {"v1": 0x7FC12345 << 96}, 1 << 8),
]
for word, source, control in guard_cases:
    slots = dict(x0=0xDEADBEEF, x8=0xCAFE, v0=(1 << 128) - 1, fpsr=0, fpcr=control, **source)
    result = exchange(product, dict(arch="arm64", bytes=word.to_bytes(4, "little").hex(), address="0x10000",
                                   slots={name: hex(value) for name, value in slots.items()}, roundtrip=True))
    assert result["supported"] and result["Outcome"] == "UnmodeledFaultStop", result
    assert {name: int(value, 16) for name, value in result["slots"].items()} == slots, result

product.stdin.close()
core.stdin.close()
assert product.wait() == 0 and core.wait() == 0
sources = ["src/Cpp2CS/Ir/Model.cs", "src/Cpp2CS/Ir/FloatEvaluator.cs", "src/Cpp2CS/Ir/MirValidator.cs",
           "src/Cpp2CS/Arm64/Arm64Floating.cs", "src/Cpp2CS/Arm64/Arm64Lifter.cs", "src/Cpp2CS/Validation/FloatChecks.cs",
           "tests/FloatCoreHarness/FloatCoreHarness.csproj", "tests/FloatCoreHarness/Program.cs", "tests/arm64_fixed_differential.py", "tests/arm64_fixture.py"]
report = dict(cases=sum(counts.values()), casesByForm=counts, coreCases=core_cases,
              classification=classification, guardCases=len(guard_cases), unicorn=unicorn.__version__, capstone=capstone.__version__,
              productSha256=hashlib.sha256(args.dll.read_bytes()).hexdigest(), coreSha256=hashlib.sha256(args.core_dll.read_bytes()).hexdigest(),
              sourceSha256={name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in sources},
              scope="All fraction-bit encodings; 32/64 general and SIMD conversions, aliases, masked FP status and explicit guard stops. Independent Unicorn simulator, not physical ARM hardware or proof over all inputs.")
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({key: value for key, value in report.items() if key not in ("sourceSha256", "casesByForm")}))
