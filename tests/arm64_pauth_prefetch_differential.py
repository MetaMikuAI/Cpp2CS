"""生产 MIR 对照启用 PAuth 的 Unicorn；预取只验证架构状态和保留的 hint 事件。"""

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
from unicorn import arm64_const as arm


ROOT = Path(__file__).resolve().parents[1]
CODE = 0x10000
MASK64 = (1 << 64) - 1
parser = argparse.ArgumentParser()
parser.add_argument("--dll", type=Path, default=ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll")
parser.add_argument("--output", type=Path, default=ROOT / "artifacts/arm64-pauth-prefetch-differential.json")
args = parser.parse_args()
server = subprocess.Popen(["dotnet", str(args.dll), "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
cpu = unicorn.Uc(unicorn.UC_ARCH_ARM64, unicorn.UC_MODE_ARM)
cpu.ctl_set_cpu_model(arm.UC_CPU_ARM64_MAX)
cpu.mem_map(CODE, 0x1000)
# EL0 AArch64, permitted PAuth key access/use, 48-bit VA and TBI disabled.
cpu.cpr_write(3, 4, 1, 1, 0, (1 << 41) | (1 << 40) | (1 << 31))
cpu.cpr_write(3, 6, 1, 1, 0, (1 << 17) | (1 << 16) | (1 << 10) | 1)
cpu.cpr_write(3, 0, 2, 0, 2, 16 | (16 << 16))
cpu.reg_write(arm.UC_ARM64_REG_PSTATE, 0)
isar1 = cpu.cpr_read(3, 0, 0, 6, 1)
assert (isar1 >> 4) & 15 == 1, hex(isar1)
assert cpu.cpr_read(3, 0, 0, 6, 2) == 0
decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM)
rng = random.Random(0xA6405)
counts = Counter()
oracle_differences = Counter()
classification = Counter()
registers = {f"x{i}": getattr(arm, f"UC_ARM64_REG_X{i}") for i in range(31)}
registers.update({f"v{i}": getattr(arm, f"UC_ARM64_REG_Q{i}") for i in range(32)})
registers.update(sp=arm.UC_ARM64_REG_SP, fpcr=arm.UC_ARM64_REG_FPCR, fpsr=arm.UC_ARM64_REG_FPSR)
flags = {"n": 31, "z": 30, "c": 29, "v": 28}
words = [0xD503211F, 0xD503215F, 0xD503219F, 0xD50321DF,
         0xD503231F, 0xD503233F, 0xD503235F, 0xD503237F,
         0xD503239F, 0xD50323BF, 0xD50323DF, 0xD50323FF]


def request(word, slots=None, **extra):
    value = dict(arch="arm64", bytes=word.to_bytes(4, "little").hex(), address=hex(CODE), **extra)
    if slots is not None:
        value["slots"] = {key: hex(bits) for key, bits in slots.items()}
        value["codePages"] = [dict(address=hex(CODE), guarded=False)]
    server.stdin.write(json.dumps(value) + "\n")
    server.stdin.flush()
    line = server.stdout.readline()
    assert line, ("server exited", server.poll(), value)
    return json.loads(line)


def initial_slots():
    slots = {name: rng.getrandbits(128 if name.startswith("v") else 64) for name in registers}
    slots.update(fpcr=0x03400000, fpsr=rng.getrandbits(5) | (rng.randrange(2) << 7), sp=rng.getrandbits(64) & ~15)
    slots.update({name: rng.randrange(2) for name in flags})
    slots.update(apia_key=rng.getrandbits(128), apib_key=rng.getrandbits(128),
                 pauth_ia_enabled=rng.randrange(2), pauth_ib_enabled=rng.randrange(2), btype=0, bti_bt0=0)
    return slots


def load_cpu(slots):
    for name, register in registers.items():
        cpu.reg_write(register, slots[name])
    cpu.reg_write(arm.UC_ARM64_REG_NZCV, sum(slots[name] << bit for name, bit in flags.items()))
    cpu.cpr_write(3, 0, 1, 0, 0, 0xC50838 | (slots["pauth_ia_enabled"] << 31) | (slots["pauth_ib_enabled"] << 30))
    for key_index, name in enumerate(("apia_key", "apib_key")):
        cpu.cpr_write(3, 0, 2, 1, key_index * 2, slots[name] & MASK64)
        cpu.cpr_write(3, 0, 2, 1, key_index * 2 + 1, slots[name] >> 64)


def run_cpu(word, slots):
    load_cpu(slots)
    cpu.mem_write(CODE, word.to_bytes(4, "little"))
    cpu.ctl_remove_cache(CODE, CODE + 4)
    cpu.emu_start(CODE, CODE + 4, count=1)
    result = dict(slots)
    result.update({name: cpu.reg_read(register) for name, register in registers.items()})
    nzcv = cpu.reg_read(arm.UC_ARM64_REG_NZCV)
    result.update({name: (nzcv >> bit) & 1 for name, bit in flags.items()})
    assert cpu.reg_read(arm.UC_ARM64_REG_PC) == CODE + 4
    return result


def check(word, slots, label, prefetch_address=None):
    expected = run_cpu(word, slots)
    malformed = False
    if word in words and not ((word >> 5) & 4):
        selector = (word >> 5) & 127
        destination = "x17" if selector & 0x18 == 8 else "x30"
        enabled = slots["pauth_ib_enabled" if selector & 2 else "pauth_ia_enabled"]
        pointer = slots[destination]
        malformed = enabled and pointer >> 48 not in (0, 65535)
        if malformed:
            canonical = dict(slots)
            canonical[destination] = (pointer & ((1 << 48) - 1)) | (0xFFFF000000000000 if pointer >> 63 else 0)
            baseline = run_cpu(word, canonical)[destination]
            # Unicorn 2.1.2 predates QEMU's corrected InsertPAC corruption bit.
            assert expected[destination] == baseline ^ (1 << 63), (hex(word), hex(pointer), hex(expected[destination]), hex(baseline))
            expected[destination] = baseline ^ (1 << 62)
    result = request(word, slots, roundtrip=True)
    assert result["supported"] and result["Outcome"] == "Normal", (hex(word), label, result)
    actual = {name: int(value, 16) for name, value in result["slots"].items()}
    assert actual == expected, (hex(word), label, {name: (hex(slots[name]), hex(expected[name]), hex(actual[name]))
                                                for name in expected if expected[name] != actual[name]})
    assert int(result["next"], 16) == CODE + 4
    assert not result["Accesses"] and not result["memory"] and not result["Choices"], result
    if prefetch_address is None:
        assert not result["events"] and result["support"] == "NormalPathOnly", result
    else:
        assert result["support"] == "NormalPathOnly" and len(result["events"]) == 1, result
        event = result["events"][0]
        assert event["Kind"] == "Prefetch" and event["Address"] == prefetch_address & MASK64, event
        assert event["Option"] == word & 31 and event["SizeBytes"] == 0 and event["Outcome"] == "Completed", event
    if malformed:
        oracle_differences[label + ".noncanonical-corruption-bit"] += 1
    else:
        counts[label] += 1


# Include canonical low/high pointers, malformed extension bits and every authenticated PAC bit.
pointers = [0, 1, (1 << 48) - 1, 0xFFFF000000000000, MASK64, 1 << 55, 1 << 63, 1 << 48,
            0x12345678, 0xFFFF123456789ABC]
for word in words:
    instruction = next(decoder.disasm(word.to_bytes(4, "little"), CODE))
    selector = (word >> 5) & 127
    destination = "x17" if selector & 0x18 == 8 else "x30"
    key_enable = "pauth_ib_enabled" if selector & 2 else "pauth_ia_enabled"
    authenticate = bool(selector & 4)
    for index in range(256):
        slots = initial_slots()
        slots[destination] = pointers[index] if index < len(pointers) else rng.getrandbits(64)
        if not authenticate and index >= len(pointers) and index % 3 == 0:
            slots[destination] = (slots[destination] & ((1 << 48) - 1)) | (0xFFFF000000000000 if index & 1 else 0)
        slots[key_enable] = int(index % 4 != 0)
        label = instruction.mnemonic + (".enabled" if slots[key_enable] else ".disabled")
        if authenticate and slots[key_enable] and index % 3 != 0:
            pointer = slots[destination] & ((1 << 48) - 1)
            if index & 1:
                pointer |= 0xFFFF000000000000
            slots[destination] = pointer
            signed = run_cpu(word & ~(4 << 5), slots)[destination]
            slots[destination] = signed
            if index % 3 == 2:
                slots[destination] ^= 1 << ([*range(48, 55), *range(56, 64)][index % 15])
                label += ".corrupt"
            else:
                label += ".valid"
        check(word, slots, label)

# Ordinary prefetch hints do not read byte memory, including noncanonical/unmapped addresses.
for hint, rn, immediate in itertools.product(range(32), (0, 31), (0, 1, 4095)):
    slots = initial_slots()
    basis = slots["sp" if rn == 31 else f"x{rn}"]
    check(0xF9800000 | (immediate << 10) | (rn << 5) | hint, slots, "prfm.unsigned", basis + immediate * 8)
for hint, rn, immediate in itertools.product(range(32), (0, 31), (-256, -1, 0, 255)):
    slots = initial_slots()
    basis = slots["sp" if rn == 31 else f"x{rn}"]
    check(0xF8800000 | ((immediate & 511) << 12) | (rn << 5) | hint, slots, "prfum", basis + immediate)
for hint, immediate in itertools.product(range(32), (-(1 << 18), -1, 0, (1 << 18) - 1)):
    check(0xD8000000 | ((immediate & 0x7FFFF) << 5) | hint, initial_slots(), "prfm.literal", CODE + immediate * 4)
for hint, option, shifted, rn, rm in itertools.product(range(32), (2, 3, 6, 7), (0, 1), (0, 31), (0, 1, 31)):
    slots = initial_slots()
    # Include overlap, zero register and negative signed offsets.
    bits = 64 if option & 1 else 32
    offset = 0 if rm == 31 else slots[f"x{rm}"] & ((1 << bits) - 1)
    if option & 4 and offset >> (bits - 1):
        offset -= 1 << bits
    basis = slots["sp" if rn == 31 else f"x{rn}"]
    word = 0xF8A00800 | (rm << 16) | (option << 13) | (shifted << 12) | (rn << 5) | hint
    check(word, slots, "prfm.register", basis + (offset << (3 if shifted else 0)))

for option, rm, rn, hint, shifted in itertools.product(range(8), (0, 31), (0, 31), range(32), (0, 1)):
    word = 0xF8A00800 | (rm << 16) | (option << 13) | (shifted << 12) | (rn << 5) | hint
    decoded = list(decoder.disasm(word.to_bytes(4, "little"), CODE))
    result = request(word, evaluate=False)
    assert result["supported"] == bool(option & 2), (hex(word), result)
    assert bool(decoded) == result["supported"], (hex(word), result, decoded)
    classification["prefetch.valid" if result["supported"] else "prefetch.reserved"] += 1
for selector in range(128):
    word = 0xD503201F | (selector << 5)
    result = request(word, evaluate=False)
    if result["supported"] and result["Form"] == "arm64.pointer-authentication":
        assert word in words, (hex(word), result)
        classification["pauth.hint"] += 1

server.stdin.close()
assert server.wait() == 0
summary = dict(cases=sum(counts.values()), by_form=dict(sorted(counts.items())), classification=dict(classification),
               official_relation_contracts=sum(oracle_differences.values()), known_oracle_differences=dict(oracle_differences),
               oracle_difference="Unicorn 2.1.2 flips bit63 for noncanonical signing; Arm InsertPAC and current QEMU specify bit62. These cases compare canonical emulator signature plus the official bit62 relation, and are excluded from strict differential count.",
               seed=hex(0xA6405), unicorn=unicorn.__version__, capstone=capstone.__version__,
               cpu_model="UC_CPU_ARM64_MAX", isar1=hex(isar1), isar2="0x0",
               profile="EL0 AArch64, PAuth permitted, classic QARMA5, VA48, TBI0, explicit EnIA/EnIB and keys",
               boundary="Independent emulator comparison; does not establish hardware or target runtime configuration; cache effects are not modeled",
               dll_sha256=hashlib.sha256(args.dll.read_bytes()).hexdigest(),
               test_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
print(json.dumps(summary, ensure_ascii=False))
