"""锁定 RMW/CAS 数据、flags 的 Unicorn/本机对照及单事件/故障边界。"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import subprocess

from unicorn import Uc, UC_ARCH_X86, UC_MODE_64
from unicorn import x86_const as xc
from x64_atomic_native import FORMS, NativeAtomicOracle


ROOT = Path(__file__).resolve().parents[1]
CODE, DATA = 0x10000, 0x50000
GPRS = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"] + [f"r{i}" for i in range(8, 16)]
FLAGS = {"cf": 0, "pf": 2, "af": 4, "zf": 6, "sf": 7, "df": 10, "of": 11}
parser = argparse.ArgumentParser()
parser.add_argument("--dll", type=Path, default=ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll")
parser.add_argument("--output", type=Path, default=ROOT / "artifacts/x64-atomic-differential.json")
args = parser.parse_args()
server = subprocess.Popen(["dotnet", str(args.dll), "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
cpu = Uc(UC_ARCH_X86, UC_MODE_64)
cpu.ctl_set_cpu_model(xc.UC_CPU_X86_HASWELL)
cpu.mem_map(CODE, 0x1000)
cpu.mem_map(DATA, 0x1000)
native = NativeAtomicOracle()
rng = random.Random(0xA706)
counts = Counter()
forms = set()


def call(code, slots, data, *, permissions=True, **extra):
    request = dict(arch="x64", bytes=code, address=hex(CODE), slots={key: hex(value) for key, value in slots.items()},
                   memory=[dict(address=hex(DATA), bytes=data.hex())], roundtrip=counts["differential"] % 17 == 0)
    if permissions: request["writePermissions"] = [dict(address=hex(DATA), size=len(data), allowed=True)]
    request.update(extra)
    server.stdin.write(json.dumps(request) + "\n")
    server.stdin.flush()
    line = server.stdout.readline()
    assert line, (server.poll(), code)
    return json.loads(line)


def state():
    slots = {name: rng.getrandbits(64) for name in GPRS}
    slots.update({name: rng.getrandbits(1) for name in FLAGS})
    slots.update(rdi=DATA + 256, df=0)
    return slots


def check(code, width, family, name, iteration):
    slots, data = state(), bytearray(rng.randbytes(512))
    mask = (1 << width) - 1
    edges = (0, 1, 15, 16, mask, mask >> 1, (mask >> 1) + 1)
    old = edges[iteration % len(edges)] if iteration < 28 else rng.getrandbits(width)
    data[256:256 + width // 8] = old.to_bytes(width // 8, "little")
    slots["rcx"] = edges[(iteration // 7) % len(edges)] & ((1 << 64) - 1) if iteration < 49 else rng.getrandbits(64)
    if name in ("bts", "btr", "btc"):
        slots["rcx"] = ((-131, -65, -33, -1, 0, 1, 15, 31, 63, 64, 127, 191)[iteration % 12]) & ((1 << 64) - 1)
    if name == "cmpxchg":
        slots["rax"] = (rng.getrandbits(64) & ~mask) | (old if iteration % 2 else (old ^ 1))
    elif name in ("cmpxchg8b", "cmpxchg16b"):
        half = width // 2
        expected = old if iteration % 2 else old ^ 1
        slots["rax"] = (rng.getrandbits(64) & ~((1 << half) - 1)) | (expected & ((1 << half) - 1))
        slots["rdx"] = (rng.getrandbits(64) & ~((1 << half) - 1)) | (expected >> half)
    slots["cf"] = iteration % 2
    for register in GPRS: cpu.reg_write(getattr(xc, "UC_X86_REG_" + register.upper()), slots[register])
    cpu.reg_write(xc.UC_X86_REG_EFLAGS, 2 | sum(slots[name] << bit for name, bit in FLAGS.items()))
    raw = bytes.fromhex(code)
    cpu.mem_write(CODE, raw)
    cpu.mem_write(DATA, bytes(data))
    cpu.emu_start(CODE, CODE + len(raw), count=1)
    hardware, hardware_flags, hardware_memory = native.run(code, slots, data)
    response = call(code, slots, data)
    assert response["supported"] and response["Outcome"] == "Normal" and response["support"] == "NormalPathOnly", (code, response)
    actual = {key: int(value, 16) for key, value in response["slots"].items()}
    for register in GPRS:
        expected = cpu.reg_read(getattr(xc, "UC_X86_REG_" + register.upper()))
        if register in hardware:
            if expected != hardware[register]:
                assert name == "cmpxchg" and width == 32 and register == "rax" or name == "cmpxchg8b" and register in ("rax", "rdx"), ("unexpected oracle register mismatch", code, register, expected, hardware[register])
                assert iteration % 2 and expected == hardware[register] & 0xffffffff, ("unexpected accumulator mismatch", code, register)
                counts["unicornCmpxchgUpperDifferences"] += 1
            expected = hardware[register]
        assert actual[register] == expected, (code, register, actual[register], expected, slots)
    flag_mask = sum(1 << bit for bit in FLAGS.values())
    if family == "logical": flag_mask &= ~0x10
    if family == "bittest": flag_mask &= 0x441
    actual_flags = sum(actual[name] << bit for name, bit in FLAGS.items())
    assert actual_flags & flag_mask == hardware_flags & flag_mask, (code, "flags", actual_flags, hardware_flags, old, slots)
    if hardware_flags & flag_mask != cpu.reg_read(xc.UC_X86_REG_EFLAGS) & flag_mask:
        assert name == "neg", ("unexpected Unicorn flag disagreement", code, hardware_flags, cpu.reg_read(xc.UC_X86_REG_EFLAGS))
        counts["unicornLockedNegFlagDifferences"] += 1
    actual_memory = bytes(response["memory"][f"0x{DATA+i:X}"] for i in range(512))
    assert actual_memory == hardware_memory == bytes(cpu.mem_read(DATA, 512)), (code, "memory", slots)
    assert len(response["events"]) == 1 and len(response["Accesses"]) == 1, response
    event = response["events"][0]
    assert event["Kind"] == "AtomicRmw" and event["Order"] == 3 and event["AtomicWidth"] == width, event
    assert event["Outcome"] in ("Completed", "Exchanged", "CompareFailed"), response
    where = event["Address"]
    before = int.from_bytes(data[where-DATA:where-DATA+width//8], "little")
    after = int.from_bytes(actual_memory[where-DATA:where-DATA+width//8], "little")
    assert int(event["PreviousData"], 16) == before and int(event["Data"], 16) == after, response
    counts["differential"] += 1
    forms.add(code)


for code, width, family, name in FORMS:
    for iteration in range(64): check(code, width, family, name, iteration)

# A stopped atomic event commits neither bytes nor flags/registers. Failed CAS still requires a write.
for code, width, _family, name in FORMS:
    slots, data = state(), bytearray(rng.randbytes(512))
    if name in ("bts", "btr", "btc"): slots["rcx"] = 1
    for mode in ("unknown", "denied", "missing"):
        fragment = data[:256 + width // 8 - 1] if mode == "missing" else data
        extra = {"writePermissions": [dict(address=hex(DATA), size=512, allowed=mode != "denied")]} if mode != "unknown" else {}
        response = call(code, slots, fragment, permissions=False, **extra)
        assert response["Outcome"] == ("UnmodeledEnvironmentStop" if mode == "unknown" else "UnmodeledFaultStop"), (code, mode, response)
        assert {key: int(value, 16) for key, value in response["slots"].items()} == slots, (code, mode, "register commit")
        assert bytes(response["memory"][f"0x{DATA+i:X}"] for i in range(len(fragment))) == fragment, (code, mode, "partial write")
        assert len(response["events"]) == 1 and response["events"][0]["PreviousData"] is None, response
        counts["faultContracts"] += 1

slots, data = state(), bytes(512)
for code in ("f048010f", "f0480fb10f", "48870f"):
    for scheduled in (0, 1):
        response = call(code, slots, data, reservation=dict(address=hex(DATA+256), sizeBytes=8),
                        schedule=[dict(beforeEvent=scheduled, address=hex(DATA+256), bytes="8877665544332211", invalidateExclusive=False)])
        assert response["Outcome"] == "Normal" and response["reservation"] is None, response
        assert len(response["events"]) == 1 and len(response["appliedSchedule"]) == 1-scheduled and len(response["remainingSchedule"]) == scheduled, response
        assert int(response["events"][0]["PreviousData"], 16) == (0x1122334455667788 if scheduled == 0 else 0), response
        counts["scheduleContracts"] += 1

for address in (0x800000000000, 0xfffffffffffffff9, DATA + 257):
    slots = state()
    slots["rdi"] = address
    response = call("f0480fc70f", slots, bytes(512))
    assert response["Outcome"] == "UnmodeledFaultStop" and response["events"] == [] and response["Accesses"] == [], response
    counts["addressContracts"] += 1

# HLE-disabled profile: only valid decoder-recognized hints may preserve the locked operation.
for code in ("f2f048010f", "f3f048010f", "f248870f", "f348870f"):
    slots = state()
    response = call(code, slots, bytes(512))
    assert response["supported"] and response["Outcome"] == "Normal" and len(response["events"]) == 1, response
    plain = call(code[2:], slots, bytes(512))
    assert all(response[field] == plain[field] for field in ("slots", "memory", "events", "Accesses")), code
    counts["hleContracts"] += 1
for code in ("f04801c8", "f0f8", "f0f9", "f00fa30f", "f248010f", "f348010f", "f048890f"):
    response = call(code, {}, b"")
    assert not response["supported"], (code, response)
    counts["rejected"] += 1

server.stdin.close()
assert server.wait() == 0
native.close()
report = dict(implementationAssembly=str(args.dll.resolve()), implementationAssemblySha256=hashlib.sha256(args.dll.read_bytes()).hexdigest().upper(),
              counts=dict(counts), encodings=len(forms), scope="synthetic scalar data/flags and explicit event contracts; not concurrency or hardware exception-delivery proof")
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report))
