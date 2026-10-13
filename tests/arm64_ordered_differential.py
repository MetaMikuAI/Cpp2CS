"""ARM64 有序/独占访存：合成指令数据对照与显式环境事件契约检查。"""

import argparse
import base64
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
from arm64_fixture import with_arm_fixture_environment, checked_arm_fixture_result


ROOT = Path(__file__).resolve().parents[1]
CODE = 0x10000
MEMORY = 0x30000
parser = argparse.ArgumentParser()
parser.add_argument("--dll", type=Path, default=ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll")
parser.add_argument("--output", type=Path, default=ROOT / "artifacts/arm64-ordered-differential.json")
args = parser.parse_args()
server = subprocess.Popen(["dotnet", str(args.dll), "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
cpu = unicorn.Uc(unicorn.UC_ARCH_ARM64, unicorn.UC_MODE_ARM)
cpu.mem_map(CODE, 0x10000)
cpu.mem_map(MEMORY, 0x10000)
decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM)
rng = random.Random(0x0ADE05)
counts = Counter()
classification = Counter()
contract_checks = 0


def exchange(request):
    server.stdin.write(json.dumps(with_arm_fixture_environment(request)) + "\n")
    server.stdin.flush()
    line = server.stdout.readline()
    assert line, ("server exited", server.poll(), request)
    return checked_arm_fixture_result(request, json.loads(line))


def request(word, slots=None, data=None, **extra):
    value = dict(arch="arm64", bytes=word.to_bytes(4, "little").hex(), address=hex(CODE), **extra)
    if slots is not None:
        value["slots"] = {key: hex(bits) for key, bits in slots.items()}
    if data is not None:
        value["memory"] = [dict(address=hex(MEMORY), bytes=data.hex())]
    response = exchange(value)
    if "schedule" in extra:
        applied = response["appliedSchedule"]
        assert len(applied) == len(extra["schedule"]) and response["remainingSchedule"] == [], response
        for actual, expected in zip(applied, extra["schedule"]):
            assert actual["BeforeEvent"] == expected["beforeEvent"], response
            assert actual["Address"] == (int(expected["address"], 16) if "address" in expected else None), response
            assert base64.b64decode(actual["Bytes"]) == bytes.fromhex(expected.get("bytes", "")), response
            assert actual["InvalidateExclusive"] == expected["invalidateExclusive"], response
    return response


def encode(width, load, ordered=False, acquire_release=False, pair=False, rt=0, rt2=7, rn=1, rs=3):
    size = {8: 0, 16: 1, 32: 2, 64: 3}[width]
    return (0x08000000 | (size << 30) | (ordered << 23) | (load << 22) | (pair << 21)
            | ((31 if load or ordered else rs) << 16) | ((ordered or acquire_release) << 15)
            | ((rt2 if pair else 31) << 10) | (rn << 5) | rt)


def decode(word):
    instructions = list(decoder.disasm(word.to_bytes(4, "little"), CODE))
    assert len(instructions) == 1, hex(word)
    return instructions[0]


def slots_for(rn):
    slots = {f"x{index}": rng.getrandbits(64) for index in range(31)}
    slots["sp"] = rng.getrandbits(64) & ~15
    slots["sp" if rn == 31 else f"x{rn}"] = MEMORY
    return slots


def cpu_slots(slots):
    for name, value in slots.items():
        cpu.reg_write(getattr(arm, "UC_ARM64_REG_" + name.upper()), value)


def run_cpu(word, slots, data, exclusive_success):
    cpu.mem_write(MEMORY, data)
    cpu_slots(slots)
    cpu.mem_write(CODE, bytes.fromhex("5f3f03d5"))
    cpu.emu_start(CODE, CODE + 4, count=1)
    if exclusive_success:
        pair = bool(word & (1 << 21))
        prefix = encode(8 << (word >> 30), True, pair=pair, rt=29, rt2=30, rn=(word >> 5) & 31)
        cpu.mem_write(CODE + 4, prefix.to_bytes(4, "little"))
        cpu.ctl_remove_cache(CODE + 4, CODE + 8)
        cpu.emu_start(CODE + 4, CODE + 8, count=1)
        cpu_slots(slots)
    cpu.mem_write(CODE + 8, word.to_bytes(4, "little"))
    cpu.ctl_remove_cache(CODE + 8, CODE + 12)
    cpu.emu_start(CODE + 8, CODE + 12, count=1)
    return {name: cpu.reg_read(getattr(arm, "UC_ARM64_REG_" + name.upper())) for name in slots}, bytes(cpu.mem_read(MEMORY, len(data)))


def result_slots(result):
    return {name: int(value, 16) for name, value in result["slots"].items()}


def result_memory(result, size):
    memory = {int(address, 16): value for address, value in result["memory"].items()}
    return bytes(memory[MEMORY + index] for index in range(size))


def check_data(word, success=True):
    instruction = decode(word)
    width = 8 << (word >> 30)
    load, ordered, pair = bool(word & (1 << 22)), bool(word & (1 << 23)), bool(word & (1 << 21))
    size = width // 8 * (2 if pair else 1)
    rn = (word >> 5) & 31
    slots = slots_for(rn)
    data = rng.randbytes(32)
    exclusive_store = not ordered and not load
    reservation = dict(address=hex(MEMORY), sizeBytes=size) if exclusive_store and success else None
    result = request(word, slots, data, reservation=reservation, exclusiveDecisions=[True], roundtrip=True)
    assert result["supported"] and result["Outcome"] == "Normal", (instruction.mnemonic, instruction.op_str, result)
    expected_slots, expected_memory = run_cpu(word, slots, data, exclusive_store and success)
    assert result_slots(result) == expected_slots, (hex(word), instruction.mnemonic, instruction.op_str, result, expected_slots)
    assert result_memory(result, len(data)) == expected_memory, (hex(word), result, expected_memory.hex())
    events = result["events"]
    atomic_width = 64 if load and size == 16 else size * 8
    assert len(events) == size * 8 // atomic_width, (hex(word), events)
    order = (1 if load else 2) if word & (1 << 15) else 0
    for index, event in enumerate(events):
        assert event["Sequence"] == index and event["Order"] == order, (hex(word), event)
        assert event["Address"] == MEMORY + index * (atomic_width // 8), (hex(word), event)
        assert event["SizeBytes"] == atomic_width // 8 and event["AtomicWidth"] == atomic_width, (hex(word), event)
        expected_kind = ("Load" if load else "Store") + ("Exclusive" if not ordered else "")
        assert event["Kind"] == expected_kind, (hex(word), event)
        assert event["Outcome"] == ("Failed" if exclusive_store and not success else "Completed"), (hex(word), event)
        if event["Outcome"] == "Completed":
            offset = index * atomic_width // 8
            assert int(event["Data"], 16) == int.from_bytes(expected_memory[offset:offset + atomic_width // 8], "little"), (hex(word), event)
    expected_reservation = dict(address=hex(MEMORY), sizeBytes=size) if load and not ordered else None
    assert result["reservation"] == expected_reservation, (hex(word), result)
    counts[instruction.mnemonic + (".success" if success else ".no-reservation")] += 1


for width, load, ordered, acqrel in itertools.product((8, 16, 32, 64), (False, True), (False, True), (False, True)):
    if ordered and not acqrel:
        continue
    for rn, rt, rs in itertools.product((0, 1, 31), (0, 1, 7, 31), (3, 31)):
        if not ordered and not load and (rs == rt or rs == rn and rn != 31):
            continue
        word = encode(width, load, ordered, acqrel, rt=rt, rn=rn, rs=rs)
        for iteration in range(5):
            check_data(word)
        if not ordered and not load:
            check_data(word, False)

for width, load, acqrel, rn, rt, rt2, rs in itertools.product((32, 64), (False, True), (False, True), (0, 1, 31), (0, 1, 31), (7, 31), (3, 31)):
    if load and rt == rt2 or not load and (rs in (rt, rt2) or rs == rn and rn != 31):
        continue
    word = encode(width, load, acquire_release=acqrel, pair=True, rt=rt, rt2=rt2, rn=rn, rs=rs)
    for iteration in range(5):
        check_data(word)
    if not load:
        check_data(word, False)

# Classification probes include constrained-unpredictable operand overlaps and non-target LSE forms.
for size, ordered, load, pair, acqrel, rs, rt2 in itertools.product(range(4), range(2), range(2), range(2), range(2), (0, 3, 31), (0, 7, 31)):
    word = 0x08000020 | (size << 30) | (ordered << 23) | (load << 22) | (pair << 21) | (rs << 16) | (acqrel << 15) | (rt2 << 10)
    expected = (bool(acqrel) and not pair and rs == rt2 == 31) if ordered else (
        (size >= 2 if pair else rt2 == 31) and (rs == 31 if load else rs != 0) and not (load and pair and rt2 == 0)
        and not (not load and pair and rs == rt2))
    result = request(word, evaluate=False)
    assert result["supported"] == expected, (hex(word), result, expected)
    classification["accepted" if expected else "rejected"] += 1

for opcode, option in itertools.product((2, 4, 5, 6), range(16)):
    word = 0xD503301F | (opcode << 5) | (option << 8)
    expected = opcode == 2 or opcode == 6 and option == 15 or opcode in (4, 5) and option % 4 != 0
    result = request(word, {}, b"", reservation=dict(address=hex(MEMORY), sizeBytes=8), roundtrip=True)
    assert result["supported"] == expected, (hex(word), result, expected)
    if expected:
        assert result["Outcome"] == "Normal" and result["slots"] == {} and result["memory"] == {}, result
        assert len(result["events"]) == 1, result
        if opcode == 2:
            assert result["reservation"] is None, result
        else:
            spec = result["events"][0]["Barrier"]
            assert spec["Kind"] == {4: 1, 5: 0, 6: 2}[opcode] and spec["Option"] == option, result
            assert spec["Domain"] == (0 if opcode == 6 else (2, 3, 1, 0)[option >> 2]), result
            assert spec["Access"] == (0 if opcode == 6 else option % 4 % 3), result
    classification["barrier.accepted" if expected else "barrier.rejected"] += 1

# Requests carry reservation state explicitly; the environment decides whether an otherwise valid store can pass.
for width, pair in ((8, False), (16, False), (32, False), (64, False), (32, True), (64, True)):
    size = width // 8 * (2 if pair else 1)
    load = encode(width, True, acquire_release=True, pair=pair)
    store = encode(width, False, acquire_release=True, pair=pair)
    slots = slots_for(1)
    data = rng.randbytes(32)
    loaded = request(load, slots, data, roundtrip=True)
    reservation = loaded["reservation"]
    assert reservation == dict(address=hex(MEMORY), sizeBytes=size), loaded
    state = result_slots(loaded)
    for decision, extra in ((False, {}), (True, {"schedule": [dict(beforeEvent=0, invalidateExclusive=True)]}),
                            (True, {"schedule": [dict(beforeEvent=0, address=hex(MEMORY), bytes=data[:1].hex(), invalidateExclusive=False)]})):
        failed = request(store, state, data, reservation=reservation, exclusiveDecisions=[decision], roundtrip=True, **extra)
        expected_slots = dict(state, x3=1)
        assert failed["Outcome"] == "Normal" and result_slots(failed) == expected_slots, failed
        assert result_memory(failed, len(data)) == data and failed["reservation"] is None, failed
        contract_checks += 1
    missing = request(store, state, data, reservation=reservation, roundtrip=True)
    assert missing["Outcome"] == "UnmodeledEnvironmentStop", missing
    assert result_slots(missing) == state and result_memory(missing, len(data)) == data, missing
    assert missing["reservation"] == reservation, missing
    contract_checks += 1
    outside = request(store, state, data, reservation=reservation, exclusiveDecisions=[True], roundtrip=True,
                      schedule=[dict(beforeEvent=0, address=hex(MEMORY + 24), bytes="ff", invalidateExclusive=False)])
    expected_bytes = bytearray(data)
    expected_bytes[24] = 255
    first = state["x0"] & ((1 << width) - 1)
    packed = first | ((state["x7"] & ((1 << width) - 1)) << width) if pair else first
    expected_bytes[:size] = packed.to_bytes(size, "little")
    assert outside["Outcome"] == "Normal" and result_slots(outside) == dict(state, x3=0), outside
    assert result_memory(outside, len(data)) == bytes(expected_bytes) and outside["reservation"] is None, outside
    assert len(outside["events"]) == 1 and outside["events"][0]["AtomicWidth"] == size * 8, outside
    contract_checks += 1
    for mismatch in (dict(address=hex(MEMORY + 16), sizeBytes=size), dict(address=hex(MEMORY), sizeBytes=size // 2 if size > 1 else 2)):
        failed = request(store, state, data, reservation=mismatch, exclusiveDecisions=[True], roundtrip=True)
        assert failed["Outcome"] == "Normal" and result_slots(failed) == dict(state, x3=1), failed
        assert result_memory(failed, len(data)) == data and failed["reservation"] is None, failed
        contract_checks += 1
    cleared = request(0xD5033F5F, state, data, reservation=reservation, roundtrip=True)
    failed = request(store, result_slots(cleared), data, reservation=cleared["reservation"], exclusiveDecisions=[True])
    assert failed["Outcome"] == "Normal" and result_slots(failed) == dict(state, x3=1), failed
    assert result_memory(failed, len(data)) == data, failed
    contract_checks += 1
    for word in (load, store):
        fault = request(word, slots, data[:size - 1], reservation=reservation, exclusiveDecisions=[True], roundtrip=True)
        assert fault["Outcome"] == "UnmodeledFaultStop" and result_slots(fault) == slots, fault
        assert result_memory(fault, size - 1) == data[:size - 1], fault
        contract_checks += 1
    if size > 1:
        unaligned = dict(slots, x1=MEMORY + 1)
        for word in (load, store):
            fault = request(word, unaligned, data, reservation=reservation, exclusiveDecisions=[True], roundtrip=True)
            assert fault["Outcome"] == "UnmodeledFaultStop" and result_slots(fault) == unaligned, fault
            assert result_memory(fault, len(data)) == data and fault["events"] == [], fault
            contract_checks += 1

# The two 64-bit beats of LDXP can observe an intervening write; its reservation must remain invalidated.
slots = slots_for(1)
old = bytes(range(32))
replacement = bytes(range(255, 239, -1))
pair_load = encode(64, True, pair=True)
torn = request(pair_load, slots, old, schedule=[dict(beforeEvent=1, address=hex(MEMORY), bytes=replacement.hex(), invalidateExclusive=False)], roundtrip=True)
assert torn["Outcome"] == "Normal" and torn["reservation"] is None, torn
assert result_slots(torn)["x0"] == int.from_bytes(old[:8], "little"), torn
assert result_slots(torn)["x7"] == int.from_bytes(replacement[8:], "little"), torn
assert result_memory(torn, 32) == replacement + old[16:], torn
contract_checks += 1

# Ordinary stores also invalidate overlapping reservations, even when the byte value is unchanged.
same = dict(slots, x0=old[0])
ordinary = request(0x39000020, same, old, reservation=dict(address=hex(MEMORY), sizeBytes=8), roundtrip=True)
assert ordinary["Outcome"] == "Normal" and ordinary["reservation"] is None, ordinary
assert result_memory(ordinary, 32) == old, ordinary
contract_checks += 1

# A new load replaces a previous local reservation; an ordinary non-overlapping write does not.
renewed = request(encode(64, True), slots, old, reservation=dict(address=hex(MEMORY + 16), sizeBytes=8), roundtrip=True)
assert renewed["reservation"] == dict(address=hex(MEMORY), sizeBytes=8), renewed
other = dict(slots, x1=MEMORY + 24, x0=old[24])
ordinary = request(0x39000020, other, old, reservation=renewed["reservation"], roundtrip=True)
assert ordinary["Outcome"] == "Normal" and ordinary["reservation"] == renewed["reservation"], ordinary
assert result_memory(ordinary, 32) == old, ordinary
contract_checks += 2

sampled = [
    (0x4997020, "88FE5F88"), (0x4997030, "897E0A88"), (0x4997040, "5F3F03D5"),
    (0x4997198, "087C5F88"), (0x499719C, "1FFC0988"), (0x499EDB4, "BF3B03D5"),
    (0x49B7840, "1FFDDF88"), (0x49B78D8, "68FE9FC8"), (0x49C67F8, "08FDDF08"),
    (0x4A38BA8, "A9FE5F08"), (0x4A38BAC, "A87E0A08"), (0x4A957E8, "15FC9F08"),
]
for address, code in sampled:
    word = int.from_bytes(bytes.fromhex(code), "little")
    if word & 0x3F000000 == 0x08000000:
        check_data(word)
    else:
        result = request(word, {}, b"", roundtrip=True)
        assert result["supported"] and result["Outcome"] == "Normal" and len(result["events"]) == 1, result
        contract_checks += 1

server.stdin.close()
assert server.wait() == 0
sources = ["src/Cpp2CS/Arm64/Arm64OrderedMemory.cs", "src/Cpp2CS/Arm64/Arm64Lifter.cs",
           "src/Cpp2CS/Ir/Model.cs", "src/Cpp2CS/Ir/MirBuilder.cs", "src/Cpp2CS/Ir/MirInterpreter.cs",
           "src/Cpp2CS/Ir/MemoryEffects.cs", "src/Cpp2CS/Ir/MirValidator.cs", "src/Cpp2CS/Ir/MachineProfile.cs", "tests/arm64_ordered_differential.py", "tests/arm64_fixture.py"]
report = dict(cases=sum(counts.values()), casesByForm=counts, classification=classification,
              contractChecks=contract_checks, unicorn=unicorn.__version__, capstone=capstone.__version__,
              sampleFixtures=[dict(address=hex(address), bytes=code) for address, code in sampled],
              sampleInputSha256="6CE1DE5C0357E122F153F62D648DE1655B7F8A339B2AE1C575595868A361E4BB",
              productSha256=hashlib.sha256(args.dll.read_bytes()).hexdigest(),
              sourceSha256={name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in sources},
              scope="Synthetic data/register checks against Unicorn plus explicit event/schedule contract checks; no physical ARM or weak-memory equivalence claim.")
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report))
