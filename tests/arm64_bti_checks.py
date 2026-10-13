"""BTI 环境、入口兼容矩阵及跨页间接分支检查；不模拟异常分派或取指。"""

import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
SOURCE = 0x10000
TARGET = 0x23000
MEMORY = 0x30000
BTI = {0xD503241F: {0}, 0xD503245F: {0, 1, 2}, 0xD503249F: {0, 1, 3}, 0xD50324DF: {0, 1, 2, 3}}
parser = argparse.ArgumentParser()
parser.add_argument("--dll", type=Path, default=ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll")
parser.add_argument("--output", type=Path, default=ROOT / "artifacts/arm64-bti-checks.json")
args = parser.parse_args()
server = subprocess.Popen(["dotnet", str(args.dll), "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
counts = Counter()


def execute(word, slots, guarded=None, address=TARGET, require_supported=True, **extra):
    request = dict(arch="arm64", bytes=word.to_bytes(4, "little").hex(), address=hex(address),
                   slots={name: hex(value) for name, value in slots.items()}, roundtrip=True, **extra)
    if guarded is not None:
        request["codePages"] = [dict(address=hex(address & ~4095), guarded=guarded)]
    server.stdin.write(json.dumps(request) + "\n")
    server.stdin.flush()
    line = server.stdout.readline()
    assert line, ("server exited", server.poll(), request)
    response = json.loads(line)
    if require_supported:
        assert response["supported"], (hex(word), response)
    return response


def state(response):
    return {name: int(value, 16) for name, value in response["slots"].items()}


def unchanged_stop(response, slots, outcome="UnmodeledFaultStop"):
    assert response["Outcome"] == outcome and response["next"] is None, response
    if outcome == "UnmodeledFaultStop":
        assert response["Event"] == "arm64.BranchTargetException", response
    assert state(response) == slots and response["events"] == [] and response["Accesses"] == [], response


for word, btype, guarded in itertools.product(BTI, range(4), (False, True)):
    slots = dict(btype=btype, x0=0xAABBCCDD, x30=0x123456789ABCDEF0)
    response = execute(word, slots, guarded)
    if not guarded or btype in BTI[word]:
        assert response["Outcome"] == "Normal" and int(response["next"], 16) == TARGET + 4, response
        assert state(response) == dict(slots, btype=0), response
    else:
        unchanged_stop(response, slots)
    assert response["events"] == [] and response["Accesses"] == [], response
    counts["bti-compatibility"] += 1

# Test branch state at the source and then execute its target in a separately described page.
for source_guarded, target_guarded, link, rn in itertools.product((False, True), (False, True), (False, True), (0, 16, 17, 30)):
    word = (0xD63F0000 if link else 0xD61F0000) | (rn << 5)
    slots = dict(btype=0, x0=0x55, x30=0xAABB)
    slots[f"x{rn}"] = TARGET
    branch = execute(word, slots, source_guarded, SOURCE)
    expected_type = 2 if link else 1 if rn in (16, 17) or not source_guarded else 3
    expected_slots = dict(slots, btype=expected_type)
    if link:
        expected_slots["x30"] = SOURCE + 4
    assert branch["Outcome"] == "Normal" and int(branch["next"], 16) == TARGET, branch
    assert state(branch) == expected_slots and branch["events"] == [], branch
    counts["indirect-branch-state"] += 1
    for target in (*BTI, 0xD503201F, 0x91000400):
        response = execute(target, state(branch), target_guarded)
        compatible = not target_guarded or expected_type in BTI.get(target, {0})
        if compatible:
            expected = dict(expected_slots, btype=0)
            if target == 0x91000400:
                expected["x0"] = (expected["x0"] + 1) & ((1 << 64) - 1)
            assert response["Outcome"] == "Normal" and state(response) == expected, response
        else:
            unchanged_stop(response, expected_slots)
        counts["cross-page-target"] += 1

# Ordinary instructions on an unguarded page clear a previous branch type on normal completion.
for word, btype in itertools.product((0xD503201F, 0x14000004, 0x94000004, 0xD65F03C0), range(4)):
    slots = dict(btype=btype, x30=SOURCE + 0x40)
    response = execute(word, slots, False, SOURCE)
    expected = dict(slots, btype=0)
    if word == 0x94000004:
        expected["x30"] = SOURCE + 4
    assert response["Outcome"] == "Normal" and state(response) == expected, response
    counts["normal-exit-clears-btype"] += 1

# PACSP remains an implicit landing pad even if pointer authentication is disabled.
for word, btype, guarded, bt0, enabled in itertools.product((0xD503233F, 0xD503237F), range(4), (False, True), range(2), range(2)):
    slots = dict(btype=btype, bti_bt0=bt0, x30=0x123456789AB0, sp=0x45670,
                 apia_key=0x0123456789ABCDEFFEDCBA9876543210, apib_key=0x112233445566778899AABBCCDDEEFF00,
                 pauth_ia_enabled=enabled, pauth_ib_enabled=enabled)
    response = execute(word, slots, guarded)
    if not guarded or btype != 3 or bt0 == 0:
        baseline = execute(word, dict(slots, btype=0), False)
        assert response["Outcome"] == "Normal" and state(response) == state(baseline), response
        assert state(response)["btype"] == 0, response
        if not enabled:
            assert state(response)["x30"] == slots["x30"], response
    else:
        unchanged_stop(response, slots)
    counts["pacsp-bt0"] += 1

# The entry stop must precede architectural writes, memory events, reservation changes and scheduled writes.
for word in (0x91000400, 0xF9000020, 0xC8037C20, 0xD5033F5F, 0xD5033BBF, 0xF9800020):
    slots = dict(btype=3, x0=0x1234, x1=MEMORY, x3=0x7777)
    reservation = dict(address=hex(MEMORY), sizeBytes=8)
    schedule = [dict(beforeEvent=0, address=hex(MEMORY), bytes="ff", invalidateExclusive=True)]
    response = execute(word, slots, True, memory=[dict(address=hex(MEMORY), bytes="00" * 8)],
                       reservation=reservation, exclusiveDecisions=[True], schedule=schedule)
    unchanged_stop(response, slots)
    assert response["reservation"] == reservation and set(response["memory"].values()) == {0}, response
    assert response["appliedSchedule"] == [] and len(response["remainingSchedule"]) == 1, response
    counts["stop-before-effects"] += 1

# Code-page environment is required at the current PC, independently of BTYPE and data mappings.
for word, btype, address in itertools.product((0xD503201F, 0xD503245F, 0xF9000020), range(4), (SOURCE, SOURCE + 0xFFC, SOURCE + 0x1000)):
    slots = dict(btype=btype, x0=0x1234, x1=MEMORY)
    response = execute(word, slots, None, address, memory=[dict(address=hex(MEMORY), bytes="00" * 8)],
                       codePages=[dict(address=hex(SOURCE - 0x1000), guarded=False)])
    unchanged_stop(response, slots, "UnmodeledEnvironmentStop")
    assert set(response["memory"].values()) == {0}, response
    counts["missing-code-page"] += 1
for address in (SOURCE, SOURCE + 0xFFC):
    response = execute(0xD503245F, dict(btype=1), True, address)
    assert response["Outcome"] == "Normal" and state(response) == dict(btype=0), response
    counts["page-boundary"] += 1

# BRK retains its higher-priority exception boundary rather than becoming a BTI fault.
for btype in range(4):
    slots = dict(btype=btype, x0=0x1234)
    response = execute(0xD4200020, slots, True)
    assert response["Outcome"] == "Trap" and response["Event"] == "arm64.BRK.0x0001", response
    assert int(response["resumeAddress"], 16) == TARGET and state(response) == slots, response
    assert response["events"] == [] and response["Accesses"] == [], response
    counts["exception-priority"] += 1

# EL0 alone does not determine HLT: halting debug enable/permission is outside this profile.
for btype in range(4):
    response = execute(0xD4400020, dict(btype=btype), True, require_supported=False)
    assert not response["supported"], response
    counts["hlt-debug-environment-unsupported"] += 1

server.stdin.close()
assert server.wait() == 0
sources = ["src/Cpp2CS/Arm64/Arm64Lifter.cs", "src/Cpp2CS/Arm64/Arm64Control.cs", "src/Cpp2CS/Arm64/Arm64PointerAuthentication.cs",
           "src/Cpp2CS/Ir/Model.cs", "src/Cpp2CS/Ir/MirInterpreter.cs", "src/Cpp2CS/Ir/MachineProfile.cs", "src/Cpp2CS/Program.cs",
           "tests/arm64_bti_checks.py"]
report = dict(checks=sum(counts.values()), checksByGroup=counts,
              productSha256=hashlib.sha256(args.dll.read_bytes()).hexdigest(),
              sourceSha256={name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in sources},
              scope="Synthetic branch-state and code-page contracts, explicit BTI compatibility table, no physical CPU or exception-delivery/next-fetch proof.")
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report))
