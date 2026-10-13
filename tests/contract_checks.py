"""外部进程核对 MIR 序列化、损坏契约与显式环境停止。"""
import copy
import json
import subprocess
import sys
from pathlib import Path

DLL = Path(sys.argv[1])
BASE = {
    "Schema": "cpp2cs.mir/0.3", "Semantics": "attempt08-native-8", "Profile": "aarch64-le-el0-v3",
    "Instruction": {
        "Architecture": "Arm64", "Origin": {"ImageId": "fixture:contract", "Address": "0x1000", "FileOffset": 0, "Bytes": "HyAD1Q=="},
        "Rule": "fixture.contract", "Operations": [{"Code": "Constant", "Result": {"Id": 0, "Width": 64}, "Inputs": [], "Payload": {"$kind": "immediate", "Value": "0x1"}, "Flow": None}],
        "Exit": {"$kind": "next", "NextAddress": "0x1004", "State": {"Id": 0}, "TransferHint": "None"}, "Annotations": [], "ProfileId": "aarch64-le-el0-v3"
    }
}


def run(command, payload):
    return subprocess.run(["dotnet", str(DLL), command], input=(payload if isinstance(payload, str) else json.dumps(payload)) + "\n", text=True, encoding="utf-8", capture_output=True)


valid = run("validate-ir", BASE)
assert valid.returncode == 0, valid.stderr
canonical = json.loads(valid.stdout)
assert canonical == json.loads(run("validate-ir", canonical).stdout)
assert "Support" not in canonical["Instruction"] and "WorldIn" not in canonical["Instruction"]["Operations"][0]
STATEFUL = copy.deepcopy(BASE)
STATEFUL["Instruction"]["Operations"].append({"Code": "WriteSlot", "Result": None, "Inputs": [{"Id": 0, "Width": 64}],
                                               "Payload": {"$kind": "slot", "Name": "x0"}, "Flow": {"Input": {"Id": 0}, "Output": {"Id": 1}}})
STATEFUL["Instruction"]["Exit"]["State"]["Id"] = 1
stateful = run("validate-ir", STATEFUL)
assert stateful.returncode == 0, stateful.stderr
cases = []
bad = copy.deepcopy(BASE)
bad["Semantics"] = "attempt08-integer-1"
cases.append(("old-semantics-version", bad))
bad = copy.deepcopy(BASE)
bad["Semantics"] = "attempt08-float-3"
cases.append(("previous-float-semantics-version", bad))
bad = copy.deepcopy(BASE)
bad["Semantics"] = "attempt08-fixed-memory-4"
cases.append(("previous-memory-semantics-version", bad))
bad = copy.deepcopy(BASE)
bad["Semantics"] = "attempt08-events-security-avx-5"
cases.append(("previous-event-semantics-version", bad))
bad = copy.deepcopy(BASE)
bad["Semantics"] = "attempt08-atomic-stack-6"
cases.append(("previous-atomic-semantics-version", bad))
bad = copy.deepcopy(BASE)
bad["Schema"] = "cpp2cs.mir/0.1"
cases.append(("old-schema-version", bad))
bad = copy.deepcopy(BASE)
bad["Schema"] = "cpp2cs.mir/0.2"
bad["Semantics"] = "attempt08-mir-contract-7"
cases.append(("previous-contract-version", bad))
for hint in ("Call", "Return", "unknown", 0):
    bad = copy.deepcopy(BASE)
    bad["Instruction"]["Exit"]["TransferHint"] = hint
    cases.append((f"invalid-next-hint-{hint}", bad))
for name, value in (("Support", "Exact"), ("Architecture", 0), ("Architecture", 999), ("ProfileId", "other-profile")):
    bad = copy.deepcopy(BASE)
    bad["Instruction"][name] = value
    cases.append((f"unknown-{name}", bad))
bad = copy.deepcopy(BASE)
bad["Profile"] = "other-profile"
cases.append(("envelope-profile-mismatch", bad))
for path, member in (((), "Instruction"), (("Instruction",), "Architecture"), (("Instruction",), "Annotations"),
                     (("Instruction", "Operations", 0), "Code"), (("Instruction", "Operations", 0), "Payload"),
                     (("Instruction", "Exit"), "State"), (("Instruction", "Exit"), "NextAddress"), (("Instruction", "Exit"), "TransferHint"),
                     (("Instruction", "Operations", 0, "Result"), "Id"), (("Instruction", "Operations", 0, "Result"), "Width"),
                     (("Instruction", "Exit", "State"), "Id")):
    bad = copy.deepcopy(BASE)
    target = bad
    for part in path:
        target = target[part]
    del target[member]
    cases.append((f"missing-{member}", bad))
for path, member in ((("Inputs", 0), "Id"), (("Inputs", 0), "Width"), (("Flow", "Input"), "Id"), (("Flow", "Output"), "Id")):
    bad = copy.deepcopy(STATEFUL)
    target = bad["Instruction"]["Operations"][1]
    for part in path:
        target = target[part]
    del target[member]
    cases.append((f"missing-{path}-{member}", bad))
for path in ((), ("Instruction",), ("Instruction", "Operations", 0, "Payload")):
    bad = copy.deepcopy(BASE)
    target = bad
    for part in path:
        target = target[part]
    target["unexpected"] = True
    cases.append((f"unknown-field-{path}", bad))
for path, member, value in ((("Instruction",), "Annotations", None),
                            (("Instruction", "Operations", 0), "Code", 0),
                            (("Instruction", "Operations", 0), "Payload", {"$kind": "slot", "Name": "x0"}),
                            (("Instruction", "Operations", 0), "Payload", {"$kind": "unknown"}),
                            (("Instruction", "Operations", 0), "Payload", None),
                            (("Instruction", "Operations", 0), "Flow", {"Input": {"Id": 0}, "Output": {"Id": 1}}),
                            (("Instruction", "Operations", 0), "Immediate", "0x1"),
                            (("Instruction", "Exit"), "State", {"Id": 1})):
    bad = copy.deepcopy(BASE)
    target = bad
    for part in path:
        target = target[part]
    target[member] = value
    cases.append((f"invalid-{path}-{member}", bad))
serialized = json.dumps(BASE)
cases.append(("duplicate-envelope-member", serialized.replace('"Schema":', '"Schema": "cpp2cs.mir/0.3", "Schema":', 1)))
cases.append(("duplicate-nested-member", serialized.replace('"Value":', '"Value": "0x2", "Value":', 1)))
for address in ("0x1001", "xx1000", "0x", "0x-1"):
    bad = copy.deepcopy(BASE)
    bad["Instruction"]["Origin"]["Address"] = address
    cases.append((f"address-{address}", bad))
for immediate in ("-1", "0x-1", "xxF", "0x", "0x ", "0x1FFFFFFFFFFFFFFFF"):
    bad = copy.deepcopy(BASE)
    bad["Instruction"]["Operations"][0]["Payload"]["Value"] = immediate
    cases.append((f"immediate-{immediate}", bad))
bad = copy.deepcopy(BASE)
bad["Instruction"]["Exit"] = {"$kind": "trap", "Boundary": {"Kind": "ArmBreakpoint", "Detail": "test", "SavedAddress": "0x1000"}, "State": {"Id": 0}, "Target": {"Id": 999, "Width": 64}}
cases.append(("stray-trap-target", bad))
bad = copy.deepcopy(BASE)
bad["Instruction"]["Operations"][0]["Result"]["Width"] = 0
cases.append(("zero-width", bad))
for name, payload in cases:
    result = run("validate-ir", payload)
    assert result.returncode != 0 and result.stderr, name
missing = run("serve", {"arch": "arm64", "bytes": "20040091", "address": "0x1000", "slots": {"btype": "0x0"},
                         "codePages": [{"address": "0x1000", "guarded": False}]})
assert missing.returncode == 0, missing.stderr
missing_state = json.loads(missing.stdout)
assert missing_state["Outcome"] == "UnmodeledEnvironmentStop" and missing_state["stop"]["kind"] == "MissingEnvironment", missing_state
assert missing_state["stoppedOperation"] == missing_state["stop"]["operationIndex"] and missing_state["next"] is None, missing_state
assert missing_state["stateKind"] == "CompletedPrefixWitness" and "x0" not in missing_state["slots"], "missing state must not become zero"
slot_cases = (("btype", 4), ("bti_bt0", 2), ("pauth_ia_enabled", 2), ("apia_key", 1 << 128), ("unknown_slot", 0))
for name, value in slot_cases:
    bad_state = run("serve", {"arch": "arm64", "bytes": "1f2403d5", "address": "0x1000",
                               "slots": {"btype": "0x0", name: hex(value)}, "codePages": [{"address": "0x1000", "guarded": True}]})
    assert bad_state.returncode != 0 and "Invalid state slot or value" in bad_state.stderr, name
classification = run("serve", {"arch": "arm64", "bytes": "20040091", "address": "0x1000", "evaluate": False})
assert classification.returncode == 0 and json.loads(classification.stdout)["supported"]
capabilities = json.loads(classification.stdout)["capabilities"]
assert capabilities["normalTransitionRepresented"] and not capabilities["faultDeliveryModeled"] and capabilities["obligations"]
first = run("serve", {"arch": "x64", "bytes": "4889d890", "address": "0x1000", "decodeFirst": True, "evaluate": False})
assert first.returncode == 0 and json.loads(first.stdout)["length"] == 3 and json.loads(first.stdout)["decoded"]
print(json.dumps({"contract_checks": len(cases) + 6 + len(slot_cases), "passed": True}))
