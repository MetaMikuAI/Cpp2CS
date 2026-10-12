"""外部进程核对损坏 MIR 与缺失机器状态必须明确失败。"""
import copy
import json
import subprocess
import sys
from pathlib import Path

DLL = Path(sys.argv[1])
BASE = {
    "Schema": "cpp2cs.mir/0.1", "Semantics": "attempt08-bitvector-2", "Profile": "aarch64-le-el0-v1",
    "Instruction": {
        "Architecture": "Arm64", "Origin": {"ImageId": "fixture:contract", "Address": "0x1000", "FileOffset": 0, "Bytes": "HyAD1Q=="},
        "Rule": "fixture.contract", "Operations": [{"Code": "Constant", "Result": {"Id": 0, "Width": 64}, "Inputs": [], "Immediate": "0x1", "WorldIn": -1, "WorldOut": -1, "Fault": "None"}],
        "Exit": {"Kind": "Next", "Address": "0x1004"}, "Support": "Exact", "Limitations": []
    }
}


def run(command, payload):
    return subprocess.run(["dotnet", str(DLL), command], input=json.dumps(payload) + "\n", text=True, encoding="utf-8", capture_output=True)


assert run("validate-ir", BASE).returncode == 0
cases = []
bad = copy.deepcopy(BASE)
bad["Semantics"] = "attempt08-integer-1"
cases.append(("old-semantics-version", bad))
for name, value in (("Support", 999), ("Architecture", 999)):
    bad = copy.deepcopy(BASE)
    bad["Instruction"][name] = value
    cases.append((f"unknown-{name}", bad))
for address in ("0x1001", "xx1000", "0x", "0x-1"):
    bad = copy.deepcopy(BASE)
    bad["Instruction"]["Origin"]["Address"] = address
    cases.append((f"address-{address}", bad))
for immediate in ("-1", "0x-1", "xxF", "0x", "0x ", "0x1FFFFFFFFFFFFFFFF"):
    bad = copy.deepcopy(BASE)
    bad["Instruction"]["Operations"][0]["Immediate"] = immediate
    cases.append((f"immediate-{immediate}", bad))
bad = copy.deepcopy(BASE)
bad["Instruction"]["Exit"] = {"Kind": "Trap", "Reason": "test", "Target": {"Id": 999, "Width": 64}}
cases.append(("stray-trap-target", bad))
bad = copy.deepcopy(BASE)
bad["Instruction"]["Operations"][0]["Result"]["Width"] = 0
cases.append(("zero-width", bad))
for name, payload in cases:
    result = run("validate-ir", payload)
    assert result.returncode != 0 and result.stderr, name
missing = run("serve", {"arch": "arm64", "bytes": "20040091", "address": "0x1000", "slots": {}})
assert missing.returncode != 0 and "KeyNotFoundException" in missing.stderr, "missing state must not become zero"
classification = run("serve", {"arch": "arm64", "bytes": "20040091", "address": "0x1000", "evaluate": False})
assert classification.returncode == 0 and json.loads(classification.stdout)["supported"]
first = run("serve", {"arch": "x64", "bytes": "4889d890", "address": "0x1000", "decodeFirst": True, "evaluate": False})
assert first.returncode == 0 and json.loads(first.stdout)["length"] == 3 and json.loads(first.stdout)["decoded"]
print(json.dumps({"contract_checks": len(cases) + 4, "passed": True}))
