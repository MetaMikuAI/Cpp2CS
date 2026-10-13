"""验证两份二进制的全部已知入口，分别记录机器诊断、条件化 NIR 与缺失签名。"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT.parent
DLL = ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll"
TARGETS = (("arm64", "lib/arm64/libil2cpp.so", "lib/arm64/global-metadata.dat"),
           ("x64", "lib/x86_64/GameAssembly.dll", "lib/x86_64/global-metadata.dat"))


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest().upper()


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def file_identity():
    paths = [path for folder in (ROOT / "src/Cpp2CS", ROOT / "tests") for path in folder.rglob("*")
             if path.suffix in {".cs", ".csproj", ".py", ".props", ".targets"}
             and "bin" not in path.parts and "obj" not in path.parts]
    paths.extend(path for path in ROOT.iterdir() if path.is_file() and
                 (path.suffix in {".props", ".targets", ".slnx"} or path.name in {"global.json", "nuget.config"}))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths)}


def inspect_report(directory, inventory, assembly_sha, inventory_path):
    summary = json.loads((directory / "summary.json").read_text(encoding="utf-8-sig"))
    assert summary["format"] == "cpp2cs.nir-corpus/1" and summary["status"] == "completed"
    assert summary["identity"]["implementationAssemblySha256"] == assembly_sha
    assert summary["identity"]["binarySha256"] == inventory["binary"]["sha256"]
    assert summary["identity"]["inventoryEntriesSha256"] == inventory["entriesSha256"]
    expected = inventory["entryCount"]
    assert summary["allKnownEntriesClassified"]
    assert summary["denominator"]["knownEntryAddresses"] == expected
    assert summary["denominator"]["processedEntries"] == expected
    counts = Counter()
    gaps = Counter()
    boundaries = Counter()
    complete = set()
    addresses = set()
    with (directory / "entries.jsonl").open(encoding="utf-8-sig") as entries:
        for line in entries:
            entry = json.loads(line)
            address = entry["address"]
            assert address not in addresses
            addresses.add(address)
            assert address == int(entry["entry"], 16) == int(entry["inventoryEntry"]["entry"], 16)
            assert entry["machine"]["structureValidated"]
            assert entry["inventoryEntry"]["evidence"]
            counts[entry["status"]] += 1
            gaps.update(set(item["code"] for item in entry["diagnostics"]))
            boundaries.update(set(item["code"] for item in entry["machine"]["boundaries"]))
            if entry["status"] == "complete":
                assert entry["signatureStatus"] == "known"
                assert entry["inventoryEntry"]["signatureSynthetic"] is False
                assert entry["inventoryEntry"]["signatureEvidence"]
                assert entry["nirValidated"] and entry["jsonRoundTripValidated"]
                assert entry["diagnostics"] == []
                complete.add(address)
            else:
                assert not entry["nirValidated"] and not entry["jsonRoundTripValidated"]
    assert len(addresses) == expected
    with (inventory_path.parent / inventory["entriesFile"]).open(encoding="utf-8-sig") as stream:
        expected_addresses = {int(json.loads(line)["entry"], 16) for line in stream}
    assert addresses == expected_addresses
    assert dict(counts) == summary["statusCounts"]
    assert dict(gaps) == summary["gapCounts"]
    assert dict(boundaries) == summary["boundaryCounts"]
    assert len(complete) == summary["completeEntries"]
    assert summary["allKnownEntriesNirComplete"] == (len(complete) == expected)
    modules = set()
    with (directory / "modules.jsonl").open(encoding="utf-8-sig") as stream:
        for line in stream:
            module = json.loads(line)
            assert module["address"] in complete and module["address"] not in modules
            modules.add(module["address"])
            assert len(module["module"]["functions"]) == 1
    assert modules == complete
    for name, digest in summary["artifacts"].items():
        assert sha(directory / name) == digest
    return {"knownEntryAddresses": expected, "adoptedContractEntries": summary["denominator"]["adoptedContractEntries"],
            "statusCounts": dict(counts), "gapCounts": dict(gaps), "boundaryCounts": dict(boundaries),
            "completeEntries": len(complete), "completeRate": len(complete) / expected,
            "allKnownEntriesClassified": True, "allKnownEntriesNirComplete": len(complete) == expected,
            "summary": str((directory / "summary.json").resolve())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--dll", type=Path, default=DLL)
    parser.add_argument("--inventory-directory", type=Path,
                        help="复用已生成的 arm64.inventory.json / x64.inventory.json；仍核对输入身份")
    parser.add_argument("--skip-fixtures", action="store_true", help="只执行全入口验证；明确记录未在本运行重复自测和有限输入对照")
    parser.add_argument("--max-instructions", type=int, default=512)
    parser.add_argument("--machine-budget", type=int, default=32)
    parser.add_argument("--normalization-rounds", type=int, default=64)
    args = parser.parse_args()
    if min(args.max_instructions, args.machine_budget, args.normalization_rounds) < 1:
        parser.error("所有预算必须为正数")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest_path = output / "manifest.json"
    if manifest_path.exists():
        parser.error("输出目录已有 manifest.json；使用新目录以保留先前验证记录")
    assembly = args.dll.resolve()
    assembly_sha = sha(assembly)
    sources = file_identity()
    started = datetime.now(timezone.utc).isoformat()
    commands = []
    write_json(manifest_path, {"status": "running", "started": started, "assemblySha256": assembly_sha,
                               "sourcesAndTests": sources, "options": vars(args) | {"output": str(output),
                                   "dll": str(assembly), "inventory_directory": str(args.inventory_directory) if args.inventory_directory else None}})

    def execute(name, command, accepted=(0,)):
        print(name, flush=True)
        log = output / f"{name}.log"
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run([str(item) for item in command], cwd=WORKSPACE, text=True,
                                    encoding="utf-8", stdout=stream, stderr=subprocess.STDOUT)
        commands.append({"name": name, "arguments": [str(item) for item in command],
                         "exitCode": result.returncode, "log": str(log)})
        assert sha(assembly) == assembly_sha, "验证过程中程序集发生变化"
        if result.returncode not in accepted:
            write_json(output / "failed-command.json", commands[-1])
            raise SystemExit(f"{name} failed: {result.returncode}; {log}")

    if not args.skip_fixtures:
        execute("selftest", ["dotnet", assembly, "selftest"])
        execute("nir-binary-fixtures", ["dotnet", assembly, "nir-check",
                                        WORKSPACE / TARGETS[0][1], WORKSPACE / TARGETS[1][1], output / "fixtures"])
        execute("nir-json-inputs", [sys.executable, ROOT / "tests/nir_json_inputs.py", assembly,
                                     output / "fixtures/arm64.nir.json"])
    reports = {}
    inputs = {}
    def validate_target(target):
        name, binary_relative, metadata_relative = target
        binary, metadata = WORKSPACE / binary_relative, WORKSPACE / metadata_relative
        inputs[name] = {"binary": {"path": str(binary), "sha256": sha(binary)},
                        "metadata": {"path": str(metadata), "sha256": sha(metadata)}}
        inventory_path = (args.inventory_directory.resolve() if args.inventory_directory else output) / f"{name}.inventory.json"
        if args.inventory_directory is not None and not inventory_path.exists():
            inventory_path = args.inventory_directory.resolve() / f"{name}.json"
        if args.inventory_directory is None:
            execute(f"{name}-inventory", [sys.executable, ROOT / "tests/nir_contract_inventory.py", binary,
                                          metadata, inventory_path, "--adopt-standard-il2cpp-prototype"])
        inventory = json.loads(inventory_path.read_text(encoding="utf-8-sig"))
        assert not inventory.get("pilot"), "全量运行不能采用 pilot 子清单"
        assert inventory["binary"]["sha256"] == inputs[name]["binary"]["sha256"]
        assert inventory["metadata"]["sha256"] == inputs[name]["metadata"]["sha256"]
        assert inventory["entriesSha256"] == sha(inventory_path.parent / inventory["entriesFile"])
        assert inventory["methodsSha256"] == sha(inventory_path.parent / inventory["methodsFile"])
        directory = output / name
        execute(f"{name}-corpus", ["dotnet", assembly, "nir-corpus", binary, inventory_path, directory,
                                   args.max_instructions, args.machine_budget, args.normalization_rounds], (0, 2))
        reports[name] = inspect_report(directory, inventory, assembly_sha, inventory_path)

    with ThreadPoolExecutor(max_workers=len(TARGETS)) as pool:
        for result in pool.map(validate_target, TARGETS):
            pass
    assert file_identity() == sources, "验证过程中源代码或测试文件发生变化"
    for item in inputs.values():
        for identity in item.values():
            assert sha(Path(identity["path"])) == identity["sha256"], "验证过程中二进制或元数据发生变化"
    all_complete = all(report["allKnownEntriesNirComplete"] for report in reports.values())
    manifest = {"status": "completed", "started": started, "finished": datetime.now(timezone.utc).isoformat(),
                "assemblySha256": assembly_sha, "sourcesAndTests": sources, "inputs": inputs, "commands": commands,
                "budgets": {"recoveryInstructionsPerEntry": args.max_instructions,
                            "unknownSignatureMachineInstructionsPerEntry": args.machine_budget,
                            "normalizationRoundsPerEntry": args.normalization_rounds},
                "checks": {"allKnownEntriesClassified": True, "allKnownEntriesNirComplete": all_complete,
                           "selftest": "not-repeated" if args.skip_fixtures else "passed",
                           "jsonInputValidation": "not-repeated" if args.skip_fixtures else "passed",
                           "finiteBinaryDifferential": "not-repeated" if args.skip_fixtures else "passed"},
                "reports": reports,
                "meaning": "Full inventory denominator for each binary; unknown and unsupported signatures are not successful NIR. Completeness is conditional on recorded signatures, ABI and recovery domains. Machine graph budget stops remain gaps. Finite fixture comparisons are distinct from all-entry structural recovery and do not prove game runtime equivalence."}
    write_json(manifest_path, manifest)
    print(json.dumps({"manifest": str(manifest_path), "reports": reports}, ensure_ascii=False), flush=True)
    return 0 if all_complete else 2


if __name__ == "__main__":
    sys.exit(main())
