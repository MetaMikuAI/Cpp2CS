"""验证已构建的产品，保留全量扫描、独立解码、语义差分及输入身份。"""
import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT.parent
DLL = ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll"
TESTS = ROOT / "tests"
TARGETS = (("arm64", "lib/arm64/libil2cpp.so"), ("x64", "lib/x86_64/GameAssembly.dll"))


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest().upper()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/verified")
    parser.add_argument("--fuzz-words", type=int, default=200000)
    parser.add_argument("--baseline", type=Path, help="旧全量报告目录；按全部候选核对覆盖回退")
    args = parser.parse_args()
    output = args.output.resolve()
    if args.baseline is not None and args.baseline.resolve() == output:
        parser.error("基线目录必须与输出目录不同，禁止覆盖后自比较")
    output.mkdir(parents=True, exist_ok=True)
    assembly_hash = sha(DLL)
    sources = {str(path.relative_to(ROOT)): sha(path) for path in sorted((ROOT / "src/Cpp2CS").rglob("*.cs")) if "obj" not in path.parts and "bin" not in path.parts}
    tests = {str(path.relative_to(ROOT)): sha(path) for path in sorted(TESTS.glob("*.py"))}
    (output / "manifest.json").write_text(json.dumps({"status": "running", "utc": datetime.now(timezone.utc).isoformat(), "assemblySha256": assembly_hash}, indent=2) + "\n", encoding="utf-8")
    commands = []

    def execute(name, command, accepted=(0,)):
        print(name, flush=True)
        result = subprocess.run([str(item) for item in command], cwd=WORKSPACE, text=True, encoding="utf-8", stdout=subprocess.PIPE)
        log = output / f"{name}.log"
        log.write_text(result.stdout, encoding="utf-8")
        commands.append({"name": name, "arguments": [str(item) for item in command], "exitCode": result.returncode, "log": str(log)})
        if result.returncode not in accepted:
            print(result.stdout, file=sys.stderr)
            raise SystemExit(f"{name} failed: {result.returncode}")
        assert sha(DLL) == assembly_hash, "验证过程中程序集发生变化，结果不能共用身份"
        return result.stdout

    execute("core", ["dotnet", DLL, "selftest"])
    execute("contracts", [sys.executable, TESTS / "contract_checks.py", DLL])
    execute("coverage-contracts", [sys.executable, TESTS / "coverage_contracts.py"])
    execute("arm64-differential", [sys.executable, TESTS / "arm64_differential.py", "--dll", DLL, "--output", output / "arm64-differential.json", "--fuzz-words", args.fuzz_words])
    x64 = execute("x64-differential", [sys.executable, TESTS / "x64_differential.py", DLL])
    (output / "x64-differential.json").write_text(json.dumps(json.loads(x64), indent=2) + "\n", encoding="utf-8")
    reports = []
    all_represented = True
    fully_lifted = True
    decoder_checks = True
    known_entries_covered = True
    coverage_regression_free = None if args.baseline is None else True
    for architecture, relative in TARGETS:
        binary = WORKSPACE / relative
        execute(f"{architecture}-scan", ["dotnet", DLL, "scan", binary, output], (0, 2))
        report_path = output / f"{architecture}-{sha(binary)[:12].lower()}.report.json"
        report = json.loads(report_path.read_text(encoding="utf-8-sig"))
        assert report["implementationAssemblySha256"] == assembly_hash
        assert report["inputSha256"] == sha(binary)
        execute(f"{architecture}-decoder", [sys.executable, TESTS / "decoder_corpus.py", report_path, binary, "--output-directory", output], (0, 1))
        independent = json.loads((output / report_path.name.replace(".report.json", ".decoder.report.json")).read_text(encoding="utf-8"))
        all_represented &= report["allCandidatesRepresented"]
        fully_lifted &= report["fullyLifted"]
        decoder_checks &= independent["decoderChecksPassed"] and independent["peEntryBoundariesCovered"]
        if architecture == "x64":
            execute("x64-entry-supplement", [sys.executable, TESTS / "entry_corpus.py", report_path, binary, "--dll", DLL, "--output", output], (0, 1))
            entries = json.loads((output / report_path.name.replace(".report.json", ".entry.report.json")).read_text(encoding="utf-8"))
            assert entries["sameAssemblyAsPrimary"], "入口补充与主扫描程序集不同"
            known_entries_covered &= entries["allKnownEntriesHaveCandidate"] and entries["allSupplementaryPathsJoinedOrEnded"]
        reports.append(str(report_path))
        if args.baseline is not None:
            execute(f"{architecture}-coverage-comparison", [sys.executable, TESTS / "compare_coverage.py", args.baseline.resolve() / report_path.name, report_path, "--output", output])
            comparison = json.loads((output / report_path.name.replace(".report.json", ".coverage-comparison.json")).read_text(encoding="utf-8"))
            coverage_regression_free &= comparison["passed"]
    artifacts = {str(path.relative_to(output)): sha(path) for path in sorted(output.iterdir()) if path.is_file() and path.name != "manifest.json"}
    assert all(sha(ROOT / path) == digest for path, digest in sources.items()), "验证过程中源代码发生变化"
    assert all(sha(ROOT / path) == digest for path, digest in tests.items()), "验证过程中测试脚本发生变化"
    arm = json.loads((output / "arm64-differential.json").read_text(encoding="utf-8"))
    checks = {"semanticFixturesPassed": True, "decoderChecksPassed": decoder_checks, "allKnownEntriesCovered": known_entries_covered, "coverageRegressionFree": coverage_regression_free, "armClassificationDisagreements": arm["classification_disagreements"], "allCandidatesRepresented": all_represented, "fullyLifted": fully_lifted}
    manifest = {"status": "completed", "utc": datetime.now(timezone.utc).isoformat(), "assemblySha256": assembly_hash, "commands": commands, "scannerReports": reports, "checks": checks, "sources": sources, "testSources": tests, "artifacts": artifacts,
                "meaning": "Full executable candidate census and structural validation, plus independent decoder checks and finite semantic fixtures. Completeness must be read from each report; this manifest does not certify native or game equivalence."}
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(output / "manifest.json")
    return 0 if fully_lifted and decoder_checks and arm["classification_disagreements"] == 0 else 2


if __name__ == "__main__":
    sys.exit(main())
