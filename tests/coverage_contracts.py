"""用改善、退化、边界错位和损坏索引核对覆盖比较器的验收边界。"""
import gzip
import hashlib
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "artifacts/coverage-contracts"
OUTPUT.mkdir(parents=True, exist_ok=True)


def fixture(name, rows, *, image="fixture:image", wrong_hash=False, contracts=None, wrong_contract_hash=False):
    boundary = OUTPUT / f"{name}.tsv.gz"
    with gzip.open(boundary, "wt", encoding="utf-8") as stream:
        stream.write("address\tfileOffset\tlength\tstatus\n")
        stream.writelines(f"{address:X}\t{offset:X}\t{length}\t{status}\n" for address, offset, length, status in rows)
    statuses = [row[3] for row in rows]
    report = {"inputSha256": image, "architecture": "Arm64", "preferredBase": "0x0",
              "executableRanges": [{"address": "0x1000", "fileOffset": "0x0", "FileSize": 8}],
              "boundaryIndex": str(boundary.resolve()), "boundaryIndexSha256": "bad" if wrong_hash else hashlib.sha256(boundary.read_bytes()).hexdigest().upper(),
              "candidates": len(rows), "bytesCovered": sum(row[2] for row in rows), "truncatedOrUnalignedBytes": 0,
              "validated": statuses.count("V"), "unsupported": statuses.count("U"), "invalid": statuses.count("I"), "validationErrors": statuses.count("E"),
              "implementationAssemblySha256": "fixture:assembly", "semanticsVersion": "fixture:semantics", "profile": {"Id": "fixture:profile"}, "forms": {}}
    if contracts is not None:
        contract_path = OUTPUT / f"{name}.contracts.tsv.gz"
        with gzip.open(contract_path, "wt", encoding="utf-8") as stream:
            stream.write("address\tfileOffset\tlength\tsupport\tobligations\n")
            stream.writelines(f"{address:X}\t{offset:X}\t{length}\t{support}\t{','.join(codes) or '-'}\n" for address, offset, length, support, codes in contracts)
        report["contractIndex"] = str(contract_path.resolve())
        report["contractIndexSha256"] = "bad" if wrong_contract_hash else hashlib.sha256(contract_path.read_bytes()).hexdigest().upper()
    path = OUTPUT / f"{name}.report.json"
    path.write_text(json.dumps(report), encoding="utf-8")
    return path


before = fixture("before", [(0x1000, 0, 4, "V"), (0x1004, 4, 4, "U")])
improved = fixture("improved", [(0x1000, 0, 4, "V"), (0x1004, 4, 4, "V")])
regressed = fixture("regressed", [(0x1000, 0, 4, "U"), (0x1004, 4, 4, "V")])
shifted = fixture("shifted", [(0x1000, 0, 3, "V"), (0x1003, 3, 5, "V")])
corrupt = fixture("corrupt", [(0x1000, 0, 4, "V"), (0x1004, 4, 4, "V")], wrong_hash=True)
different = fixture("different", [(0x1000, 0, 4, "V"), (0x1004, 4, 4, "V")], image="fixture:other-image")
for after, expected_code, error in ((before, 0, None), (improved, 0, None), (regressed, 1, None),
                                   (shifted, 1, "解码边界改变"), (corrupt, 1, "边界索引身份不符"), (different, 1, "不可比较不同输入或映射")):
    result = subprocess.run([sys.executable, "-X", "utf8", str(ROOT / "tests/compare_coverage.py"), str(before), str(after), "--output", str(OUTPUT)], capture_output=True, text=True, encoding="utf-8")
    assert result.returncode == expected_code, (after.name, result.returncode, result.stderr)
    if error is not None:
        assert error in result.stderr, (after.name, result.stderr)
    else:
        assert result.stdout.strip().endswith(".coverage-comparison.json"), (after.name, result.stdout, result.stderr)
assert json.loads((OUTPUT / "regressed.coverage-comparison.json").read_text(encoding="utf-8"))["coverageRegressions"] == 1
unavailable = json.loads((OUTPUT / "improved.coverage-comparison.json").read_text(encoding="utf-8"))
assert unavailable["contractComparisonStatus"] == "unavailable" and unavailable["semanticContractRegressionFree"] is None
candidate_rows = [(0x1000, 0, 4, "V"), (0x1004, 4, 4, "U")]
exact = fixture("contract-exact", candidate_rows, contracts=[(0x1000, 0, 4, "Exact", [])])
normal = fixture("contract-normal", candidate_rows, contracts=[(0x1000, 0, 4, "NormalPathOnly", ["FaultDelivery"])])
boundary = fixture("contract-boundary", candidate_rows, contracts=[(0x1000, 0, 4, "ExceptionBoundaryOnly", ["FaultDelivery"])])
added = fixture("contract-added", candidate_rows, contracts=[(0x1000, 0, 4, "NormalPathOnly", ["Environment", "FaultDelivery"])])
missing = fixture("contract-missing", candidate_rows, contracts=[])
extra = fixture("contract-extra", candidate_rows, contracts=[(0x1000, 0, 4, "Exact", []), (0x1004, 4, 4, "Exact", [])])
bad_contract_hash = fixture("contract-bad-hash", candidate_rows, contracts=[(0x1000, 0, 4, "Exact", [])], wrong_contract_hash=True)
bad_contract_boundary = fixture("contract-bad-boundary", candidate_rows, contracts=[(0x1000, 1, 4, "Exact", [])])
contract_cases = ((exact, exact, 0, None), (before, exact, 0, None), (exact, normal, 1, None),
                  (normal, boundary, 1, None), (normal, added, 1, None), (added, normal, 0, None),
                  (exact, missing, 1, "新契约索引未对应全部有效候选"), (exact, extra, 1, "新契约索引含多余候选"),
                  (exact, bad_contract_hash, 1, "契约索引身份不符"), (exact, bad_contract_boundary, 1, "新契约索引未对应全部有效候选"))
for old, after, expected_code, error in contract_cases:
    result = subprocess.run([sys.executable, "-X", "utf8", str(ROOT / "tests/compare_coverage.py"), str(old), str(after), "--output", str(OUTPUT)], capture_output=True, text=True, encoding="utf-8")
    assert result.returncode == expected_code, (after.name, result.returncode, result.stderr)
    if error is not None:
        assert error in result.stderr, (after.name, result.stderr)
    else:
        comparison = json.loads(Path(result.stdout.strip()).read_text(encoding="utf-8"))
        assert comparison["structuralCoveragePassed"], comparison
        assert comparison["contractComparisonStatus"] == ("unavailable" if old == before else "compared")
        assert comparison["semanticContractRegressionFree"] == (None if old == before else expected_code == 0), comparison
        assert comparison["contractRegressions"] == (None if old == before else expected_code), comparison
guard = OUTPUT / "guard-baseline"
guard.mkdir(exist_ok=True)
manifest = guard / "manifest.json"
manifest.write_text("preserve baseline", encoding="utf-8")
result = subprocess.run([sys.executable, "-X", "utf8", str(ROOT / "tests/run_validation.py"), "--output", str(guard), "--baseline", str(guard)], capture_output=True, text=True, encoding="utf-8")
assert result.returncode == 2 and "基线目录必须与输出目录不同" in result.stderr, result.stderr
assert manifest.read_text(encoding="utf-8") == "preserve baseline"
print(json.dumps({"coverage_contract_checks": 8 + len(contract_cases), "passed": True}))
