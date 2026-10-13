"""逐地址比较两轮全量扫描，保留全部状态变化，拒绝已支持候选回退。"""
import argparse
import collections
import gzip
import hashlib
import itertools
import json
from pathlib import Path


def sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest().upper()


def rows(path):
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        assert stream.readline().rstrip() == "address\tfileOffset\tlength\tstatus"
        for line in stream:
            address, offset, length, status = line.rstrip().split("\t")
            assert status in {"V", "U", "I", "E"}
            yield int(address, 16), int(offset, 16), int(length), status


def contract_rows(report):
    with gzip.open(report["contractIndex"], "rt", encoding="utf-8") as stream:
        assert stream.readline().rstrip() == "address\tfileOffset\tlength\tsupport\tobligations"
        for line in stream:
            address, offset, length, support, obligations = line.rstrip().split("\t")
            assert support in {"Exact", "NormalPathOnly", "ExceptionBoundaryOnly"}, "未知支持等级"
            codes = () if obligations == "-" else tuple(obligations.split(","))
            assert codes == tuple(sorted(set(codes))) and all(codes), "义务代码必须唯一且有序"
            yield int(address, 16), int(offset, 16), int(length), support, codes


def contract_stream(report):
    assert ("contractIndex" in report) == ("contractIndexSha256" in report), "契约索引身份字段不完整"
    if "contractIndex" not in report:
        return None
    assert sha(report["contractIndex"]) == report["contractIndexSha256"], "契约索引身份不符"
    return contract_rows(report)


def compare(before_path, after_path, output):
    before = json.loads(before_path.read_text(encoding="utf-8-sig"))
    after = json.loads(after_path.read_text(encoding="utf-8-sig"))
    for key in ("inputSha256", "architecture", "preferredBase", "executableRanges"):
        assert before[key] == after[key], f"不可比较不同输入或映射：{key}"
    for report in (before, after):
        assert sha(report["boundaryIndex"]) == report["boundaryIndexSha256"], "边界索引身份不符"
    output.mkdir(parents=True, exist_ok=True)
    stem = after_path.name.removesuffix(".report.json")
    changes = output / f"{stem}.coverage-changes.tsv.gz"
    contract_changes = output / f"{stem}.contract-changes.tsv.gz"
    report_path = output / f"{stem}.coverage-comparison.json"
    transitions = collections.Counter()
    old_counts = collections.Counter()
    new_counts = collections.Counter()
    candidates = candidate_bytes = regressions = 0
    old_contracts, new_contracts = contract_stream(before), contract_stream(after)
    contracts_available = old_contracts is not None and new_contracts is not None
    support_rank = {"Exact": 2, "NormalPathOnly": 1, "ExceptionBoundaryOnly": 0}
    contract_candidates = contract_regressions = 0
    contract_transitions = collections.Counter()
    with gzip.open(changes, "wt", encoding="utf-8") as stream, gzip.open(contract_changes, "wt", encoding="utf-8") as contract_output:
        stream.write("address\tfileOffset\tlength\tbefore\tafter\n")
        contract_output.write("address\tfileOffset\tlength\tbeforeSupport\tafterSupport\tbeforeObligations\tafterObligations\tregression\n")
        for old, new in itertools.zip_longest(rows(before["boundaryIndex"]), rows(after["boundaryIndex"])):
            assert old is not None and new is not None, "候选数量改变"
            assert old[:3] == new[:3], f"解码边界改变：{old} -> {new}"
            address, offset, length, status = new
            transition = f"{old[3]}->{status}"
            transitions[transition] += 1
            old_counts[old[3]] += 1
            new_counts[status] += 1
            candidates += 1
            candidate_bytes += length
            if old[3] != status:
                stream.write(f"{address:X}\t{offset:X}\t{length}\t{old[3]}\t{status}\n")
            if old[3] == "V" and status != "V":
                regressions += 1
            old_contract = next(old_contracts, None) if old[3] == "V" and old_contracts is not None else None
            new_contract = next(new_contracts, None) if status == "V" and new_contracts is not None else None
            if old[3] == "V" and old_contracts is not None:
                assert old_contract is not None and old_contract[:3] == old[:3], "旧契约索引未对应全部有效候选"
            if status == "V" and new_contracts is not None:
                assert new_contract is not None and new_contract[:3] == new[:3], "新契约索引未对应全部有效候选"
            if old_contract is not None and new_contract is not None:
                contract_candidates += 1
                contract_transitions[f"{old_contract[3]}->{new_contract[3]}"] += 1
                regression = support_rank[new_contract[3]] < support_rank[old_contract[3]] or bool(set(new_contract[4]) - set(old_contract[4]))
                contract_regressions += int(regression)
                if old_contract[3:] != new_contract[3:]:
                    old_codes = ",".join(old_contract[4]) or "-"
                    new_codes = ",".join(new_contract[4]) or "-"
                    contract_output.write(f"{address:X}\t{offset:X}\t{length}\t{old_contract[3]}\t{new_contract[3]}\t{old_codes}\t{new_codes}\t{int(regression)}\n")
    if old_contracts is not None:
        assert next(old_contracts, None) is None, "旧契约索引含多余候选"
    if new_contracts is not None:
        assert next(new_contracts, None) is None, "新契约索引含多余候选"
    assert candidates == before["candidates"] == after["candidates"]
    for source, counts in ((before, old_counts), (after, new_counts)):
        assert candidate_bytes + source["truncatedOrUnalignedBytes"] == source["bytesCovered"]
        for status, key in (("V", "validated"), ("U", "unsupported"), ("I", "invalid"), ("E", "validationErrors")):
            assert counts[status] == source[key], (status, key, counts[status], source[key])
    forms = set(before["forms"]) | set(after["forms"])
    form_delta = {form: after["forms"].get(form, 0) - before["forms"].get(form, 0) for form in sorted(forms)}
    result = {
        "inputSha256": after["inputSha256"], "architecture": after["architecture"],
        "beforeReport": str(before_path.resolve()), "afterReport": str(after_path.resolve()),
        "beforeReportSha256": sha(before_path), "afterReportSha256": sha(after_path),
        "beforeAssemblySha256": before["implementationAssemblySha256"],
        "afterAssemblySha256": after["implementationAssemblySha256"],
        "beforeSemantics": before["semanticsVersion"], "afterSemantics": after["semanticsVersion"],
        "beforeProfile": before["profile"], "afterProfile": after["profile"],
        "candidatesCompared": candidates, "candidateBytesCompared": candidate_bytes,
        "transitions": dict(sorted(transitions.items())), "coverageRegressions": regressions,
        "validatedGain": after["validated"] - before["validated"],
        "beforeCandidateCoverage": before["validated"] / candidates if candidates else None,
        "afterCandidateCoverage": after["validated"] / candidates if candidates else None,
        "changedFormCounts": {form: delta for form, delta in form_delta.items() if delta},
        "structuralCoveragePassed": regressions == 0 and after["validationErrors"] == 0,
        "contractsCompared": contracts_available,
        "contractComparisonStatus": "compared" if contracts_available else "unavailable",
        "contractCandidatesCompared": contract_candidates if contracts_available else None,
        "contractTransitions": dict(sorted(contract_transitions.items())) if contracts_available else None,
        "contractRegressions": contract_regressions if contracts_available else None,
        "semanticContractRegressionFree": contract_regressions == 0 if contracts_available else None,
        "passed": regressions == 0 and after["validationErrors"] == 0 and (not contracts_available or contract_regressions == 0),
        "changeIndex": str(changes.resolve()), "changeIndexSha256": sha(changes),
        "contractChangeIndex": str(contract_changes.resolve()), "contractChangeIndexSha256": sha(contract_changes),
        "scriptSha256": sha(__file__),
        "meaning": "Structural coverage requires identical candidate boundaries and supported-status preservation. Contract comparison, when both indexes exist, detects support downgrades and added obligation codes; missing indexes are unavailable, not a semantic pass. Neither check proves semantic equivalence or reachable-code coverage. Profile and semantics changes remain explicit.",
    }
    report_path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(report_path.resolve())
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    raise SystemExit(compare(args.before, args.after, args.output))
