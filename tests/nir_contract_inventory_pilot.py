"""从完整入口清单截取确定的诊断样本；不计作全量验证。"""
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest().upper()


def create(path):
    manifest = json.loads(path.read_text(encoding="utf-8"))
    selected = []
    counts = Counter()
    with (path.parent / manifest["entriesFile"]).open(encoding="utf-8") as stream:
        for line in stream:
            entry = json.loads(line)
            group = "known" if entry["signatureStatus"] == "known" else "other"
            limit = 500 if group == "known" else 100
            if counts[group] < limit:
                selected.append(entry)
                counts[group] += 1
            if counts["known"] == 500 and counts["other"] == 100:
                break
    assert counts == {"known": 500, "other": 100}
    output = path.with_name(path.stem + "-pilot.json")
    entries_path = output.with_suffix(".entries.jsonl")
    with entries_path.open("w", encoding="utf-8") as stream:
        for entry in selected:
            stream.write(json.dumps(entry, ensure_ascii=False, separators=(",", ":")) + "\n")
    pilot = deepcopy(manifest)
    pilot["entriesFile"] = entries_path.name
    pilot["entriesSha256"] = digest(entries_path)
    pilot["entryCount"] = len(selected)
    pilot["summary"]["entries"] = dict(Counter(entry["signatureStatus"] for entry in selected))
    evidence = Counter()
    for entry in selected:
        evidence.update({source["kind"] for source in entry["evidence"]})
    pilot["summary"]["entryEvidence"] = dict(evidence)
    pilot["pilot"] = {"enabled": True, "purpose": "timing and crash diagnosis only; not full-corpus validation",
                      "selection": "first 500 known and first 100 combined non-known entries, address order",
                      "sourceManifest": path.name, "sourceManifestSha256": digest(path), "sourceEntryCount": manifest["entryCount"],
                      "methodScope": "methodsFile and metadata/provider remain the full source inventory",
                      "generatorSha256": digest(Path(__file__))}
    output.write_text(json.dumps(pilot, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(output), "entryCount": len(selected), "statuses": pilot["summary"]["entries"]}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifests", type=Path, nargs="+")
    args = parser.parse_args()
    for path in args.manifests:
        create(path)


if __name__ == "__main__":
    main()
