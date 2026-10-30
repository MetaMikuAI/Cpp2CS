#!/usr/bin/env python3
"""两次 recover（含全量执行对照）的通用前后对比。

    python3 tests/report.py diff <前目录> <后目录> [--check] [--json <输出.json>]

目录是 recover 的输出（含 recovery.jsonl；有 execution.tsv 时一并比较判定）。口径与 tests/execute_sharded.py 相同：
目标范围不含依赖访问器，字节取 L0 函数大小、同一入口只计一次。洞桶是独立洞原因的第一个词，一个方法可属于多个桶。
--check：后目录出现 mismatch、not-checkable，或以前写出 / verified 的目标方法丢失时返回 1。
"""
import json
import pathlib
import sys


def load(directory):
    path = pathlib.Path(directory)
    rows = [json.loads(line) for line in (path / "recovery.jsonl").open(encoding="utf-8")]
    targets = [r for r in rows if not r.get("dependency")]
    verdicts = {}
    execution = path / "execution.tsv"
    if execution.exists():
        for line in execution.read_text(encoding="utf-8").splitlines():
            fields = line.split("\t")
            if fields[0].startswith("0x") and (len(fields) < 9 or fields[8] != "dependency"):
                verdicts[(fields[0], fields[1])] = fields[2]
    return {
        "scope": {r["address"]: r["bytes"] for r in targets},
        "emitted": {(r["address"], r["method"]) for r in targets if r["status"] == "emitted"},
        "verdicts": verdicts,
        "buckets": buckets(targets),
        "bytes": {(r["address"], r["method"]): r["bytes"] for r in targets},
        "executed": execution.exists(),
    }


def buckets(targets):
    result = {}
    for r in targets:
        names = {h.get("category") or h["reason"].split(" ")[0] for h in r.get("holes") or [] if not h.get("derived")}
        if r.get("emitProblem"):
            names.add("CIL/" + r["emitProblem"].split(" ")[0])
        for name in names:
            result.setdefault(name, {})[r["address"]] = r["bytes"]
    return result


def entry_bytes(keys, sizes):
    return sum({address: sizes[(address, method)] for address, method in keys}.values())


def verified(data, verdict="verified"):
    return {k for k, v in data["verdicts"].items() if v == verdict}


def diff(before_dir, after_dir, check=False, json_path=None):
    before, after = load(before_dir), load(after_dir)
    total = sum(after["scope"].values())
    out = {"before": before_dir, "after": after_dir, "scope": {"methods": len(after["bytes"]), "bytes": total}}
    print(f"范围：{len(after['bytes'])} 方法 / {total} 字节（入口去重）")
    if before["scope"] != after["scope"]:
        print(f"  注意：两边的范围不同（前 {len(before['scope'])} 个入口，后 {len(after['scope'])} 个入口）")

    def line(name, a, b, sizes_a, sizes_b):
        ba, bb = entry_bytes(a, sizes_a), entry_bytes(b, sizes_b)
        print(f"{name}：{len(a)} 方法 / {ba} 字节 → {len(b)} 方法 / {bb} 字节（{len(b) - len(a):+} 方法，{bb - ba:+} 字节，"
              f"占比 {ba / max(1, total):.4%} → {bb / max(1, total):.4%}）")
        gained, lost = sorted(b - a), sorted(a - b)
        print(f"  新增 {len(gained)}，丢失 {len(lost)}")
        for address, method in lost[:10]:
            print(f"    丢失 {address} {method}")
        out[name] = {"before": len(a), "after": len(b), "beforeBytes": ba, "afterBytes": bb,
                     "gained": [list(k) for k in gained], "lost": [list(k) for k in lost]}
        return lost

    lost_emitted = line("写出", before["emitted"], after["emitted"], before["bytes"], after["bytes"])
    lost_verified = []
    if before["executed"] and after["executed"]:
        lost_verified = line("verified", verified(before), verified(after), before["bytes"], after["bytes"])
    bad = {v: sorted(verified(after, v)) for v in ("mismatch", "not-checkable")} if after["executed"] else {}
    for v, keys in bad.items():
        print(f"{v}：{len(keys)}" + "".join(f"\n    {a} {m}" for a, m in keys[:10]))
    out["bad"] = {v: [list(k) for k in keys] for v, keys in bad.items()}

    print("独立洞分桶（方法 / 字节，前 → 后，按字节变化排序）：")
    names = set(before["buckets"]) | set(after["buckets"])
    changes = []
    for name in names:
        a, b = before["buckets"].get(name, {}), after["buckets"].get(name, {})
        changes.append((sum(b.values()) - sum(a.values()), name, len(a), sum(a.values()), len(b), sum(b.values())))
    for delta, name, ma, ba, mb, bb in sorted(changes, key=lambda c: (-abs(c[0]), c[1])):
        if ma != mb or ba != bb:
            print(f"  {name:12} {ma:6} / {ba:9} → {mb:6} / {bb:9}（{mb - ma:+} / {delta:+}）")
    if all(c[2] == c[4] and c[3] == c[5] for c in changes):
        print("  全部不变")
    out["buckets"] = {c[1]: {"before": [c[2], c[3]], "after": [c[4], c[5]]} for c in changes}

    if json_path:
        pathlib.Path(json_path).write_text(json.dumps(out, ensure_ascii=False, indent=1), encoding="utf-8")
    failed = check and (any(bad.values()) or lost_emitted or lost_verified)
    if check:
        print("检查：" + ("失败（mismatch、not-checkable，或丢失以前写出 / verified 的目标方法）" if failed else "通过"))
    return 1 if failed else 0


def main(argv):
    if len(argv) >= 3 and argv[0] == "diff":
        options = argv[3:]
        json_path = options[options.index("--json") + 1] if "--json" in options else None
        return diff(argv[1], argv[2], "--check" in options, json_path)
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
