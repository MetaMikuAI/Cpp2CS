"""流式比较规范导出。数据行按 (kind, index) 排序，末行为 summary。"""
import argparse
from collections import Counter
from contextlib import ExitStack
import json
from pathlib import Path

FIELDS = {
    "field": "flags index instanceOffset kind name ordinal owner staticOffset threadStaticOffset type",
    "generic-method": "entry index instance invoker kind",
    "image": "assembly culture end index kind name start version",
    "invoker": "entry index kind",
    "method": "entry flags genericParameters implFlags index invoker kind name owner signature token",
    "registration": "code index kind metadata",
    "runtime-type": "index kind type",
    "string-literal": "index kind sha256",
    "type": "declaring fields flags genericCount genericParameters index interfaces kind methods name namespace parent",
    "summary": "counts index kind",
}


def rows(stream):
    previous = None
    counts = Counter()
    summary = False
    for line_number, line in enumerate(stream, 1):
        obj = json.loads(line)
        kind, index = obj["kind"], obj["index"]
        if summary or kind not in FIELDS or list(obj) != FIELDS[kind].split():
            raise ValueError(f"{stream.name}:{line_number} 字段集合、字段顺序或汇总位置无效")
        key = (kind == "summary", kind, index)
        if type(index) is not int or index < 0 or previous is not None and key <= previous:
            raise ValueError(f"{stream.name}:{line_number} 身份键无效、无序或重复")
        if kind == "summary":
            if index != 0 or obj["counts"] != dict(counts):
                raise ValueError(f"{stream.name}:{line_number} 汇总与数据行不符")
            summary = True
        else:
            counts[kind] += 1
        previous = key
        yield key, line, obj
    if not summary:
        raise ValueError(f"{stream.name} 缺少汇总")


def compare(old, new, differences):
    totals = {kind: [0, 0, 0, 0] for kind in FIELDS}
    left, right = rows(old), rows(new)
    a, b = next(left, None), next(right, None)
    while a is not None or b is not None:
        key = min(row[0] for row in (a, b) if row is not None)
        has_a = a is not None and a[0] == key
        has_b = b is not None and b[0] == key
        equal = has_a and has_b and a[1] == b[1]
        stats = totals[key[1]]
        stats[0] += has_a
        stats[1] += has_b
        stats[2] += equal
        stats[3] += not equal
        if not equal:
            print(json.dumps({"kind": key[1], "index": key[2], "old": a[2] if has_a else None,
                              "new": b[2] if has_b else None}, ensure_ascii=True), file=differences)
        if has_a:
            a = next(left, None)
        if has_b:
            b = next(right, None)
    print("种类\t旧条目\t新条目\t一致\t差异")
    for kind, stats in totals.items():
        print(kind, *stats, sep="\t")
    return int(any(s[3] for s in totals.values()))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("old", "new", "differences"):
        parser.add_argument(arg, type=Path)
    args = parser.parse_args()
    if args.differences.resolve() in (args.old.resolve(), args.new.resolve()):
        parser.error("差异文件与输入重名")
    with ExitStack() as stack:
        old = stack.enter_context(args.old.open("rb"))
        new = stack.enter_context(args.new.open("rb"))
        diff = stack.enter_context(args.differences.open("w", encoding="utf-8"))
        raise SystemExit(compare(old, new, diff))
