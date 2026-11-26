"""汇总逐入口记录；符号文件和用例清单只参与事后核对。"""
import argparse
import csv
import json
from collections import Counter, defaultdict
from pathlib import Path

from elftools.elf.elffile import ELFFile


def rows(path):
    with Path(path).open() as source:
        yield from csv.reader(source, delimiter="\t")


def report(prefix, symbols, cases):
    functions = {int(a, 16): (s, e, result) for a, s, e, result in rows(prefix + ".functions.local.tsv")}
    checked = {int(a, 16): (r, int(covered), int(total)) for a, r, covered, total in rows(prefix + ".execution.local.tsv")}
    lift = Counter(row[2] for row in functions.values())
    execution = Counter(row[0] for row in checked.values())
    edges = [sum(row[1] for row in checked.values()), sum(row[2] for row in checked.values())]
    summary = dict(entries=len(functions), lift=lift, selected=len(checked), execution=execution, edges=edges)
    if symbols:
        sizes = defaultdict(set)
        with open(symbols, "rb") as source:
            table = ELFFile(source).get_section_by_name(".symtab")
            for symbol in table.iter_symbols():
                if symbol["st_info"]["type"] == "STT_FUNC" and symbol["st_shndx"] != "SHN_UNDEF":
                    sizes[symbol["st_value"]].add(symbol["st_size"])
        mismatches = missing = 0
        with open(prefix + ".ranges.local.tsv", "w") as out:
            print("入口", "FDE起点", "FDE终点", "符号大小", sep="\t", file=out)
            for a, (s, e, _) in functions.items():
                expected = sorted(sizes[a])
                if not expected:
                    missing += 1
                if s == "-" or expected != [int(e, 16) - a] or a != int(s, 16):
                    mismatches += 1
                    print(f"{a:x}", s, e, ",".join(map(str, expected)) or "无", sep="\t", file=out)
        summary.update(range_mismatches=mismatches, missing_symbols=missing)
    if cases:
        with open(cases) as source:
            truth = json.load(source)
        with open(prefix + ".cases.local.tsv", "w") as out:
            print("用例", "入口", "提升", "执行", "已达出口", "全部出口", sep="\t", file=out)
            for case in truth:
                name = case["case"]["method"]
                targets = case["mapping"]["targets"].get("arm64-v8a", [])
                if not targets:
                    print(name, "-", "无映射", "未执行", "-", "-", sep="\t", file=out)
                for a in sorted({int(t["address"], 16) for t in targets}):
                    status = functions.get(a, (None, None, "代码地图无入口"))[2]
                    outcome, hit, total = checked.get(a, ("未执行", "-", "-"))
                    print(name, f"{a:x}", status, outcome, hit, total, sep="\t", file=out)
        summary["cases"] = len(truth)
    with open(prefix + ".summary.local.json", "w") as out:
        json.dump(summary, out, ensure_ascii=False, indent=2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("prefix")
    parser.add_argument("--symbols")
    parser.add_argument("--cases")
    args = parser.parse_args()
    report(args.prefix, args.symbols, args.cases)
