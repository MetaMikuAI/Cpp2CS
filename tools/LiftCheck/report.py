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


def switch_results(prefix, functions, suspects):
    confirmed = {(int(a, 16), int(pc, 16)): (int(n), result)
                 for a, pc, n, result in rows(prefix + ".switches.local.tsv")}
    items = list(rows(prefix + ".items.local.tsv"))
    outcomes = {a: result for a, _, _, _, _, result in items}
    summary = dict(confirmed_sites=len(confirmed), checked=len(outcomes),
                   outcomes=Counter(outcomes.values()), checked_sites=len(items),
                   ordinary_items=sum(int(row[2]) for row in items),
                   covered_items=sum(int(row[3]) for row in items),
                   total_items=sum(int(row[4]) for row in items))
    if suspects:
        reasons = {int(a, 16): (int(pc, 16), reason) for a, pc, reason in rows(prefix + ".rejected.local.tsv")}
        groups = Counter()
        with open(prefix + ".suspects.local.tsv", "w") as out:
            for a, pc, _, _, _, kind in rows(suspects):
                if kind != "疑表":
                    continue
                entry, branch = int(a, 16), int(pc, 16)
                result = functions[entry][2]
                detail = result
                if (entry, branch) in confirmed:
                    group = "已确认"
                elif entry in reasons:
                    rejected, detail = reasons[entry]
                    group = detail if rejected == branch else "同函数另一间接跳转未证实"
                    detail = f"{rejected:x} {detail}"
                else:
                    group = result
                groups[group] += 1
                print(a, pc, group, result, detail, sep="\t", file=out)
        summary["suspects"] = groups
    return summary


def report(prefix, symbols, cases, suspects=None):
    functions = {int(a, 16): (s, e, result) for a, s, e, result in rows(prefix + ".functions.local.tsv")}
    checked = {int(a, 16): (r, int(covered), int(total)) for a, r, covered, total in rows(prefix + ".execution.local.tsv")}
    lift = Counter(row[2] for row in functions.values())
    execution = Counter(row[0] for row in checked.values())
    edges = [sum(row[1] for row in checked.values()), sum(row[2] for row in checked.values())]
    summary = dict(entries=len(functions), lift=lift, selected=len(checked), execution=execution, edges=edges)
    coverage_file = Path(prefix + ".coverage.local.tsv")
    if coverage_file.exists():
        coverage = list(rows(coverage_file))
        summary["ordinary_edges"] = sum(int(r[1]) for r in coverage)
        summary["biased_edges"] = sum(int(r[2]) for r in coverage)
        destinations = defaultdict(Counter)
        groups = defaultdict(Counter)
        for _, group, old, outcome, *_ in rows(prefix + ".followup.local.tsv"):
            if old:
                destinations[old][outcome] += 1
            groups[group][outcome] += 1
        summary.update(destinations=destinations, groups=groups)
    if Path(prefix + ".items.local.tsv").exists():
        summary["switches"] = switch_results(prefix, functions, suspects)
    branch_file = Path(prefix + ".branches.local.tsv")
    if branch_file.exists():
        classes = defaultdict(Counter)
        examples = defaultdict(list)
        for entry, _, sp, lr, origin, table in rows(branch_file):
            for dimension, value in (("栈与链接", sp + "/" + lr), ("来源", origin), ("跳转表形态", table)):
                classes[dimension][value] += 1
                if len(examples[(dimension, value)]) < 3:
                    examples[(dimension, value)].append(entry)
        if sum(classes["来源"].values()) != lift["间接跳转目标未证实"]:
            raise ValueError("间接跳转分类与提升清单不一致")
        summary["branches"] = {k: {v: [count, examples[(k, v)]] for v, count in c.items()} for k, c in classes.items()}
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
    parser.add_argument("--suspects", help="前次间接跳转分类清单，按入口和 BR 地址核实疑表去向")
    args = parser.parse_args()
    report(args.prefix, args.symbols, args.cases, args.suspects)
