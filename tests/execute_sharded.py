"""对显式输入的恢复产物分片执行，合并判定与验证证据。"""
import argparse
import json
import concurrent.futures
import os
import re
import subprocess
import sys


def main(argv):
    extra = []
    if "--" in argv:
        extra = argv[argv.index("--") + 1:]
        argv = argv[:argv.index("--")]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory")
    parser.add_argument("--binary", required=True)
    parser.add_argument("--metadata", required=True)
    parser.add_argument("--tests", required=True)
    parser.add_argument("--shards", type=int, default=4)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args(argv)
    directory, tests, shards, jobs = args.directory, args.tests, args.shards, args.jobs
    if not 1 <= jobs <= shards:
        raise ValueError("要求 1 <= jobs <= shards")
    logs = os.path.join(directory, "shards")
    os.makedirs(logs, exist_ok=True)

    def run(k):
        command = ["dotnet", tests, "execute", args.binary, args.metadata, directory, "--shard", f"{k}/{shards}", *extra]
        with open(os.path.join(logs, f"{k}.log"), "w", encoding="utf-8") as log:
            return k, subprocess.run(command, stdout=log, stderr=subprocess.STDOUT).returncode

    def finished(k):
        # 正常结束的分片一定写出了判定汇总行；异常终止的分片没有
        with open(os.path.join(logs, f"{k}.log"), encoding="utf-8") as f:
            return any("判定：" in line for line in f)

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        codes = dict(executor.map(run, range(shards)))
    # 进程异常终止（没有判定汇总）的分片逐个重跑，最多两次；断言失败（有汇总、返回 1）的不重跑
    for attempt in range(2):
        for k in [k for k in range(shards) if not finished(k)]:
            print(f"  分片 {k} 异常终止（返回码 {codes[k]}），第 {attempt + 1} 次重跑", file=sys.stderr)
            codes[k] = run(k)[1]
    failed = [k for k in range(shards) if codes[k] != 0]

    rows = []
    for k in range(shards):
        path = os.path.join(directory, f"execution-{k}-of-{shards}.tsv")
        if os.path.exists(path):
            with open(path, encoding="utf-8") as f:
                rows += [line.rstrip("\n").split("\t") for line in f if line.strip()]
            os.remove(path)
    rows.sort(key=lambda r: int(r[0], 16))
    with open(os.path.join(directory, "execution.tsv"), "w", encoding="utf-8") as f:
        f.writelines("\t".join(r) + "\n" for r in rows)

    scope = {}
    with open(os.path.join(directory, "recovery.jsonl"), encoding="utf-8") as f:
        for line in f:
            record = json.loads(line)
            if not record.get("dependency", False):
                scope[record["address"]] = record["bytes"]
    with open(os.path.join(directory, "emitted.tsv"), encoding="utf-8") as f:
        expected = {(r[3], r[4]) for line in f if (r := line.rstrip("\n").split("\t"))}
    actual = {(r[0], r[1]) for r in rows}
    if actual != expected or len(actual) != len(rows):
        raise ValueError("执行对照结果与全部写出方法不一致（含依赖）；不得漏检或重复")
    target_scope = scope
    total = sum(target_scope.values())
    entries, reasons = {}, {}
    target_rows = [r for r in rows if len(r) < 9 or r[8] != "dependency"]
    for r in target_rows:
        entries.setdefault(r[2], {})[r[0]] = int(r[7])
        if r[2] == "not-checkable":
            reasons[r[5]] = reasons.get(r[5], 0) + 1
    counts = {v: sum(1 for r in target_rows if r[2] == v) for v in ("verified", "mismatch", "not-checkable")}
    size = {v: sum(entries.get(v, {}).values()) for v in counts}
    print(f"  判定：" + "，".join(f"{v} {counts[v]} 方法 / {size[v]} 字节" for v in counts) + f"（{shards} 片）")
    print(f"  已验证字节：{size['verified']} / {total} = {size['verified'] / max(1, total):.4%}（范围与各判定均按入口去重）")
    for reason, count in sorted(reasons.items(), key=lambda x: -x[1]):
        print(f"    不可检查 {count:5}  {reason}")

    dependencies = [r for r in rows if len(r) >= 9 and r[8] == "dependency"]
    print("  依赖访问器：" + "，".join(f"{v} {sum(r[2] == v for r in dependencies)}" for v in ("verified", "mismatch", "not-checkable", "language-defined")))
    exceptions = [r for r in target_rows if len(r) >= 11 and int(r[10]) > 0]
    if exceptions:
        injected = sum(int(r[9]) for r in exceptions)
        cases = 32 * len(exceptions)
        print(f"  F5 异常方法 {len(exceptions)}，两侧实际注入抛出 {injected}/{cases} 用例 = {injected / cases:.4%}")
    evidence = set()
    for k in range(shards):
        path = os.path.join(directory, f"accessor-verified-{k}-of-{shards}.tsv")
        if os.path.exists(path):
            with open(path, encoding="utf-8") as f:
                evidence.update(line.rstrip("\n") for line in f if line.strip() and not line.startswith("#"))
            os.remove(path)
    with open(os.path.join(directory, "accessor-verified.tsv"), "w", encoding="utf-8") as f:
        f.write("# F9：访问器自身全部 32 用例 verified；入口、身份、原生 SHA256、CIL SHA256\n")
        f.writelines(line + "\n" for line in sorted(evidence))
    mutants = [0, 0, 0, 0, 0]
    missed = []
    pattern = re.compile(r"变异：(\d+) 个，检出 (\d+)，未检出 (\d+)，不可比较 (\d+)，非法 IL (\d+)")
    for k in range(shards):
        with open(os.path.join(logs, f"{k}.log"), encoding="utf-8") as f:
            for line in f:
                if line.startswith(("  ✗", "  ?", "✗")):
                    print(line.rstrip())
                elif (m := pattern.search(line)) is not None:
                    mutants = [a + int(b) for a, b in zip(mutants, m.groups())]
                elif line.startswith("    未检出："):
                    missed.append(line.rstrip())
    if "--mutants" in extra:
        print(f"  变异：{mutants[0]} 个，检出 {mutants[1]}，未检出 {mutants[2]}，不可比较 {mutants[3]}，非法 IL {mutants[4]}；"
              f"检出率 {mutants[1] / max(1, mutants[1] + mutants[2]):.1%}")
        for line in missed:
            print(line)
    if failed:
        print(f"  ✗ 失败的分片：{failed}（日志见 {logs}/）")
    return 1 if failed or any(r[2] == "mismatch" for r in rows) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
