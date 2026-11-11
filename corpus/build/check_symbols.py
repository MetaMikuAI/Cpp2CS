"""按完整生成器方法前缀核对函数符号；数据、未定义符号和内联副本不计。"""
import argparse
import json
from pathlib import Path
import re
import subprocess


def check(methods, text):
    symbols = set()
    for line in text.splitlines():
        match = re.fullmatch(r"\s*[0-9a-fA-F]+\s+[tT]\s+(\S+)\s*", line)
        if match:
            symbols.add(match[1])
    missing, ambiguous, found = [], [], []
    for method in methods:
        pattern = re.compile(re.escape(method["symbolPrefix"]) + r"[0-9A-Fa-f]+$")
        matches = sorted(s for s in symbols if pattern.fullmatch(s))
        record = {**method, "symbols": matches}
        if len(matches) == 1:
            found.append(record)
        elif not matches:
            missing.append(record)
        else:
            ambiguous.append(record)
    return {"total": len(methods), "found": len(found), "missing": missing,
            "ambiguous": ambiguous, "matches": found}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--methods", type=Path, required=True)
    parser.add_argument("--nm", help="NDK llvm-nm 路径；使用 --symbols 时不需要")
    parser.add_argument("--library", action="append", default=[], metavar="ABI=PATH")
    parser.add_argument("--symbols", action="append", default=[], metavar="ABI=PATH")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    methods = json.loads(args.methods.read_text(encoding="utf-8"))
    if not methods or len({m['symbolPrefix'] for m in methods}) != len(methods):
        parser.error("方法清单为空或包含重复前缀")
    inputs = {}
    for value in args.library:
        abi, path = value.split("=", 1)
        if not args.nm or abi in inputs:
            parser.error("缺少 --nm 或 ABI 重复")
        inputs[abi] = subprocess.check_output([args.nm, "--defined-only", path], text=True, encoding="utf-8")
    for value in args.symbols:
        abi, path = value.split("=", 1)
        if abi in inputs:
            parser.error("ABI 重复")
        inputs[abi] = Path(path).read_text(encoding="utf-8")
    if set(inputs) != {"arm64-v8a", "x86_64"}:
        parser.error("必须同时提供 arm64-v8a 和 x86_64")
    results = {abi: check(methods, data) for abi, data in inputs.items()}
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    for abi, result in results.items():
        print(f"{abi}: 用例方法数 / 找到数 = {result['total']} / {result['found']}")
        print("未找到: " + ", ".join(m['type'] + '.' + m['method'] for m in result['missing']))
        print("不唯一: " + ", ".join(m['type'] + '.' + m['method'] for m in result['ambiguous']))
    return int(any(r['found'] != r['total'] for r in results.values()))


if __name__ == "__main__":
    raise SystemExit(main())
