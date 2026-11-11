#!/usr/bin/env python3
"""核对两次输出逐字节一致，并用 nm 独立核对所有用例符号。"""
import argparse
from collections import defaultdict
import json
import filecmp
from pathlib import Path
import re
import subprocess
from extract import require, digest, write


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--truth', type=Path, required=True)
    p.add_argument('--repeat', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('--nm', default='nm')
    a = p.parse_args()
    require(a.truth.resolve() != a.repeat.resolve(), '必须比较两个不同输出目录')
    require(not a.report.resolve().is_relative_to(a.input.resolve()), '报告不能写入输入目录')
    for directory in (a.truth, a.repeat):
        require(not a.report.resolve().is_relative_to(directory.resolve()), '报告不能改变真值目录')
    left = {f.name: digest(f) for f in a.truth.iterdir() if f.is_file()}
    right = {f.name: digest(f) for f in a.repeat.iterdir() if f.is_file()}
    require(left == right, '两次输出不一致')
    require(all(filecmp.cmp(a.truth/name, a.repeat/name, shallow=False) for name in left), '逐字节比较失败')
    manifest = json.loads((a.truth/'manifest.json').read_text())
    for name, checksum in manifest['outputs'].items():
        require(left[name] == checksum, f'输出校验失败：{name}')
    cases = json.loads((a.truth/'cases.json').read_text())
    checks = json.loads((a.truth/'checks.json').read_text())
    verified_il = set(checks['independent_il_case_ids'])
    targets = cases[0]['mapping']['targets']
    nm = {}
    for target in targets:
        lib = a.input/'artifacts/il2cppOutput/build'/target/'libil2cpp.sym.so'
        result = subprocess.check_output([a.nm, '-S', '--defined-only', str(lib)], text=True)
        names = defaultdict(list)
        for line in result.splitlines():
            m = re.fullmatch(r'([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([TtWwIi])\s+(.+)', line)
            if m:
                names[m[4]].append((int(m[1], 16), int(m[2], 16)))
        nm[target] = names
    samples, categories = [], set()
    for case in cases:
        m, mapping = case['method'], case['mapping']
        require(m['id'] in verified_il, f'用例缺少独立 IL 核对：{m["id"]}')
        for target, functions in mapping['targets'].items():
            require(len(functions) == 1, '用例函数不唯一')
            f = functions[0]
            require(nm[target][f['symbol_name']] == [(int(f['address'], 16), f['size'])], f'nm 核对失败：{m["id"]}/{target}')
        category = case['case']['category']
        if category not in categories and len(samples) < 5:
            categories.add(category)
            samples.append(dict(method_id=m['id'], signature=m['signature'], il_hex=m['il_hex'],
                                il_sha256=m['il_sha256'], cpp_name=mapping['cpp_name'], targets=mapping['targets']))
    require(len(samples) == 5, '需要五个类别的抽查用例')
    write(a.report, dict(byte_identical=True, compared_files=len(left),
                         independent_il_cases=len(cases), nm_cases_per_target=len(cases), samples=samples))
    print(f'通过：{len(left)} 个文件逐字节一致；{len(cases)} 个用例 IL 独立核对和双目标 nm 核对；5 个抽查已写报告。')


if __name__ == '__main__':
    main()
