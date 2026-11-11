#!/usr/bin/env python3
"""生成交付组合与逐项核对记录。"""
import argparse
import copy
from pathlib import Path
import re
from generate import generate, dump, sha
from check_legacy import check


def differences(a, b, path=''):
    if type(a) is not type(b):
        return [{'path': path, 'single': a, 'runtime': b}]
    if isinstance(a, dict):
        out = []
        for key in sorted(a.keys() | b.keys()):
            out.extend(differences(a.get(key), b.get(key), path + '/' + key))
        return out
    if isinstance(a, list):
        if len(a) != len(b):
            return [{'path': path, 'single': a, 'runtime': b}]
        return [d for i, (x, y) in enumerate(zip(a, b)) for d in differences(x, y, path + '/' + str(i))]
    return [] if a == b else [{'path': path, 'single': a, 'runtime': b}]


def canonical(value):
    if isinstance(value, dict):
        return {k: re.sub(r'\bstruct ', '', v) if k == 'type' else canonical(v) for k, v in value.items()}
    if isinstance(value, list):
        return [canonical(v) for v in value]
    return value


def require(condition, reason):
    if not condition:
        raise ValueError(reason)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--runtime-2022', required=True, type=Path)
    p.add_argument('--single-headers', required=True, type=Path)
    p.add_argument('--output', default=Path('spec'), type=Path)
    p.add_argument('--legacy-ref', default='attempt-12')
    a = p.parse_args()
    arm = generate(a.runtime_2022, '2022.3.62f2', 'android-arm64', True)
    x64 = generate(a.runtime_2022, '2022.3.62f2', 'android-x64', True)
    require(arm['records'] == x64['records'], 'Android 结构不同，必须拆分数据文件')
    require(arm['constants'] == x64['constants'], 'Android 常量不同，必须拆分数据文件')
    comparisons = {}
    for target, real in [('android-arm64', arm), ('android-x64', x64)]:
        source = a.single_headers / '2022.3.62f2.h'
        raw = generate(source, '2022.3.62f2', target, restore_arrays=False)
        restored = generate(source, '2022.3.62f2', target)
        common = sorted(real['records'].keys() & raw['records'].keys())
        raw_diff = differences({n: raw['records'][n] for n in common}, {n: real['records'][n] for n in common})
        restored_diff = differences(canonical({n: restored['records'][n] for n in common}), canonical({n: real['records'][n] for n in common}))
        require(not restored_diff, restored_diff)
        shared_constants = sorted(real['constants'].keys() & raw['constants'].keys())
        constant_diff = differences({n: raw['constants'][n] for n in shared_constants}, {n: real['constants'][n] for n in shared_constants})
        require(not constant_diff, constant_diff)
        comparisons[target] = {'single_source': raw['source'], 'runtime_source': real['source'], 'common_records': len(common), 'common_constants': len(shared_constants), 'raw_differences': raw_diff, 'restored_differences': restored_diff, 'constant_differences': constant_diff, 'single_only_records': sorted(raw['records'].keys() - real['records'].keys()), 'runtime_only_records': sorted(real['records'].keys() - raw['records'].keys()), 'single_only_constants': sorted(raw['constants'].keys() - real['constants'].keys()), 'runtime_only_constants': sorted(real['constants'].keys() - raw['constants'].keys())}
    merged = copy.deepcopy(arm)
    merged['targets'] = [merged.pop('target'), x64['target']]
    merged['merge_basis'] = '两个目标逐项比较 records 和 constants 完全相同；基础类型尺度分别保留。'
    legacy = check(merged, a.legacy_ref)
    require(legacy['summary']['不一致'] == legacy['summary']['数据里没有'] == 0, legacy['summary'])
    windows = generate(a.single_headers / '2021.3.28f1.h', '2021.3.28f1', 'windows-x64')
    windows['limitations'] = ['单文件头不含 il2cpp-tabledefs.h 属性宏；不从其他 Unity 版本补值。', '零长数组按提取脚本的转换还原；未与本版本完整运行时头文件独立比较。']
    report = {'source_comparison': comparisons, 'android_targets_equal': True, 'legacy': legacy, 'extractor_sha256': sha(a.single_headers / 'extract.py'), 'explanations': ['原始单文件头的零长数组被 headers/extract.py 改为 [32]；恢复声明后重新交给 clang 计算，三个运行时结构的大小及数组字段大小与真实头文件相同。', 'struct 标签与 typedef 名称是同一类型的两种拼写；比较时只去除类型字符串的 struct 前缀。', '单文件头多出元数据、快照及 Il2CppClass 拆分辅助结构；真实头文件多出属性宏与静态整数常量。共有集合逐项比较，不把非共有项算作一致。']}
    dump(a.output / 'unity-2022.3.62f2-android-lp64.json', merged)
    dump(a.output / 'unity-2021.3.28f1-windows-x64-llp64.json', windows)
    dump(a.output / 'checks.json', report)
    for name, data in [('2022 Android', merged), ('2021 Windows', windows)]:
        print(name, 'records=', len(data['records']), 'constants=', len(data['constants']))
    print(legacy['summary'])

if __name__ == '__main__':
    main()
