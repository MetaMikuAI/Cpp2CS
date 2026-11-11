#!/usr/bin/env python3
"""使用 GNU readelf 转储独立核对指定用例的内联名称与地址范围。"""
import argparse
import json
from pathlib import Path
import re
from extract import require, write, digest

DIE = re.compile(r'^\s*<\d+><([0-9a-f]+)>:')
ATTR = re.compile(r'DW_AT_(\w+)\s*:\s*(.*)')


def blocks(path, wanted):
    result = {}
    current = None
    with path.open() as stream:
        for line in stream:
            match = DIE.match(line)
            if match:
                current = int(match[1], 16)
                if current in wanted:
                    result[current] = {}
            elif current in wanted:
                match = ATTR.search(line)
                if match:
                    result[current][match[1]] = match[2].strip()
    require(wanted <= result.keys(), 'readelf 转储缺少请求的 DIE')
    return result


def reference(value):
    return int(re.search(r'<0x([0-9a-f]+)>', value)[1], 16)


def number(value):
    return int(re.search(r'0x[0-9a-f]+', value)[0], 16)


def verify(cases, info, range_path):
    records = [r for c in cases for r in c['records']]
    wanted = {int(r['id'], 16) for r in records}
    dies = blocks(info, wanted)
    while True:
        refs = {reference(a[k]) for a in dies.values() for k in ('abstract_origin', 'specification') if k in a} - dies.keys()
        if not refs:
            break
        dies.update(blocks(info, refs))
    def attribute(offset, key):
        attrs = dies[offset]
        if key in attrs:
            return attrs[key]
        for ref in ('abstract_origin', 'specification'):
            if ref in attrs:
                value = attribute(reference(attrs[ref]), key)
                if value is not None:
                    return value
        return None
    needed = {number(dies[int(r['id'], 16)]['ranges']) for r in records if 'ranges' in dies[int(r['id'], 16)]}
    ranges = {offset: [] for offset in needed}
    with range_path.open() as stream:
        for line in stream:
            match = re.fullmatch(r'\s*([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s*', line)
            if match and int(match[1], 16) in needed:
                ranges[int(match[1], 16)].append([hex(int(match[2], 16)), hex(int(match[3], 16))])
    checked = []
    for record in records:
        offset = int(record['id'], 16)
        name = attribute(offset, 'name')
        require(name is not None and name.rsplit(': ', 1)[-1] == record['name'], f'名称不一致：{record["id"]}')
        attrs = dies[offset]
        if 'ranges' in attrs:
            actual = ranges[number(attrs['ranges'])]
        elif 'low_pc' in attrs:
            low = number(attrs['low_pc'])
            high = number(attrs['high_pc'])
            actual = [[hex(low), hex(high if '(addr)' in attrs['high_pc'] else low+high)]]
        else:
            actual = []
        require(actual == record['ranges'], f'范围不一致：{record["id"]}')
        checked.append(dict(id=record['id'], name=record['name'], ranges=actual))
    return dict(cases=[c['cpp_name'] for c in cases], records=checked, info_sha256=digest(info), ranges_sha256=digest(range_path))


def validate_tree(rows):
    counts = dict(functions=len(rows), debug_functions=0, records=0, runtime_records=0,
                  multi_range_records=0, empty_range_records=0, maximum_depth=0)
    for function in rows:
        counts['debug_functions'] += function['debug_function_found']
        records = {r['id']: r for r in function['records']}
        require(len(records) == len(function['records']), '函数内 DIE 身份重复')
        start = int(function['address'], 16)
        for record in records.values():
            seen = {record['id']}
            current = record
            while current['parent']:
                parent = current['parent']
                require(parent in records and parent not in seen, '父引用缺失或形成环')
                seen.add(parent)
                current = records[parent]
            for lo, hi in record['ranges']:
                require(start <= int(lo, 16) <= int(hi, 16) <= start + function['size'], '内联范围越过函数符号边界')
            counts['records'] += 1
            counts['runtime_records'] += record['origin'] == 'runtime_or_library'
            counts['multi_range_records'] += len(record['ranges']) > 1
            counts['empty_range_records'] += not record['ranges']
            counts['maximum_depth'] = max(counts['maximum_depth'], len(seen))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--truth', type=Path, required=True)
    parser.add_argument('--repeat', type=Path, required=True)
    parser.add_argument('--info', action='append', required=True, help='目标=readelf --debug-dump=info --wide 的转储')
    parser.add_argument('--ranges', action='append', required=True, help='目标=readelf --debug-dump=Ranges --wide 的转储')
    parser.add_argument('--case', action='append', required=True, help='完整类型名.方法名')
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    require(not args.report.exists(), '不覆盖已有报告')
    files = sorted(p.name for p in args.truth.glob('*.json'))
    require(files == sorted(p.name for p in args.repeat.glob('*.json')), '两次输出文件集合不同')
    for name in files:
        require((args.truth/name).read_bytes() == (args.repeat/name).read_bytes(), f'两次输出不同：{name}')
    infos = dict(s.split('=', 1) for s in args.info)
    ranges = dict(s.split('=', 1) for s in args.ranges)
    report = dict(reproducible_files=files, targets={})
    for target in ('arm64-v8a', 'x86_64'):
        cases = json.loads((args.truth/('inline-cases.'+target+'.json')).read_text())
        selected = [c for c in cases if c['case']['type']+'.'+c['case']['method'] in args.case]
        require(len(selected) == len(set(args.case)), '请求的用例不唯一或不存在')
        report['targets'][target] = verify(selected, Path(infos[target]), Path(ranges[target]))
        rows = json.loads((args.truth/('inlines.'+target+'.json')).read_text())
        report['targets'][target]['structure'] = validate_tree(rows)
    write(args.report, report)
    print({t: len(r['records']) for t, r in report['targets'].items()})


if __name__ == '__main__':
    main()
