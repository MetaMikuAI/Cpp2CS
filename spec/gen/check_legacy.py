#!/usr/bin/env python3
"""逐项核对旧版 RuntimeLayout；名称映射不包含偏移数值。"""
import argparse
import json
from pathlib import Path
import re
import subprocess
from generate import dump


def old_constants(ref):
    def read(path):
        return subprocess.check_output(['git', 'show', ref + ':' + path], text=True)
    text = read('src/Cpp2CS.Core/Facts/RuntimeLayout.cs')
    model = read('src/Cpp2CS.Core/Model/TypeLayout.cs')
    text = re.sub(r'//[^\n]*', '', text)
    result = {}
    for kind, body in re.findall(r'public const (int|string)\s+(.*?);', text, re.S):
        for item in body.split(','):
            name, value = map(str.strip, item.split('='))
            if kind == 'string':
                result[name] = value.strip('"')
            elif value == 'Cpp2CS.Model.TypeLayout.ObjectHeaderSize':
                result[name] = int(re.search(r'ObjectHeaderSize\s*=\s*(\w+)', model)[1], 0)
            else:
                result[name] = int(value, 0)
    return result


def check(data, ref='attempt-12'):
    mapping = json.loads(Path(__file__).with_name('legacy-map.json').read_text())
    rows = []
    for name, old in old_constants(ref).items():
        path = mapping.get(name)
        value = None
        if path == ['unity_version']:
            value = data['unity_version']
        elif path and path[0] in data['records']:
            record = data['records'][path[0]]
            if path[1] == 'size':
                value = record['size']
            else:
                field = next((f for f in record['fields'] if f['name'] == path[1]), None)
                if field:
                    value = field['offset_bits'] // 8
        status = '数据里没有' if value is None else '一致' if value == old else '不一致'
        rows.append({'name': name, 'old': old, 'generated': value, 'query': path, 'status': status})
    return {'reference': ref, 'summary': {s: sum(r['status'] == s for r in rows) for s in ['一致', '不一致', '数据里没有']}, 'items': rows}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('data', type=Path)
    p.add_argument('--ref', default='attempt-12')
    p.add_argument('--output', required=True, type=Path)
    a = p.parse_args()
    result = check(json.loads(a.data.read_text()), a.ref)
    dump(a.output, result)
    print(json.dumps(result['summary'], ensure_ascii=False))
    if result['summary']['数据里没有'] or result['summary']['不一致']:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
