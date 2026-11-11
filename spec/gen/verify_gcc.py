#!/usr/bin/env python3
"""用宿主 GCC 独立核对 Android x64 的结构与非位域字段。"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile
from generate import PRELUDE, PLATFORM


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--runtime-headers', required=True, type=Path)
    p.add_argument('--data', required=True, type=Path)
    a = p.parse_args()
    data = json.loads(a.data.read_text())
    assert any(t['triple'] == 'x86_64-linux-android' for t in data['targets'])
    checks = []
    for name, record in data['records'].items():
        ctype = record['type']
        checks += [f'_Static_assert(sizeof({ctype}) == {record["size"]}, "{name} size");', f'_Static_assert(_Alignof({ctype}) == {record["alignment"]}, "{name} alignment");']
        def members(fields, prefix='', base=0):
            for field in fields:
                path = prefix + field['name']
                if 'bit_width' not in field:
                    yield f'_Static_assert(sizeof((({ctype}*)0)->{path}) == {field["size"]}, "{name}.{path} size");'
                    yield f'_Static_assert(offsetof({ctype}, {path}) * 8 == {base + field["offset_bits"]}, "{name}.{path} offset");'
                if 'members' in field:
                    yield from members(field['members'], path + '.', base + field['offset_bits'])
        checks.extend(members(record['fields']))
    with tempfile.TemporaryDirectory(suffix='.local.gcc') as tmp:
        root = Path(tmp)
        (root / 'primitives.h').write_text(PRELUDE)
        for name in ('stdint.h', 'stddef.h', 'string.h'):
            (root / name).write_text('#include "primitives.h"\n')
        config = root / 'os/c-api'
        config.mkdir(parents=True)
        (config / 'il2cpp-config-platforms.h').write_text(PLATFORM)
        (config / 'il2cpp-config-api-platforms.h').write_text('#pragma once\n')
        source = root / 'check.c'
        source.write_text('#include "primitives.h"\n#include "il2cpp-object-internals.h"\n' + '\n'.join(checks))
        subprocess.run(['gcc', '-std=gnu11', '-nostdinc', '-fsyntax-only', '-I' + tmp, '-I' + str(a.runtime_headers.resolve()), str(source)], check=True)
    print(f'GCC: {len(data["records"])} 个结构，{len(checks)} 个静态断言通过；不验证位域。')

if __name__ == '__main__':
    main()
