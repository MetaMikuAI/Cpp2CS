#!/usr/bin/env python3
"""用最小声明检查打包、匿名联合、位域及 LP64/LLP64 的提取。"""
from pathlib import Path
import tempfile
from generate import generate


def main():
    with tempfile.TemporaryDirectory(suffix='.local.layout-test') as tmp:
        source = Path(tmp) / 'fixture.h'
        source.write_text('''
#pragma pack(push, 1)
struct Packed { char c; void *p; };
#pragma pack(pop)
struct Bits { unsigned a:3; unsigned b:5; union { int x; short y; }; union { int z; char c; } named; };
struct Model { long value; void *pointer; };
enum Values { ZERO, SHIFT = 1 << 5, NEG = -1 };
''')
        for target in ('android-arm64', 'android-x64', 'windows-x64'):
            data = generate(source, 'fixture', target)
            records = data['records']
            assert records['Packed']['size'] == 9
            assert records['Packed']['alignment'] == 1
            assert records['Packed']['fields'][1]['offset_bits'] == 8
            fields = {f['name']: f for f in records['Bits']['fields']}
            assert fields['a']['offset_bits'] == 0 and fields['a']['bit_width'] == 3
            assert fields['b']['offset_bits'] == 3 and fields['b']['bit_width'] == 5
            assert fields['x']['offset_bits'] == fields['y']['offset_bits'] == 32
            assert fields['named']['members'][0]['name'] == 'z'
            assert records['Model']['fields'][0]['size'] == (4 if target == 'windows-x64' else 8)
            assert data['constants'] == {'ZERO': 0, 'SHIFT': 32, 'NEG': -1}
    print('三个目标的最小布局用例通过。')

if __name__ == '__main__':
    main()
