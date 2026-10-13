"""按工具分类的 ABI 传参、取返回值，与 Clang ARM64 聚合函数的执行结果对照。"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import *


ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('configuration', type=Path)
parser.add_argument('--tool', type=Path, required=True)
args = parser.parse_args()
config = json.loads(args.configuration.read_text(encoding='utf-8-sig'))
out = ROOT / 'artifacts/aggregate-abi'
out.mkdir(parents=True, exist_ok=True)
types = ['Bytes' + str(n) for n in [1, 2, 3, 4, 7, 8, 9, 12, 16, 24, 32]]
header = 'typedef unsigned char uint8_t; typedef unsigned int uint32_t; typedef unsigned long long uint64_t;\n'
header += '\n'.join('struct Bytes%d { union { uint8_t bytes[%d]; uint8_t first; }; };' % (n, n)
                    for n in [1, 2, 3, 4, 7, 8, 9, 12, 16, 24, 32])
header += '''
union IntegerUnion { uint64_t words[2]; uint8_t bytes[16]; };
struct IntegerPair { uint32_t a; uint32_t b; };
struct IntegerArray { IntegerPair pairs[3]; };
struct PointerOverlay { union { void* pointer; uint64_t bits; }; };
struct FloatPair { float x; float y; };
union FloatUnion { float value; float values[2]; };
union MixedUnion { float floating; uint32_t integer; };
#pragma pack(push, 1)
struct PackedOverlay { uint8_t prefix; union { uint64_t wide; uint8_t bytes[8]; }; };
#pragma pack(pop)
'''
types += ['IntegerUnion', 'IntegerArray', 'PointerOverlay', 'FloatPair']
cases = [dict(Type=t, Prefix=p, Reject=False) for t in types for p in [0, 6, 7, 8]]
cases += [dict(Type=t, Prefix=0, Reject=True) for t in ['FloatUnion', 'MixedUnion', 'PackedOverlay']]
(out / 'types.h').write_text(header, encoding='utf-8')
(out / 'cases.json').write_text(json.dumps(cases), encoding='utf-8')
source = '#include "types.h"\n'
for case in cases:
    if case['Reject']:
        continue
    name, prefix = case['Type'], case['Prefix']
    params = [f'uint64_t lead{i}' for i in range(prefix)] + [f'{name} value', 'uint64_t tail']
    seed = ' ^ '.join(['tail'] + [f'lead{i}' for i in range(prefix)])
    source += f'''extern "C" uint64_t check_{name}_{prefix}({', '.join(params)}) {{
    uint64_t result = {seed};
    const uint8_t* bytes = reinterpret_cast<const uint8_t*>(&value);
    for (unsigned int i = 0; i < sizeof(value); ++i) result = result * 257 + bytes[i];
    return result;
}}
'''
for name in types:
    source += f'''extern "C" {name} return_{name}(const uint8_t* input) {{
    {name} result;
    __builtin_memcpy(&result, input, sizeof(result));
    return result;
}}
'''
(out / 'cases.cpp').write_text(source, encoding='utf-8')
subprocess.run([config['Clang'], '-target', 'aarch64-linux-gnu', '-O2', '-ffreestanding', '-fno-exceptions', '-fno-rtti',
                '-fno-stack-protector', '-fno-vectorize', '-fno-slp-vectorize', '-c', str(out / 'cases.cpp'), '-o', str(out / 'cases.o')], check=True)
with (out / 'cases.o').open('rb') as stream:
    elf = ELFFile(stream)
    code = elf.get_section_by_name('.text').data()
    symbols = {s.name: s['st_value'] for s in elf.get_section_by_name('.symtab').iter_symbols() if s['st_info']['type'] == 'STT_FUNC'}
    assert elf.get_section_by_name('.rela.text') is None, '夹具不能依赖未加载的外部数据或调用'
(out / 'cases.bin').write_bytes(code)
subprocess.run(['dotnet', str(args.tool.resolve()), 'aggregate-abi', str(args.configuration.resolve()), str(out)], check=True)
layouts = json.loads((out / 'layouts.json').read_text(encoding='utf-8'))
BASE, DATA, STACK, STOP = 0x100000, 0x200000, 0x300000, 0x400000
MASK = (1 << 64) - 1
rng = random.Random(44017)
checks = 0


def register(name):
    index = int(name[1:])
    return UC_ARM64_REG_Q0 + index if name[0] == 'V' else UC_ARM64_REG_X0 + index


def run(name, layout, arguments):
    uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    uc.mem_map(BASE, (len(code) + 4095) & ~4095)
    uc.mem_write(BASE, code)
    for address in [DATA, STACK, STOP]:
        uc.mem_map(address, 0x10000)
    uc.reg_write(UC_ARM64_REG_SP, STACK + 0x8000)
    uc.reg_write(UC_ARM64_REG_X30, STOP)
    for i in range(29):
        uc.reg_write(UC_ARM64_REG_X0 + i, rng.getrandbits(64))
    for i in range(32):
        uc.reg_write(UC_ARM64_REG_Q0 + i, rng.getrandbits(128))
    uc.mem_write(DATA, arguments[0] if name.startswith('return_') else bytes(256))
    for index, (argument, value) in enumerate(zip(layout['Arguments'], arguments)):
        if name.startswith('return_'):
            value = DATA.to_bytes(8, 'little')
        if argument['Indirect']:
            pointer = DATA + 0x1000 + index * 0x100
            uc.mem_write(pointer, value)
            value = pointer.to_bytes(8, 'little')
        for piece in argument['Pieces']:
            part = value[piece['ValueOffset']:piece['ValueOffset'] + piece['Size']]
            assert len(part) == piece['Size']
            if piece['Register'] is not None:
                target = register(piece['Register'])
                mask = (1 << (piece['Size'] * 8)) - 1
                uc.reg_write(target, (uc.reg_read(target) & ~mask) | int.from_bytes(part, 'little'))
            else:
                uc.mem_write(STACK + 0x8000 + piece['StackOffset'], part)
    result = layout['Return']
    if result['Indirect']:
        assert result['Pieces'][0]['Register'] == 'X8'
        uc.reg_write(UC_ARM64_REG_X8, DATA + 0x8000)
    uc.emu_start(BASE + symbols[name], STOP, count=10000)
    assert uc.reg_read(UC_ARM64_REG_PC) == STOP, name
    if result['Indirect']:
        return bytes(uc.mem_read(DATA + 0x8000, result['Shape']['Size']))
    recovered = bytearray(result['Shape']['Size'])
    for piece in result['Pieces']:
        number = uc.reg_read(register(piece['Register'])) & ((1 << (piece['Size'] * 8)) - 1)
        recovered[piece['ValueOffset']:piece['ValueOffset'] + piece['Size']] = number.to_bytes(piece['Size'], 'little')
    return bytes(recovered)


for case in layouts:
    if case['Reject']:
        assert case['Checksum'] is None and case['Returned'] is None
        continue
    size, name, prefix = case['Shape']['Size'], case['Type'], case['Prefix']
    for trial in range(32):
        value = bytes([0 if trial == 0 else 255]) * size if trial < 2 else rng.randbytes(size)
        prefix_values = [rng.getrandbits(64) for _ in range(prefix)]
        tail = rng.getrandbits(64)
        expected = tail
        for number in prefix_values:
            expected ^= number
        for byte in value:
            expected = (expected * 257 + byte) & MASK
        arguments = [v.to_bytes(8, 'little') for v in prefix_values] + [value, tail.to_bytes(8, 'little')]
        actual = int.from_bytes(run(f'check_{name}_{prefix}', case['Checksum'], arguments), 'little')
        assert actual == expected, (name, prefix, trial, expected, actual)
        checks += 1
        if prefix == 0:
            assert run(f'return_{name}', case['Returned'], [value]) == value, (name, trial)
            checks += 1
report = dict(signatures=len(layouts), rejected=sum(c['Reject'] for c in layouts), scenarios=checks,
              arm64Sha256=hashlib.sha256(code).hexdigest(), coreSha256=hashlib.sha256((args.tool.parent / 'Cpp2CS.Core.dll').read_bytes()).hexdigest(),
              scope='Clang ARM64 execution with registers, stack and indirect return buffers; no game or generated C# execution')
(out / 'report.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
print(json.dumps(report))
