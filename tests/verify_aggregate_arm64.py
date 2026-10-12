import json
import random
import struct
from pathlib import Path
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import *

# 直接执行真实指令，独立核对元组字节拆分、结构体写入与有符号比较。
config = json.loads(Path('native.local.json').read_text(encoding='utf-8'))
with open(config['Binary'], 'rb') as stream:
    elf = ELFFile(stream)
    segments = list(elf.iter_segments())
    def code(address, size):
        segment = next(s for s in segments if s['p_type'] == 'PT_LOAD' and s['p_vaddr'] <= address < s['p_vaddr'] + s['p_filesz'])
        stream.seek(segment['p_offset'] + address - segment['p_vaddr'])
        return stream.read(size)
    snippets = [code(0x570ea00, 4) + code(0x570ea14, 4), code(0x570ea70, 8), code(0x570ebec, 8), code(0x58fa704, 8)]
machine = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
machine.mem_map(0x1000, 0x2000)
for index, snippet in enumerate(snippets):
    machine.mem_write(0x1000 + index * 0x100, snippet)
def run(index):
    start = 0x1000 + index * 0x100
    machine.emu_start(start, start + len(snippets[index]))
randomizer = random.Random(20261011)
edges = [-2147483648, -1, 0, 1, 2147483647]
pairs = [(a, b) for a in edges for b in edges] + [(randomizer.randint(-2**31, 2**31-1), randomizer.randint(-2**31, 2**31-1)) for _ in range(1000)]
for a, b in pairs:
    packed = int.from_bytes(struct.pack('<ii', a, b), 'little')
    machine.reg_write(UC_ARM64_REG_X0, packed)
    machine.reg_write(UC_ARM64_REG_X1, packed)
    run(0)
    assert machine.reg_read(UC_ARM64_REG_X26) == a & 0xffffffff
    assert machine.reg_read(UC_ARM64_REG_X25) == b & 0xffffffff
    machine.reg_write(UC_ARM64_REG_X20, packed)
    run(1)
    assert machine.reg_read(UC_ARM64_REG_X27) == a & 0xffffffff
    assert machine.reg_read(UC_ARM64_REG_X3) == b & 0xffffffff
    machine.reg_write(UC_ARM64_REG_W8, a & 0xffffffff)
    machine.reg_write(UC_ARM64_REG_W20, b & 0xffffffff)
    run(2)
    assert machine.reg_read(UC_ARM64_REG_W1) == int(a <= b)
    machine.reg_write(UC_ARM64_REG_X0, 0x2000)
    machine.reg_write(UC_ARM64_REG_W1, a & 0xffffffff)
    machine.reg_write(UC_ARM64_REG_W2, b & 0xffffffff)
    machine.reg_write(UC_ARM64_REG_W3, 0)
    run(3)
    assert bytes(machine.mem_read(0x2000, 12)) == struct.pack('<iii', a, b, 0)
print(f'PASS: {len(pairs)} inputs x 4 real ARM64 snippets; tuple slices, signed LE, complete constructor stores')
