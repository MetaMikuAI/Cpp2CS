import json
import random
from pathlib import Path
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import UC_ARM64_REG_W20, UC_ARM64_REG_W24, UC_ARM64_REG_W8

# 从真实方法提取纯数值指令；不执行游戏、分配器或元数据函数。
with open(json.loads(Path('native.local.json').read_text(encoding='utf-8'))['Binary'], 'rb') as stream:
    elf = ELFFile(stream)
    segment = next(s for s in elf.iter_segments() if s['p_type'] == 'PT_LOAD' and s['p_vaddr'] <= 0x570e810 < s['p_vaddr'] + s['p_filesz'])
    code = bytearray()
    for address, size in [(0x570e810, 8), (0x570e838, 4), (0x570e850, 4), (0x570e858, 24)]:
        stream.seek(segment['p_offset'] + address - segment['p_vaddr'])
        code.extend(stream.read(size))
machine = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
machine.mem_map(0x1000, 0x1000)
machine.mem_write(0x1000, bytes(code))
edges = [-2147483648, -2147483647, -16777217, -7, -1, 0, 1, 3, 7, 16777217, 2147483646, 2147483647]
pairs = [(a, b) for a in edges for b in edges]
randomizer = random.Random(20261011)
pairs += [(randomizer.randint(-2147483648, 2147483647), randomizer.randint(-2147483648, 2147483647)) for _ in range(1000)]
rows = []
for amount, recovery in pairs:
    machine.reg_write(UC_ARM64_REG_W20, amount & 0xffffffff)
    machine.reg_write(UC_ARM64_REG_W24, recovery & 0xffffffff)
    machine.emu_start(0x1000, 0x1000 + len(code))
    result = machine.reg_read(UC_ARM64_REG_W8)
    if result >= 0x80000000:
        result -= 0x100000000
    rows.append(dict(amount=amount, recovery=recovery, expected=result))
Path('artifacts/numeric-oracle.json').write_text(json.dumps(rows), encoding='utf-8')
print(f'ARM64 Unicorn: {len(rows)} real-instruction numeric cases saved')
