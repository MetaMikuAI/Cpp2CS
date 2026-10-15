"""执行 GetSquareMin 的原生计算段，记录调用 GridPosition 构造前的完整参数。"""
import hashlib
import json
from pathlib import Path
import random
import struct
import sys
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_X3, UC_ARM64_REG_SP, UC_ARM64_REG_PC

data = Path(sys.argv[1]).read_bytes()
digest = hashlib.sha256(data).hexdigest().upper()
assert digest == '6CE1DE5C0357E122F153F62D648DE1655B7F8A339B2AE1C575595868A361E4BB'
start, stop = 0x58688ac, 0x5868900
phoff, = struct.unpack_from('<Q', data, 0x20)
phentsize, phnum = struct.unpack_from('<HH', data, 0x36)
segments = [struct.unpack_from('<IIQQQQQQ', data, phoff + i * phentsize) for i in range(phnum)]
segment, = [s for s in segments if s[0] == 1 and s[3] <= start < stop <= s[3] + s[5]]
code = data[segment[2] + start - segment[3]:segment[2] + stop - segment[3]]
machine = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
machine.mem_map(start & ~0xfff, 0x1000)
machine.mem_write(start, code)
machine.mem_map(0x100000, 0x1000)
limits = [-2147483648, -2147483647, -257, -256, -129, -128, -3, -2, -1, 0, 1, 2, 3, 127, 128, 255, 256, 2147483646, 2147483647]
inputs = [(x, 123456789, z) for x in limits for z in limits]
randomizer = random.Random(58688)
inputs += [tuple(randomizer.randrange(-2147483648, 2147483648) for _ in range(3)) for _ in range(1000)]
rows = []
signed = lambda value: (value + 0x80000000) % 0x100000000 - 0x80000000
for x, y, z in inputs:
    machine.reg_write(UC_ARM64_REG_SP, 0x100800)
    machine.reg_write(UC_ARM64_REG_X0, 0)
    machine.reg_write(UC_ARM64_REG_X1, (x & 0xffffffff) | ((y & 0xffffffff) << 32))
    machine.reg_write(UC_ARM64_REG_X2, z & 0xffffffff)
    machine.emu_start(start, stop, count=100)
    assert machine.reg_read(UC_ARM64_REG_PC) == stop
    rows.append({'input': [x, y, z], 'arguments': [signed(machine.reg_read(r) & 0xffffffff) for r in (UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_X3)]})
Path(sys.argv[2]).write_text(json.dumps({'binarySha256': digest, 'start': start, 'stop': stop, 'cases': rows}), encoding='utf-8')
print(f'Unicorn: {len(rows)} cases, stopped before constructor call at {stop:#x}')
