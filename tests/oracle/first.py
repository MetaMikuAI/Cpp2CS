"""执行原始 ARM64 方法；仅映射代码页、参数内存和栈，不代写目标方法公式。"""
import hashlib
import itertools
import json
from pathlib import Path
import random
import struct
import sys
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_X3, UC_ARM64_REG_X4, UC_ARM64_REG_X5, UC_ARM64_REG_X30, UC_ARM64_REG_SP, UC_ARM64_REG_PC

data = Path(sys.argv[1]).read_bytes()
catalog = json.loads(Path(sys.argv[2]).read_text(encoding='utf-8'))
digest = hashlib.sha256(data).hexdigest().upper()
assert digest == catalog['binarySha256']
phoff, = struct.unpack_from('<Q', data, 0x20)
phentsize, phnum = struct.unpack_from('<HH', data, 0x36)
segments = [struct.unpack_from('<IIQQQQQQ', data, phoff + i * phentsize) for i in range(phnum)]
methods = {m['name']: int(m['address'], 16) for t in catalog['types'] for m in t['methods'] if t['name'].endswith('StaminaData')}
request = next(t for t in catalog['types'] if t['name'].endswith('MusicScoreSearchConditionRequest'))
constructor = int(request['methods'][0]['address'], 16)
object_ctor = int(catalog['objectConstructorAddress'], 16)
pages = {a & ~0xfff for a in [*methods.values(), constructor, object_ctor]}
machine = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
for page in sorted(pages):
    segment, = [s for s in segments if s[0] == 1 and s[3] <= page and page + 4096 <= s[3] + s[5]]
    offset = segment[2] + page - segment[3]
    machine.mem_map(page, 4096)
    machine.mem_write(page, data[offset:offset+4096])
machine.mem_map(0x100000, 0x10000)
registers = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_X3, UC_ARM64_REG_X4, UC_ARM64_REG_X5]
stop = 0x10f000
memory = 0x101000
signed = lambda v: (v + 0x80000000) % 0x100000000 - 0x80000000

def run(address, args):
    machine.reg_write(UC_ARM64_REG_SP, 0x10e000)
    machine.reg_write(UC_ARM64_REG_X30, stop)
    for register, value in zip(registers, args + [0] * (len(registers)-len(args))):
        machine.reg_write(register, value & 0xffffffffffffffff)
    machine.emu_start(address, stop, count=200)
    assert machine.reg_read(UC_ARM64_REG_PC) == stop
    return [machine.reg_read(r) for r in registers[:2]]

def packed(values):
    return [(values[0] & 0xffffffff) | ((values[1] & 0xffffffff) << 32), values[2] & 0xffffffff]

def returned(registers):
    return [signed(registers[0] & 0xffffffff), signed(registers[0] >> 32), signed(registers[1] & 0xffffffff)]

limits = [-2147483648, -2147483647, -1, 0, 1, 2147483646, 2147483647]
randomizer = random.Random(10)
values = list(itertools.product(limits, repeat=3))
values += [tuple(randomizer.randrange(-2147483648,2147483648) for _ in range(3)) for _ in range(1000)]
rows = []
for a in values:
    b = tuple(randomizer.randrange(-2147483648,2147483648) for _ in range(3))
    original = struct.pack('<3i', *a)
    machine.mem_write(memory, original)
    has = run(methods['get_IsHasBoostStaminaOrEnhanceStamina'], [memory])[0] & 1
    empty = run(methods['get_IsEmptyStamina'], [memory])[0] & 1
    total = signed(run(methods['get_SumStamina'], [memory])[0] & 0xffffffff)
    assert bytes(machine.mem_read(memory, 12)) == original
    machine.mem_write(memory, bytes([0xa5]) * 20)
    run(methods['.ctor'], [memory+4, *a])
    after = bytes(machine.mem_read(memory, 20))
    assert after[:4] == bytes([0xa5])*4 and after[16:] == bytes([0xa5])*4
    rows.append({'a': a, 'b': b, 'has': bool(has), 'empty': bool(empty), 'sum': total,
                 'constructed': list(struct.unpack('<3i', after[4:16])),
                 'add': returned(run(methods['op_Addition'], packed(a)+packed(b))),
                 'sub': returned(run(methods['op_Subtraction'], packed(a)+packed(b)))})
zero = returned(run(methods['get_Zero'], []))
requests = []
inputs = [(-1,-1,0,0), (0,0,1,1)] + [tuple(randomizer.randrange(-2147483648,2147483648) for _ in range(4)) for _ in range(1000)]
for values in inputs:
    machine.mem_write(memory, bytes([0xa5]) * 40)
    run(constructor, [memory, *values])
    after = bytes(machine.mem_read(memory, 40))
    assert after[:16] == bytes([0xa5])*16 and after[32:] == bytes([0xa5])*8
    requests.append({'input': values, 'fields': list(struct.unpack('<4i', after[16:32]))})
result = {'binarySha256': digest, 'objectConstructor': hex(object_ctor), 'zero': zero,
          'stamina': rows, 'requests': requests, 'nativeCalls': len(rows)*6+1+len(requests)}
Path(sys.argv[3]).write_text(json.dumps(result), encoding='utf-8')
print(f"native: {len(rows)} stamina, {len(requests)} requests, {result['nativeCalls']} calls; original Object constructor executed")
