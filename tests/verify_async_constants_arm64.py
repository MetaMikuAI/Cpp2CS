import json
from pathlib import Path
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import UC_ARM64_REG_X8, UC_ARM64_REG_S0, UC_ARM64_REG_S1

with open(json.loads(Path('native.local.json').read_text(encoding='utf-8'))['Binary'], 'rb') as stream:
    segments = list(ELFFile(stream).iter_segments())
    def read(address, size):
        segment = next(s for s in segments if s['p_type'] == 'PT_LOAD' and s['p_vaddr'] <= address < s['p_vaddr'] + s['p_filesz'])
        stream.seek(segment['p_offset'] + address - segment['p_vaddr'])
        return stream.read(size)
    code = read(0x5993e04, 8)
    constant = read(0x1f21338, 4)
machine = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
machine.mem_map(0x1000, 0x1000)
machine.mem_map(0x1f21000, 0x1000)
machine.mem_write(0x1000, code)
machine.mem_write(0x1f21338, constant)
machine.reg_write(UC_ARM64_REG_X8, 0x1f21000)
machine.emu_start(0x1000, 0x1008)
assert machine.reg_read(UC_ARM64_REG_S0) == 0x3f800000
assert machine.reg_read(UC_ARM64_REG_S1) == 0x3e4ccccd
print('PASS: real LDR S1 / FMOV S0 produce exact 0.2f / 1.0f bits used by generated C#')
