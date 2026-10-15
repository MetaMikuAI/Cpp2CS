"""无替身的 ARM64 小型执行环境；只映射指定原始代码页和测试内存。"""
import hashlib
from pathlib import Path
import struct
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn import arm64_const as arm


class Machine:
    def __init__(self, binary, expected_hash, addresses):
        data = Path(binary).read_bytes()
        self.digest = hashlib.sha256(data).hexdigest().upper()
        assert self.digest == expected_hash
        assert data[:6] == b'\x7fELF\x02\x01'
        assert struct.unpack_from('<H', data, 18)[0] == 183
        phoff, = struct.unpack_from('<Q', data, 0x20)
        phentsize, phnum = struct.unpack_from('<HH', data, 0x36)
        segments = [struct.unpack_from('<IIQQQQQQ', data, phoff+i*phentsize) for i in range(phnum)]
        self.cpu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
        for page in sorted({a & ~0xfff for a in addresses}):
            segment, = [s for s in segments if s[0] == 1 and s[3] <= page and page+4096 <= s[3]+s[5]]
            offset = segment[2] + page - segment[3]
            self.cpu.mem_map(page,4096)
            self.cpu.mem_write(page,data[offset:offset+4096])
        self.cpu.mem_map(0x100000,0x10000)
        self.memory, self.stop, self.calls = 0x101000, 0x10f000, 0
        self.registers = [getattr(arm,f'UC_ARM64_REG_X{i}') for i in range(9)]

    def run(self,address,args):
        assert len(args) <= len(self.registers)
        self.cpu.reg_write(arm.UC_ARM64_REG_SP,0x10e000)
        self.cpu.reg_write(arm.UC_ARM64_REG_X30,self.stop)
        for register,value in zip(self.registers,args+[0]*(len(self.registers)-len(args))):
            self.cpu.reg_write(register,value & 0xffffffffffffffff)
        self.cpu.emu_start(address,self.stop,count=200)
        assert self.cpu.reg_read(arm.UC_ARM64_REG_PC) == self.stop
        self.calls += 1
        return [self.cpu.reg_read(r) for r in self.registers[:2]]
