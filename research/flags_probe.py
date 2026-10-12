"""Flags 设计核验：数学穷举与合成指令的 Unicorn 对照，不执行游戏代码。"""

import itertools
import json
import random

import capstone
import unicorn
from capstone import Cs, CS_ARCH_ARM64, CS_ARCH_X86, CS_MODE_64
from unicorn import Uc, UC_ARCH_ARM64, UC_ARCH_X86, UC_MODE_ARM, UC_MODE_64, UC_HOOK_MEM_READ
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_NZCV
from unicorn.x86_const import UC_X86_REG_RAX, UC_X86_REG_RBX, UC_X86_REG_RCX, UC_X86_REG_EFLAGS


def signed(value, width):
    return value - (1 << width) if value >> (width - 1) else value


def addc(a, b, carry, width):
    mask = (1 << width) - 1
    total = a + b + carry
    result = total & mask
    overflow = ((~(a ^ b) & (a ^ result)) >> (width - 1)) & 1
    return result, total >> width, overflow


def reference(a, b, carry, width, subtract):
    delta = 1 - carry if subtract else carry
    exact = a - b - delta if subtract else a + b + delta
    signed_exact = signed(a, width) - signed(b, width) - delta if subtract else signed(a, width) + signed(b, width) + delta
    mask = (1 << width) - 1
    result = exact & mask
    c = int(exact >= 0) if subtract else int(exact > mask)
    v = int(not -(1 << (width - 1)) <= signed_exact < (1 << (width - 1)))
    return result, c, v


def nzcv(result, carry, overflow, width):
    return ((result >> (width - 1)) << 31) | (int(result == 0) << 30) | (carry << 29) | (overflow << 28)


def xflags(a, b, result, carry, overflow, width, subtract, carry_in):
    af = int((a & 15) < (b & 15) + carry_in) if subtract else int((a & 15) + (b & 15) + carry_in > 15)
    pf = int((result & 255).bit_count() % 2 == 0)
    return (carry ^ int(subtract)) | (pf << 2) | (af << 4) | (int(result == 0) << 6) | ((result >> (width - 1)) << 7) | (overflow << 11)


def pairs(width):
    edge = [0, 1, 15, 16, (1 << (width - 1)) - 1, 1 << (width - 1), (1 << width) - 1]
    rng = random.Random(808 + width)
    return list(itertools.product(edge, repeat=2)) + [(rng.getrandbits(width), rng.getrandbits(width)) for _ in range(64)]


def check_math():
    count = 0
    for a, b, carry, subtract in itertools.product(range(256), range(256), range(2), (False, True)):
        actual = addc(a, b ^ (255 if subtract else 0), carry, 8)
        assert actual == reference(a, b, carry, 8, subtract), (a, b, carry, subtract, actual)
        count += 1
    return count


def check_arm():
    decoder = Cs(CS_ARCH_ARM64, 0)
    machine = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    machine.mem_map(0x10000, 0x1000)
    encodings = {"adds": 0xAB020020, "subs": 0xEB020020, "adcs": 0xBA020020, "sbcs": 0xFA020020, "ands": 0xEA020020, "adc": 0x9A020020}
    count = 0
    for index, (width, name) in enumerate(itertools.product((32, 64), encodings)):
        code = (encodings[name] & (0x7FFFFFFF if width == 32 else 0xFFFFFFFF)).to_bytes(4, "little")
        address = 0x10000 + index * 16
        assert next(decoder.disasm(code, address)).mnemonic == name
        machine.mem_write(address, code)
        for a, b in pairs(width):
            for old in (0, 0xF0000000):
                carry = (old >> 29) & 1
                machine.reg_write(UC_ARM64_REG_X0, 0xDEADBEEFDEADBEEF)
                machine.reg_write(UC_ARM64_REG_X1, a)
                machine.reg_write(UC_ARM64_REG_X2, b)
                machine.reg_write(UC_ARM64_REG_NZCV, old)
                machine.emu_start(address, address + 4, count=1)
                if name == "ands":
                    result, c, v = a & b, 0, 0
                else:
                    subtract = name in ("subs", "sbcs")
                    incoming = carry if name in ("adcs", "sbcs", "adc") else int(subtract)
                    result, c, v = addc(a, b ^ (((1 << width) - 1) if subtract else 0), incoming, width)
                expected = old if name == "adc" else nzcv(result, c, v, width)
                observed = machine.reg_read(UC_ARM64_REG_NZCV) & 0xF0000000
                assert machine.reg_read(UC_ARM64_REG_X0) == result, (name, width, a, b, "result")
                assert observed == expected, (name, width, a, b, old, hex(observed), hex(expected))
                count += 1
    address = 0x10200
    code = bytes.fromhex("2a0042fa")  # ccmp x1, x2, #10, eq
    decoded = next(decoder.disasm(code, address))
    assert decoded.mnemonic == "ccmp" and decoded.op_str == "x1, x2, #0xa, eq", decoded.op_str
    machine.mem_write(address, code)
    for old in range(16):
        machine.reg_write(UC_ARM64_REG_X1, 3)
        machine.reg_write(UC_ARM64_REG_X2, 5)
        machine.reg_write(UC_ARM64_REG_NZCV, old << 28)
        machine.emu_start(address, address + 4, count=1)
        expected = nzcv(*addc(3, 5 ^ ((1 << 64) - 1), 1, 64), 64) if old & 4 else 10 << 28
        assert machine.reg_read(UC_ARM64_REG_NZCV) & 0xF0000000 == expected, ("ccmp", old)
        count += 1
    return count


def check_x64():
    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    machine = Uc(UC_ARCH_X86, UC_MODE_64)
    machine.mem_map(0x10000, 0x2000)
    opcodes = {"add": "01d8", "adc": "11d8", "sub": "29d8", "sbb": "19d8"}
    flag_mask = 0x8D5
    count = 0
    for index, (width, name) in enumerate(itertools.product((32, 64), opcodes)):
        code = bytes.fromhex(("48" if width == 64 else "") + opcodes[name])
        address = 0x10000 + index * 16
        assert next(decoder.disasm(code, address)).mnemonic == name
        machine.mem_write(address, code)
        for a, b in pairs(width):
            for cf in (0, 1):
                machine.reg_write(UC_X86_REG_RAX, a | (0xFACE000000000000 if width == 32 else 0))
                machine.reg_write(UC_X86_REG_RBX, b)
                machine.reg_write(UC_X86_REG_EFLAGS, 2 | cf)
                machine.emu_start(address, address + len(code), count=1)
                subtract = name in ("sub", "sbb")
                incoming = cf if name in ("adc", "sbb") else 0
                result, c, v = addc(a, b ^ (((1 << width) - 1) if subtract else 0), 1 - incoming if subtract else incoming, width)
                expected = xflags(a, b, result, c, v, width, subtract, incoming)
                observed = machine.reg_read(UC_X86_REG_EFLAGS) & flag_mask
                assert machine.reg_read(UC_X86_REG_RAX) == result, (name, width, a, b, "result")
                assert observed == expected, (name, width, a, b, cf, hex(observed), hex(expected))
                count += 1
    for index, (width, name) in enumerate(itertools.product((8, 32, 64), ("shl", "rol"))):
        code = bytes.fromhex(("48" if width == 64 else "") + ("d2" if width == 8 else "d3") + ("e0" if name == "shl" else "c0"))
        address = 0x10200 + index * 16
        assert next(decoder.disasm(code, address)).mnemonic == name
        machine.mem_write(address, code)
        mask = (1 << width) - 1
        for a, raw_count, old in itertools.product((0, 1, 3, 1 << (width - 1), mask), (0, 1, 2, 7, 8, 9, 16, 31, 32, 33, 63, 64, 65, 255), (0, flag_mask)):
            m = raw_count & (63 if width == 64 else 31)
            machine.reg_write(UC_X86_REG_RAX, a)
            machine.reg_write(UC_X86_REG_RCX, raw_count)
            machine.reg_write(UC_X86_REG_EFLAGS, old | 2)
            machine.emu_start(address, address + len(code), count=1)
            expected, defined, result = old, flag_mask, a
            if m and name == "shl":
                result = (a << m) & mask
                expected = (int(result == 0) << 6) | ((result >> (width - 1)) << 7) | (int((result & 255).bit_count() % 2 == 0) << 2)
                defined &= ~0x10  # AF 未定义
                if m < width:
                    expected |= (a >> (width - m)) & 1
                else:
                    defined &= ~1  # 不能固化模拟器返回的 CF
                if m == 1:
                    expected |= (((result >> (width - 1)) ^ (expected & 1)) << 11)
                else:
                    defined &= ~0x800
            elif m:
                k = m % width
                result = ((a << k) | (a >> (width - k))) & mask
                expected = (old & ~0x801) | (result & 1)
                if m == 1:
                    expected |= (((result >> (width - 1)) ^ (result & 1)) << 11)
                else:
                    defined &= ~0x800
            assert machine.reg_read(UC_X86_REG_RAX) & mask == result, (name, width, a, raw_count)
            observed = machine.reg_read(UC_X86_REG_EFLAGS)
            assert observed & defined == expected & defined, (name, width, a, raw_count, old, hex(observed), hex(expected), hex(defined))
            count += 1
    for width, hex_code in ((8, "fec0"), (32, "ffc0"), (64, "48ffc0")):
        address = 0x10300 + width * 4
        code = bytes.fromhex(hex_code)
        machine.mem_write(address, code)
        for a, old_cf in itertools.product((0, 1, 15, 16, (1 << (width - 1)) - 1, 1 << (width - 1), (1 << width) - 1), (0, 1)):
            machine.reg_write(UC_X86_REG_RAX, a)
            machine.reg_write(UC_X86_REG_EFLAGS, 2 | old_cf)
            machine.emu_start(address, address + len(code), count=1)
            result, c, v = addc(a, 1, 0, width)
            expected = (xflags(a, 1, result, c, v, width, False, 0) & ~1) | old_cf
            assert machine.reg_read(UC_X86_REG_RAX) == result, ("inc", width, a, old_cf, "result")
            assert machine.reg_read(UC_X86_REG_EFLAGS) & flag_mask == expected, ("inc", width, a, old_cf)
            count += 1
    address = 0x10100
    code = bytes.fromhex("0f4403")  # cmove eax, [rbx]
    assert next(decoder.disasm(code, address)).mnemonic == "cmove"
    machine.mem_write(address, code)
    machine.mem_write(0x11000, bytes.fromhex("78563412"))
    reads = []
    machine.hook_add(UC_HOOK_MEM_READ, lambda _uc, _access, addr, size, _value, _data: reads.append((addr, size)))
    machine.reg_write(UC_X86_REG_RAX, 0xDEADBEEF00000042)
    machine.reg_write(UC_X86_REG_RBX, 0x11000)
    machine.reg_write(UC_X86_REG_EFLAGS, 2)  # ZF=0，条件为假
    machine.emu_start(address, address + len(code), count=1)
    assert reads == [(0x11000, 4)], reads
    assert machine.reg_read(UC_X86_REG_RAX) == 0x42
    return count + 1


if __name__ == "__main__":
    print(json.dumps({"math_8bit": check_math(), "arm64_unicorn": check_arm(), "x64_unicorn": check_x64(), "capstone": capstone.__version__, "unicorn": unicorn.__version__, "scope": "synthetic instructions; not hardware or game validation"}, indent=2))
