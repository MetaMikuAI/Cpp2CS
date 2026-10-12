"""通过生产 CLI 提升并解释 x64 MIR，再与 Unicorn 的合成指令执行比较。"""

import json
from pathlib import Path
import random
import subprocess
import sys

from unicorn import Uc, UC_ARCH_X86, UC_MODE_64, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
from unicorn import x86_const as xc


DLL = Path(__file__).resolve().parents[1] / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll"
CODE, DATA, STACK = 0x10000, 0x30000, 0x40000
GPRS = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"] + [f"r{i}" for i in range(8, 16)]
REGISTERS = {name: getattr(xc, "UC_X86_REG_" + name.upper()) for name in GPRS}
REGISTERS.update(fsbase=xc.UC_X86_REG_FS_BASE, gsbase=xc.UC_X86_REG_GS_BASE)
FLAGS = {"cf": 0, "pf": 2, "af": 4, "zf": 6, "sf": 7, "df": 10, "of": 11}
FLAG_MASK = sum(1 << bit for bit in FLAGS.values())
RNG = random.Random(0xC2208)


class Harness:
    def __init__(self, server):
        self.server = server
        self.machine = Uc(UC_ARCH_X86, UC_MODE_64)
        self.machine.mem_map(CODE, 0x10000)
        self.machine.mem_map(DATA, 0x1000)
        self.machine.mem_map(STACK, 0x1000)
        self.forms = {}
        self.checks = 0
        self.rejected = 0
        self.accesses = []
        self.machine.hook_add(UC_HOOK_MEM_READ, lambda _uc, _access, address, size, _value, _user: self.accesses.append(("Load", address, size)))
        self.machine.hook_add(UC_HOOK_MEM_WRITE, lambda _uc, _access, address, size, _value, _user: self.accesses.append(("Store", address, size)))

    def request(self, code, address, slots, memory):
        request = {"arch": "x64", "bytes": code.hex(), "address": hex(address),
                   "slots": {name: hex(value) for name, value in slots.items()},
                   "memory": [{"address": hex(start), "bytes": data.hex()} for start, data in memory],
                   "roundtrip": self.checks % 17 == 0}
        self.server.stdin.write(json.dumps(request) + "\n")
        self.server.stdin.flush()
        line = self.server.stdout.readline()
        assert line, ("production CLI exited", self.server.poll(), code.hex())
        return json.loads(line)

    def run(self, code_hex, *, width=64, family="plain", values=None, count=None, old_flags=None, memory=False, setup=None, zero_source=False):
        if code_hex not in self.forms:
            self.forms[code_hex] = CODE + len(self.forms) * 32
            code = bytes.fromhex(code_hex)
            self.machine.mem_write(self.forms[code_hex], code)
        address = self.forms[code_hex]
        code = bytes.fromhex(code_hex)
        slots = {name: RNG.getrandbits(64) for name in GPRS}
        slots.update(rsp=STACK + 64, fsbase=DATA, gsbase=DATA)
        if values is not None:
            mask = (1 << width) - 1
            slots["rax"] = (slots["rax"] & ~mask) | (values[0] & mask)
            slots["rbx"] = (slots["rbx"] & ~mask) | (values[1] & mask)
        if count is not None:
            slots["rcx"] = (slots["rcx"] & ~255) | count
        if old_flags is None:
            old_flags = RNG.getrandbits(12) & FLAG_MASK
        slots.update({flag: (old_flags >> bit) & 1 for flag, bit in FLAGS.items()})
        regions = []
        if memory:
            slots["rbx"] = DATA + 32
            regions = [(DATA, bytearray(RNG.randbytes(128))), (STACK, bytearray(RNG.randbytes(128)))]
        if setup is not None:
            setup(slots, regions, address)
        for name, register in REGISTERS.items():
            self.machine.reg_write(register, slots[name])
        self.machine.reg_write(xc.UC_X86_REG_EFLAGS, 2 | old_flags)
        for start, data in regions:
            self.machine.mem_write(start, bytes(data))
        self.accesses.clear()
        self.machine.emu_start(address, address + len(code), count=1)
        response = self.request(code, address, slots, regions)
        assert response["supported"], (code_hex, response)
        assert response["Outcome"] == "Normal", (code_hex, response)
        actual_slots = {name: int(value, 16) for name, value in response["slots"].items()}
        for name, register in REGISTERS.items():
            mask = (1 << 64) - 1
            if zero_source and name == "rax":
                mask ^= (1 << width) - 1
            expected = self.machine.reg_read(register)
            assert (actual_slots[name] & mask) == (expected & mask), (code_hex, name, hex(actual_slots[name]), hex(expected), slots)
        compare_flags = FLAG_MASK
        if family == "logical":
            compare_flags &= ~0x10
        elif family == "multiply":
            compare_flags &= 0x801 | 0x400
        elif family == "bittest":
            compare_flags &= 0x41 | 0x400
        elif family == "bitscan":
            compare_flags &= 0x40 | 0x400
        elif family in ("shl", "shr", "sar", "rol", "ror"):
            masked = (slots["rcx"] & 255) & (63 if width == 64 else 31)
            if masked:
                if masked != 1:
                    compare_flags &= ~0x800
                if family in ("shl", "shr", "sar"):
                    compare_flags &= ~0x10
                    if family != "sar" and masked >= width:
                        compare_flags &= ~1
        actual_flags = sum(actual_slots[flag] << bit for flag, bit in FLAGS.items())
        expected_flags = self.machine.reg_read(xc.UC_X86_REG_EFLAGS)
        assert actual_flags & compare_flags == expected_flags & compare_flags, (code_hex, "flags", hex(actual_flags), hex(expected_flags), hex(compare_flags), slots)
        assert int(response["next"], 16) == self.machine.reg_read(xc.UC_X86_REG_RIP), (code_hex, "next", response["next"])
        for start, data in regions:
            expected = bytes(self.machine.mem_read(start, len(data)))
            actual = bytes(response["memory"][hex(start + i).upper().replace("0X", "0x")] for i in range(len(data)))
            assert actual == expected, (code_hex, "memory", hex(start))
        expected_accesses = [f"{kind}:0x{where:X}:{size}" for kind, where, size in self.accesses]
        assert response["Accesses"] == expected_accesses, (code_hex, "access order", response["Accesses"], expected_accesses)
        if memory:
            assert response["support"] == "NormalPathOnly", (code_hex, response["support"])
        self.checks += 1

    def reject(self, code_hex):
        response = self.request(bytes.fromhex(code_hex), CODE, {}, [])
        assert not response["supported"], ("unsupported form accepted", code_hex, response)
        self.rejected += 1


def arithmetic(h):
    forms = {"add": ("00d8", "01d8"), "adc": ("10d8", "11d8"), "sub": ("28d8", "29d8"),
             "sbb": ("18d8", "19d8"), "cmp": ("38d8", "39d8"), "and": ("20d8", "21d8"),
             "or": ("08d8", "09d8"), "xor": ("30d8", "31d8"), "test": ("84d8", "85d8")}
    unary = [("fec0", "ffc0"), ("fec8", "ffc8"), ("f6d8", "f7d8"), ("f6d0", "f7d0")]
    for width in (8, 16, 32, 64):
        prefix = "66" if width == 16 else "48" if width == 64 else ""
        mask = (1 << width) - 1
        edge = [0, 1, 15, 16, (1 << (width - 1)) - 1, 1 << (width - 1), mask]
        pairs = [(a, b) for a in edge for b in edge] + [(RNG.getrandbits(width), RNG.getrandbits(width)) for _ in range(12)]
        for name, codes in forms.items():
            code = prefix + codes[width != 8]
            for index, pair in enumerate(pairs):
                h.run(code, width=width, family="logical" if name in ("and", "or", "xor", "test") else "plain", values=pair,
                      old_flags=0 if index % 2 else FLAG_MASK)
        for codes in unary:
            for a in edge:
                for old in (0, FLAG_MASK):
                    h.run(prefix + codes[width != 8], width=width, values=(a, 0), old_flags=old)
    for code in ("4883c0ff", "4883d0ff", "4883e8ff", "4883d8ff", "4883f8ff", "83c0ff", "80c4ff"):
        for _ in range(12):
            h.run(code)


def shifts(h):
    for width in (8, 16, 32, 64):
        prefix = "66" if width == 16 else "48" if width == 64 else ""
        for name, modrm in (("shl", "e0"), ("shr", "e8"), ("sar", "f8"), ("rol", "c0"), ("ror", "c8")):
            code = prefix + ("d2" if width == 8 else "d3") + modrm
            for count in (0, 1, 2, 7, 8, 9, 16, 17, 31, 32, 33, 63, 64, 65, 255):
                for a in (0, 1, 3, 1 << (width - 1), (1 << width) - 1):
                    h.run(code, width=width, family=name, values=(a, 0), count=count)


def conditions(h):
    arithmetic_bits = [0, 2, 4, 6, 7, 11]
    for condition in range(16):
        for combination in range(64):
            old = sum(((combination >> i) & 1) << bit for i, bit in enumerate(arithmetic_bits))
            for prefix in ("", "66", "48"):
                h.run(prefix + f"0f{0x40 + condition:02x}c3", old_flags=old)
            h.run(f"{0x70 + condition:02x}05", old_flags=old)
            h.run(f"0f{0x90 + condition:02x}c0", old_flags=old)


def other_registers(h):
    codes = ["88e0", "88c4", "88dc", "6689d8", "89d8", "4889d8", "4188c0", "4189c0", "4989c0",
             "0fb6c4", "480fb6c3", "0fb7c3", "0fbec3", "480fbfc3", "4863c3", "660fb6c3",
             "b8ffffffff", "48c7c0ffffffff", "b4ab", "86e0", "4887d8", "87d8", "87c0", "0fc8", "480fc8",
             "98", "6698", "4898", "99", "6699", "4899", "f8", "f9", "f5", "fc", "fd", "90"]
    for code in codes:
        for _ in range(16):
            h.run(code)
    for width in (8, 16, 32, 64):
        prefix = "66" if width == 16 else "48" if width == 64 else ""
        codes = [prefix + ("f6" if width == 8 else "f7") + suffix for suffix in ("e3", "eb")]
        if width != 8:
            codes += [prefix + "0fafc3", prefix + "6bc3fd"]
        for code in codes:
            for _ in range(24):
                h.run(code, width=width, family="multiply")
        if width == 8:
            continue
        for suffix in ("a3d8", "abd8", "b3d8", "bbd8", "bae003"):
            for _ in range(12):
                h.run(prefix + "0f" + suffix, width=width, family="bittest")
        for suffix in ("bcc3", "bdc3"):
            if width == 32:
                continue
            for value in [0, 1, 2, 8, 1 << (width - 1), (1 << width) - 1] + [RNG.getrandbits(width) for _ in range(12)]:
                h.run(prefix + "0f" + suffix, width=width, family="bitscan", values=(0xABABABABABABABAB, value), zero_source=value == 0)


def memory_and_control(h):
    codes = ["488b03", "8b03", "668b03", "8a03", "488903", "8903", "668903", "8803",
             "480103", "480303", "483b03", "488503", "48ff03", "48c703ffffffff", "0f4403", "480f4403", "0f9403",
             "8d448b20", "488d448b20", "64488b03", "65488b03", "67488b03"]
    for code in codes:
        for old in (0, FLAG_MASK):
            def setup(slots, _regions, _address):
                slots["rcx"] = 3
                if code.startswith(("64", "65")):
                    slots["rbx"] = 32
                if code.startswith("67"):
                    slots["rbx"] |= 0xBEEFABCD00000000
            family = "logical" if code == "488503" else "plain"
            # LEA 只计算地址，不执行内存访问。
            if code in ("8d448b20", "488d448b20"):
                h.run(code, old_flags=old, setup=lambda s, r, a: s.update(rbx=DATA + 32, rcx=3))
            else:
                h.run(code, old_flags=old, memory=True, setup=setup, family=family)
    for code in ("50", "6650", "6aff", "ff33", "5b", "5c", "665c", "e800000000", "ffd0", "ff13", "c3", "c21000", "ffe0", "e905000000"):
        def setup(slots, regions, address):
            target = address + 16
            if code in ("ffd0", "ffe0"):
                slots["rax"] = target
            if code == "ff13":
                regions[0][1][32:40] = target.to_bytes(8, "little")
            if code in ("c3", "c21000"):
                regions[1][1][64:72] = target.to_bytes(8, "little")
        if code in ("ffe0", "e905000000"):
            # 间接 JMP 的地址检查未建模，但没有内存效应。
            h.run(code, setup=setup)
        else:
            h.run(code, memory=True, setup=setup)
    for code in ("e305", "67e305"):
        for value in (0, 1, 0x100000000, 0x100000001):
            h.run(code, setup=lambda s, r, a: s.update(rcx=value))
    for width in (8, 16, 32, 64):
        prefix = "66" if width == 16 else "48" if width == 64 else ""
        for family, suffix in (("shl", "23"), ("shr", "2b"), ("sar", "3b"), ("rol", "03"), ("ror", "0b")):
            code = prefix + ("d2" if width == 8 else "d3") + suffix
            for count in (0, 1, 2, 8, 16, 32, 64, 255):
                h.run(code, width=width, family=family, count=count, memory=True)
    for code in ("488b042520000300", "67488b042520000300"):
        h.run(code, memory=True)
    address = CODE + len(h.forms) * 32
    code = "488b05" + (DATA + 32 - address - 7).to_bytes(4, "little", signed=True).hex()
    h.run(code, memory=True)


def main():
    command = ["dotnet", str(Path(sys.argv[1]) if len(sys.argv) > 1 else DLL), "serve"]
    with subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, encoding="utf-8", bufsize=1) as server:
        h = Harness(server)
        arithmetic(h)
        shifts(h)
        conditions(h)
        other_registers(h)
        memory_and_control(h)
        for code in ("f0480103", "f3a4", "d3d0", "d3d8", "48f7f3", "0f58c0", "e005", "e105", "e205", "9d", "0fae2b", "0fbcc3", "0fbdc3"):
            h.reject(code)
        server.stdin.close()
        server.wait()
        assert server.returncode == 0, server.returncode
        print(json.dumps({"x64_differential": h.checks, "forms": len(h.forms), "unsupported_rejected": h.rejected,
                          "scope": "production MIR + JSON roundtrip vs Unicorn; synthetic normal paths, not hardware/game/fault proof"}, indent=2))


if __name__ == "__main__":
    main()
