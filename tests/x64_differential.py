"""通过生产 CLI 提升并解释 x64 MIR，再与 Unicorn 的合成指令执行比较。"""

import json
from pathlib import Path
import random
import subprocess
import sys

from unicorn import Uc, UC_ARCH_X86, UC_MODE_64, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
from unicorn import x86_const as xc


DLL = Path(__file__).resolve().parents[1] / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll"
CODE, DATA, STACK = 0x10000, 0x50000, 0x60000
GPRS = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"] + [f"r{i}" for i in range(8, 16)]
REGISTERS = {name: getattr(xc, "UC_X86_REG_" + name.upper()) for name in GPRS}
REGISTERS.update(fsbase=xc.UC_X86_REG_FS_BASE, gsbase=xc.UC_X86_REG_GS_BASE)
XMM_REGISTERS = {f"xmm{i}": getattr(xc, f"UC_X86_REG_XMM{i}") for i in range(16)}
FLAGS = {"cf": 0, "pf": 2, "af": 4, "zf": 6, "sf": 7, "df": 10, "of": 11}
FLAG_MASK = sum(1 << bit for bit in FLAGS.values())
RNG = random.Random(0xC2208)


class Harness:
    def __init__(self, server):
        self.server = server
        self.machine = Uc(UC_ARCH_X86, UC_MODE_64)
        self.machine.ctl_set_cpu_model(xc.UC_CPU_X86_HASWELL)
        self.machine.mem_map(CODE, DATA - CODE)
        self.machine.mem_map(DATA, 0x1000)
        self.machine.mem_map(STACK, 0x1000)
        self.forms = {}
        self.checks = 0
        self.rejected = 0
        self.fault_stops = 0
        self.native = None
        self.native_checks = 0
        self.native_only_checks = 0
        self.unicorn_fp_differences = {}
        self.unicorn_fp_examples = []
        self.unicorn_access_differences = {}
        self.unicorn_legacy_high_differences = {}
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

    def run(self, code_hex, *, width=64, family="plain", values=None, count=None, old_flags=None, memory=False, setup=None, zero_source=False, simd=False, native=False, emulate=True, memory_read_width=None):
        if code_hex not in self.forms:
            self.forms[code_hex] = CODE + len(self.forms) * 32
            code = bytes.fromhex(code_hex)
            self.machine.mem_write(self.forms[code_hex], code)
        address = self.forms[code_hex]
        code = bytes.fromhex(code_hex)
        slots = {name: RNG.getrandbits(64) for name in GPRS}
        slots.update(rsp=STACK + 64, fsbase=DATA, gsbase=DATA)
        if simd:
            slots.update({name: RNG.getrandbits(128) for name in XMM_REGISTERS})
            slots.update({f"ymm{i}_hi": 0xcafe0123456789abcdef001122334455 ^ i for i in range(16)})
            slots["mxcsr"] = RNG.getrandbits(16)
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
        if simd:
            for name, register in XMM_REGISTERS.items():
                index = int(name[3:])
                self.machine.reg_write(getattr(xc, f"UC_X86_REG_YMM{index}"), slots[name] | (slots[f"ymm{index}_hi"] << 128))
            self.machine.reg_write(xc.UC_X86_REG_MXCSR, slots["mxcsr"])
        self.machine.reg_write(xc.UC_X86_REG_EFLAGS, 2 | old_flags)
        for start, data in regions:
            self.machine.mem_write(start, bytes(data))
        self.accesses.clear()
        if emulate:
            self.machine.emu_start(address, address + len(code), count=1)
        else:
            assert native and not memory
            self.native_only_checks += 1
        hardware = {}
        if native:
            if self.native is None:
                from x64_float_native import NativeFloatOracle
                self.native = NativeFloatOracle()
            hardware = self.native.run(code_hex, xmm0=slots["xmm0"], xmm1=slots["xmm1"],
                                       rax=slots["rax"], rbx=slots["rbx"], mxcsr=slots["mxcsr"], eflags=2 | old_flags)
            self.native_checks += 1
            for name in (("xmm0", "xmm1", "rax", "rbx", "mxcsr") if emulate else ()):
                emulator = self.machine.reg_read(getattr(xc, "UC_X86_REG_" + name.upper()))
                if emulator != hardware[name]:
                    self.unicorn_fp_differences[name] = self.unicorn_fp_differences.get(name, 0) + 1
                    if len(self.unicorn_fp_examples) < 8:
                        self.unicorn_fp_examples.append({"code": code_hex, "slot": name, "unicorn": hex(emulator), "hardware": hex(hardware[name])})
        response = self.request(code, address, slots, regions)
        assert response["supported"], (code_hex, response)
        assert response["Outcome"] == "Normal", (code_hex, response)
        actual_slots = {name: int(value, 16) for name, value in response["slots"].items()}
        if simd:
            for name, register in XMM_REGISTERS.items():
                expected = hardware[name] if name in hardware else self.machine.reg_read(register)
                assert actual_slots[name] == expected, (code_hex, name, hex(actual_slots[name]), hex(expected), slots)
                index = int(name[3:])
                # Legacy SSE leaves YMM[255:128] unchanged; Unicorn's helpers do not consistently preserve it.
                expected_high = slots[f"ymm{index}_hi"]
                if self.machine.reg_read(getattr(xc, f"UC_X86_REG_YMM{index}")) >> 128 != expected_high:
                    self.unicorn_legacy_high_differences[code_hex] = self.unicorn_legacy_high_differences.get(code_hex, 0) + 1
                assert actual_slots[f"ymm{index}_hi"] == expected_high, (code_hex, f"ymm{index}_hi", actual_slots[f"ymm{index}_hi"], expected_high)
            expected_mxcsr = hardware["mxcsr"] if native else self.machine.reg_read(xc.UC_X86_REG_MXCSR)
            assert actual_slots["mxcsr"] == expected_mxcsr, (code_hex, "mxcsr", hex(actual_slots["mxcsr"]), hex(expected_mxcsr), slots)
        for name, register in REGISTERS.items():
            mask = (1 << 64) - 1
            if zero_source and name == "rax":
                mask ^= (1 << width) - 1
            expected = hardware[name] if name in hardware else self.machine.reg_read(register)
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
        elif family == "division":
            compare_flags &= 0x400
        elif family == "tzcnt":
            compare_flags &= 0x441
        elif family in ("shl", "shr", "sar", "rol", "ror", "rcl", "rcr"):
            masked = (slots["rcx"] & 255) & (63 if width == 64 else 31)
            if masked:
                if masked != 1:
                    compare_flags &= ~0x800
                if family in ("shl", "shr", "sar"):
                    compare_flags &= ~0x10
                    if family != "sar" and masked >= width:
                        compare_flags &= ~1
        actual_flags = sum(actual_slots[flag] << bit for flag, bit in FLAGS.items())
        expected_flags = hardware["eflags"] if native else self.machine.reg_read(xc.UC_X86_REG_EFLAGS)
        assert actual_flags & compare_flags == expected_flags & compare_flags, (code_hex, "flags", hex(actual_flags), hex(expected_flags), hex(compare_flags), slots)
        expected_next = self.machine.reg_read(xc.UC_X86_REG_RIP) if emulate else address + len(code)
        assert int(response["next"], 16) == expected_next, (code_hex, "next", response["next"])
        for start, data in regions:
            expected = bytes(self.machine.mem_read(start, len(data)))
            actual = bytes(response["memory"][hex(start + i).upper().replace("0X", "0x")] for i in range(len(data)))
            assert actual == expected, (code_hex, "memory", hex(start))
        expected_accesses = [f"{kind}:0x{where:X}:{size}" for kind, where, size in self.accesses]
        if memory_read_width is not None:
            # Intel SDM Vol2A 3-265/3-286 指定 m64；Unicorn 2.1.2 错误读取了 m128。
            documented = [f"Load:0x{slots['rbx']:X}:{memory_read_width}"]
            if expected_accesses != documented:
                self.unicorn_access_differences[code_hex] = self.unicorn_access_differences.get(code_hex, 0) + 1
            expected_accesses = documented
        if simd:
            # Unicorn 将 128 位访存拆成两个 64 位 hook；按有序字节访问比较，不声称原子性。
            def access_bytes(accesses):
                result = []
                for access in accesses:
                    kind, where, size = access.split(":")
                    result.extend((kind, int(where, 16) + i) for i in range(int(size)))
                return result
            assert access_bytes(response["Accesses"]) == access_bytes(expected_accesses), (code_hex, "access order", response["Accesses"], expected_accesses)
        else:
            assert response["Accesses"] == expected_accesses, (code_hex, "access order", response["Accesses"], expected_accesses)
        if memory:
            assert response["support"] == "NormalPathOnly", (code_hex, response["support"])
        self.checks += 1

    def reject(self, code_hex):
        response = self.request(bytes.fromhex(code_hex), CODE, {}, [])
        assert not response["supported"], ("unsupported form accepted", code_hex, response)
        self.rejected += 1

    def fault(self, code_hex, byte_count):
        slots = {name: RNG.getrandbits(128) for name in XMM_REGISTERS}
        slots.update({f"ymm{i}_hi": 0xcafe0123456789abcdef001122334455 ^ i for i in range(16)})
        slots["rbx"] = DATA
        slots["mxcsr"] = 0x1f80
        data = RNG.randbytes(byte_count)
        response = self.request(bytes.fromhex(code_hex), CODE, slots, [(DATA, data)])
        assert response["supported"] and response["support"] == "NormalPathOnly", (code_hex, response)
        assert response["Outcome"] == "UnmodeledFaultStop" and response["next"] is None, (code_hex, response)
        assert {name: int(value, 16) for name, value in response["slots"].items()} == slots, (code_hex, "fault committed register")
        assert bytes(response["memory"][f"0x{DATA+i:X}"] for i in range(byte_count)) == data, (code_hex, "fault committed memory")
        self.fault_stops += 1

    def guard_stop(self, code_hex, updates, memory=None, address=CODE):
        slots = {name: RNG.getrandbits(64) for name in GPRS}
        slots.update({flag: RNG.getrandbits(1) for flag in FLAGS})
        slots.update({name: RNG.getrandbits(128) for name in XMM_REGISTERS})
        slots.update({f"ymm{i}_hi": 0xcafe0123456789abcdef001122334455 ^ i for i in range(16)})
        slots["mxcsr"] = 0x1f80
        slots.update(updates)
        response = self.request(bytes.fromhex(code_hex), address, slots, memory or [])
        assert response["supported"] and response["Outcome"] == "UnmodeledFaultStop", (code_hex, response)
        assert response["support"] == "NormalPathOnly" and response["next"] is None, (code_hex, response)
        assert {name: int(value, 16) for name, value in response["slots"].items()} == slots, (code_hex, "guard committed state")
        for start, data in memory or []:
            assert bytes(response["memory"][f"0x{start+i:X}"] for i in range(len(data))) == data, (code_hex, "guard committed memory")
        self.fault_stops += 1


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
            for value in [0, 1, 2, 8, 1 << (width - 1), (1 << width) - 1] + [RNG.getrandbits(width) for _ in range(12)]:
                if width == 32 and value == 0:
                    h.guard_stop(prefix + "0f" + suffix, {"rbx": 0})
                    continue
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
    for code in (prefix + "488b0425" + (DATA + 32).to_bytes(4, "little").hex() for prefix in ("", "67")):
        h.run(code, memory=True)
    address = CODE + len(h.forms) * 32
    code = "488b05" + (DATA + 32 - address - 7).to_bytes(4, "little", signed=True).hex()
    h.run(code, memory=True)


def simd_registers(h):
    moves = [prefix + opcode + modrm
             for prefix, opcodes in (("", ("0f10", "0f11", "0f28", "0f29")),
                                     ("66", ("0f10", "0f11", "0f28", "0f29", "0f6f", "0f7f")),
                                     ("f3", ("0f10", "0f11", "0f6f", "0f7f", "0f7e")),
                                     ("f2", ("0f10", "0f11")))
             for opcode in opcodes for modrm in ("c1", "c0")]
    moves += [prefix + opcode + "c3" for prefix in ("66", "6648") for opcode in ("0f6e", "0f7e")]
    moves += ["660fd6c1", "660fd6c0", "0f12c1", "0f16c1", "0f12c0", "0f16c0",
              "450f10f9", "f3450f10f9", "f2450f11f9", "66450f6efa", "664d0f7efa"]
    logical = [prefix + f"0f{opcode:02x}" + modrm for prefix, opcodes in
               (("", (0x54, 0x55, 0x56, 0x57)), ("66", (0x54, 0x55, 0x56, 0x57, 0xdb, 0xdf, 0xeb, 0xef)))
               for opcode in opcodes for modrm in ("c1", "c0")]
    unpack = [prefix + f"0f{opcode:02x}" + modrm for prefix, opcodes in
              (("", (0x14, 0x15)), ("66", (0x14, 0x15, 0x60, 0x61, 0x62, 0x68, 0x69, 0x6a, 0x6c, 0x6d)))
              for opcode in opcodes for modrm in ("c1", "c0")]
    for code in moves + logical + unpack + ["0f50c1", "660f50c1", "660fd7c1", "66450fd7f9", "66480fd7c1"]:
        for index in range(12):
            def setup(slots, _regions, _address):
                if index == 0:
                    slots.update(xmm0=0, xmm1=(1 << 128) - 1)
                elif index == 1:
                    slots.update(xmm0=(1 << 128) - 1, xmm1=0)
                elif index == 2:
                    slots.update(xmm0=int.from_bytes(bytes(range(16)), "little"),
                                 xmm1=int.from_bytes(bytes(range(16, 32)), "little"))
            h.run(code, simd=True, setup=setup)
    for opcode in ("0fc6", "660fc6", "660f70", "f20f70", "f30f70", "660fc5"):
        for control in range(256):
            for modrm in ("c1", "c0"):
                h.run(opcode + modrm + f"{control:02x}", simd=True)
    for modrm in ("d8", "f8"):
        for count in (0, 1, 7, 8, 15, 16, 17, 31, 127, 128, 255):
            for _ in range(8):
                h.run("660f73" + modrm + f"{count:02x}", simd=True)


def simd_memory(h):
    aligned = [prefix + opcode + "03" for prefix, opcodes in
               (("", ("0f28", "0f29", "0f54", "0f55", "0f56", "0f57", "0f14", "0f15")),
                ("66", ("0f28", "0f29", "0f6f", "0f7f", "0f54", "0f55", "0f56", "0f57",
                        "0fdb", "0fdf", "0feb", "0fef", "0f14", "0f15", "0f60", "0f61", "0f62", "0f68", "0f69", "0f6a", "0f6c", "0f6d")))
               for opcode in opcodes]
    aligned += [opcode + "03e4" for opcode in ("0fc6", "660fc6", "660f70", "f20f70", "f30f70")]
    unaligned = [prefix + opcode + "03" for prefix, opcodes in
                 (("", ("0f10", "0f11", "0f12", "0f13", "0f16", "0f17")),
                  ("66", ("0f10", "0f11", "0f12", "0f13", "0f16", "0f17", "0f6e", "0f7e", "0fd6")),
                  ("6648", ("0f6e", "0f7e")), ("f3", ("0f10", "0f11", "0f6f", "0f7f", "0f7e")),
                  ("f2", ("0f10", "0f11"))) for opcode in opcodes]
    for code in aligned + unaligned:
        for offset in ((32,) if code in aligned else (32, 33, 39, 47)):
            for _ in range(4):
                h.run(code, simd=True, memory=True, setup=lambda s, r, a: s.update(rbx=DATA + offset))
    for code in ("64450f10f9", "65450f10f9"):
        # 段覆盖对寄存器形式没有作用。
        h.run(code, simd=True)
    for code in ("64440f100b", "65440f100b", "67440f100b", "67440f110b"):
        def setup(slots, _regions, _address):
            slots["rbx"] = 33 if code[:2] in ("64", "65") else 0xF00DCAFE00000000 | (DATA + 33)
        h.run(code, simd=True, memory=True, setup=setup)
    for code, size in (("0f1003", 16), ("0f1103", 16), ("f30f1003", 4), ("f30f1103", 4),
                       ("f20f1003", 8), ("f20f1103", 8), ("660f6e03", 4), ("660f7e03", 4)):
        h.fault(code, size - 1)


def division_and_loops(h):
    for width in (8, 16, 32, 64):
        prefix = "66" if width == 16 else "48" if width == 64 else ""
        mask = (1 << width) - 1
        for signed in (False, True):
            opcode = prefix + ("f6" if width == 8 else "f7") + ("fb" if signed else "f3")
            for _ in range(80):
                divisor = RNG.randint(1, (1 << (width - 1)) - 1)
                quotient = RNG.randint(0, (1 << (width - 2)) - 1)
                remainder = RNG.randrange(divisor)
                dividend = quotient * divisor + remainder
                if signed and RNG.getrandbits(1): dividend = -dividend
                if signed and RNG.getrandbits(1): divisor = -divisor
                def setup(slots, _regions, _address):
                    slots["rbx"] = divisor & mask
                    if width == 8:
                        slots["rax"] = (slots["rax"] & ~65535) | (dividend & 65535)
                    else:
                        slots["rax"] = (slots["rax"] & ~mask) | (dividend & mask)
                        slots["rdx"] = (slots["rdx"] & ~mask) | ((dividend >> width) & mask)
                h.run(opcode, width=width, family="division", setup=setup)
            h.guard_stop(opcode, {"rax": 0, "rdx": 0, "rbx": 0})
            h.guard_stop(opcode, {"rax": 256 if width == 8 else 0, "rdx": 1, "rbx": 1})
    for code in ("e005", "e105", "e205", "67e005", "67e105", "67e205"):
        for count in (0, 1, 2, 0x100000000, 0x100000001, 0xffffffffffffffff):
            for flags in (0, FLAG_MASK):
                h.run(code, old_flags=flags, setup=lambda s, r, a: s.update(rcx=count))
    for ah in range(256):
        for code in ("9e", "9f"):
            h.run(code, setup=lambda s, r, a: s.update(rax=(s["rax"] & ~0xff00) | (ah << 8)))


def simd_integer(h):
    opcodes = (0xfc, 0xfd, 0xfe, 0xd4, 0xf8, 0xf9, 0xfa, 0xfb, 0xec, 0xed, 0xdc, 0xdd,
               0xe8, 0xe9, 0xd8, 0xd9, 0x74, 0x75, 0x76, 0x64, 0x65, 0x66, 0xda, 0xde, 0xea, 0xee, 0xd5, 0xe5, 0xe4)
    for opcode in opcodes:
        for modrm in ("c1", "c0", "03"):
            for index in range(16):
                def setup(slots, _regions, _address):
                    if index < 8:
                        patterns = (0, 0xff, 0x7f, 0x80, 1, 0x81, 0xfe, 0x40)
                        slots["xmm0"] = int.from_bytes(bytes([patterns[index]]) * 16, "little")
                        slots["xmm1"] = int.from_bytes(bytes([patterns[(index + 3) % 8]]) * 16, "little")
                h.run(f"660f{opcode:02x}" + modrm, simd=True, memory=modrm == "03", setup=setup)
    for opcode in (0xf1, 0xf2, 0xf3, 0xd1, 0xd2, 0xd3, 0xe1, 0xe2):
        for count in (0, 1, 15, 16, 31, 32, 63, 64, 127, 255, 0x1000000000000000):
            for modrm in ("c1", "03"):
                def setup(slots, regions, _address):
                    slots["xmm1"] = (RNG.getrandbits(64) << 64) | count
                    if regions:
                        regions[0][1][32:48] = slots["xmm1"].to_bytes(16, "little")
                h.run(f"660f{opcode:02x}" + modrm, simd=True, memory=modrm == "03", setup=setup)
    for opcode, modrm in ((0x71, "f0"), (0x72, "f0"), (0x73, "f0"), (0x71, "d0"),
                          (0x72, "d0"), (0x73, "d0"), (0x71, "e0"), (0x72, "e0")):
        for count in (0, 1, 15, 16, 31, 32, 63, 64, 127, 255):
            h.run(f"660f{opcode:02x}{modrm}{count:02x}", simd=True)


FP_EDGES = {
    32: [0, 0x80000000, 0x3f800000, 0xbf800000, 0x3f000000, 0x3fc00000, 0x40400000,
         0x7f7fffff, 0x00800000, 0x007fffff, 1, 0x80000001, 0x7f800000, 0xff800000,
         0x7fc01234, 0x7f801234, 0xffc05678],
    64: [0, 0x8000000000000000, 0x3ff0000000000000, 0xbff0000000000000, 0x3fe0000000000000,
         0x3ff8000000000000, 0x4008000000000000, 0x7fefffffffffffff, 0x0010000000000000,
         0x000fffffffffffff, 1, 0x8000000000000001, 0x7ff0000000000000, 0xfff0000000000000,
         0x7ff8000000001234, 0x7ff0000000001234, 0xfff8000000005678],
}
FP_CONTROLS = [0x1f80 | (rounding << 13) | (daz << 6) | (ftz << 15)
               for rounding in range(4) for daz in range(2) for ftz in range(2)]


def floating(h):
    def input_setup(width, left, right, control, packed=False):
        def setup(slots, _regions, _address):
            mask = (1 << width) - 1
            if packed:
                slots["xmm0"] = sum(left << offset for offset in range(0, 128, width))
                slots["xmm1"] = sum(right << offset for offset in range(0, 128, width))
            else:
                slots["xmm0"] = (slots["xmm0"] & ~mask) | left
                slots["xmm1"] = (slots["xmm1"] & ~mask) | right
            slots["mxcsr"] = control | RNG.getrandbits(6)
        return setup

    for prefix, width, packed in (("", 32, True), ("66", 64, True), ("f3", 32, False), ("f2", 64, False)):
        edges = FP_EDGES[width]
        pairs = [(a, c, 0x1f80) for a in edges for c in edges]
        focused = [(edges[i], edges[j]) for i, j in ((2, 6), (8, 6), (10, 0), (10, 14), (15, 10),
                                                    (7, 4), (7, 7), (8, 4), (0, 1), (14, 15), (15, 14))]
        pairs += [(a, c, control) for a, c in focused for control in FP_CONTROLS]
        for opcode in ("58", "59", "5c", "5e", "5d", "5f", "51"):
            for a, c, control in pairs:
                h.run(prefix + "0f" + opcode + "c1", simd=True, native=True,
                      setup=input_setup(width, a, c, control, packed))
        for predicate in list(range(8)) + [255]:
            for i, a in enumerate(edges):
                for c in (edges[(i + 3) % len(edges)], edges[10], edges[14], edges[15]):
                    h.run(prefix + "0fc2c1" + f"{predicate:02x}", simd=True, native=True,
                          setup=input_setup(width, a, c, FP_CONTROLS[i % 16], packed), emulate=predicate != 255)
    for prefix, width in (("", 32), ("66", 64)):
        for opcode in ("2e", "2f"):
            for i, a in enumerate(FP_EDGES[width]):
                for j, c in enumerate(FP_EDGES[width]):
                    h.run(prefix + "0f" + opcode + "c1", simd=True, native=True,
                          setup=input_setup(width, a, c, FP_CONTROLS[(i + j) % 16]))

    scalar = [(prefix + rex + "0f" + opcode + "c1", width)
              for prefix, width in (("f3", 32), ("f2", 64)) for rex in ("", "48") for opcode in ("2c", "2d")]
    scalar += [("f30f5ac1", 32), ("f20f5ac1", 64)]
    packed = [("0f5ac1", 32), ("660f5ac1", 64), ("f30f5bc1", 32), ("660f5bc1", 32),
              ("f20fe6c1", 64), ("660fe6c1", 64)]
    for code, width in scalar + packed:
        edges = FP_EDGES[width] + ([0x380fffffe1000000, 0x380ffffffffff000, 0x47effffff0000000] if width == 64
                                 else [0x4effffff, 0x4f000000, 0xcf000000, 0xcf000001])
        for value in edges:
            for control in FP_CONTROLS:
                h.run(code, simd=True, native=True, setup=input_setup(width, value, value, control, code in dict(packed)))
    for code, width in [(prefix + rex + "0f2ac3", 64 if rex else 32) for prefix in ("f3", "f2") for rex in ("", "48")]:
        for value in (0, 1, -1, 3, -(1 << (width - 1)), (1 << (width - 1)) - 1, (1 << 24) + 1, -(1 << 24) - 1):
            for control in FP_CONTROLS:
                def setup(slots, _regions, _address):
                    slots["rbx"] = value & ((1 << 64) - 1)
                    slots["mxcsr"] = control | RNG.getrandbits(6)
                h.run(code, simd=True, native=True, setup=setup)
    for code in ("0f5bc1", "f30fe6c1"):
        for control in FP_CONTROLS:
            for pattern in (0, 0x7fffffff, 0x80000000, 0xffffffff, 0x01000001, 0xfeffffff):
                def setup(slots, _regions, _address):
                    slots["xmm1"] = sum(pattern << offset for offset in range(0, 128, 32))
                    slots["mxcsr"] = control | RNG.getrandbits(6)
                h.run(code, simd=True, native=True, setup=setup)
    # 无屏蔽异常只验证显式停止，不在本机触发异常递送。
    h.guard_stop("f30f5ec1", {"xmm0": 0x3f800000, "xmm1": 0, "mxcsr": 0x1d80})
    h.guard_stop("f30f5ec1", {"xmm0": 0, "xmm1": 0, "mxcsr": 0x1f00})
    h.guard_stop("0f2fc1", {"xmm0": 0x7fc01234, "xmm1": 0, "mxcsr": 0x1f00})


def floating_memory(h):
    # 精确正规数使这里的 Unicorn 比对不依赖其缺失的浮点异常状态。
    forms = []
    for prefix, width, packed in (("", 32, True), ("66", 64, True), ("f3", 32, False), ("f2", 64, False)):
        forms += [(prefix + "0f" + opcode + "03", width, False, packed) for opcode in ("58", "59", "5c", "5e", "5d", "5f", "51")]
        forms += [(prefix + "0fc203" + f"{predicate:02x}", width, False, packed) for predicate in range(8)]
    forms += [(prefix + "0f" + opcode + "03", width, False, False)
              for prefix, width in (("", 32), ("66", 64)) for opcode in ("2e", "2f")]
    forms += [(prefix + rex + "0f" + opcode + "03", width, False, False)
              for prefix, width in (("f3", 32), ("f2", 64)) for rex in ("", "48") for opcode in ("2c", "2d")]
    forms += [(prefix + rex + "0f2a03", 64 if rex else 32, True, False)
              for prefix in ("f3", "f2") for rex in ("", "48")]
    forms += [("f30f5a03", 32, False, False), ("f20f5a03", 64, False, False)]
    forms += [(code, width, integer, True) for code, width, integer in
              (("0f5a03", 32, False), ("660f5a03", 64, False), ("f30f5b03", 32, False),
               ("660f5b03", 32, False), ("f20fe603", 64, False), ("660fe603", 64, False),
               ("0f5b03", 32, True), ("f30fe603", 32, True))]
    for code, width, integer, packed in forms:
        for offset in ((32,) if packed else (32, 33, 39)):
            def setup(slots, regions, _address):
                one = 1 if integer else 0x3f800000 if width == 32 else 0x3ff0000000000000
                slots["xmm0"] = sum((0x3f800000 if width == 32 else 0x3ff0000000000000) << bit for bit in range(0, 128, width))
                slots["mxcsr"] = FP_CONTROLS[offset % 16] | RNG.getrandbits(6)
                slots["rbx"] = DATA + offset
                regions[0][1][offset:offset+16] = sum(one << bit for bit in range(0, 128, width)).to_bytes(16, "little")
            h.run(code, simd=True, memory=True, setup=setup, memory_read_width=8 if code in ("0f5a03", "f30fe603") else None)
    for code, size in (("f30f5803", 4), ("f20f5803", 8), ("0f5803", 16), ("660f5803", 16),
                       ("0f2f03", 4), ("660f2e03", 8), ("f3480f2a03", 8), ("f30fe603", 8),
                       ("f20fe603", 16), ("0fae13", 4), ("0fae1b", 4)):
        h.fault(code, size - 1)
    for code in ("0fae13", "0fae1b"):
        for control in FP_CONTROLS:
            def setup(slots, regions, _address):
                slots["rbx"] = DATA + 33
                slots["mxcsr"] = control | RNG.getrandbits(6)
                regions[0][1][33:37] = (control | RNG.getrandbits(6)).to_bytes(4, "little")
            h.run(code, simd=True, memory=True, setup=setup)
    h.guard_stop("0fae13", {"rbx": DATA}, [(DATA, (0x10000 | 0x1f80).to_bytes(4, "little"))])
    for code in ("0f5803", "660f5803", "0f2803", "660f6f03", "660ffe03", "660ff103"):
        h.guard_stop(code, {"rbx": DATA + 1}, [(DATA + 1, b"\0" * 16)])


def integer_remaining(h):
    for width in (8, 16, 32, 64):
        prefix = "66" if width == 16 else "48" if width == 64 else ""
        for family, modrm in (("rcl", "d0"), ("rcr", "d8")):
            code = prefix + ("d2" if width == 8 else "d3") + modrm
            for count in (0, 1, 2, 8, 9, 16, 17, 18, 27, 31, 32, 33, 63, 64, 65, 255):
                masked = count & (63 if width == 64 else 31)
                if width in (8, 16) and masked and masked % (width + 1) == 0:
                    h.guard_stop(code, {"rcx": count})
                    continue
                for source in (0, 1, 1 << (width - 1), (1 << width) - 1):
                    for flags in (0, FLAG_MASK):
                        h.run(code, width=width, family=family, values=(source, 0), count=count, old_flags=flags)
            for count in (0, 1, 2, 31):
                h.run(prefix + ("d2" if width == 8 else "d3") + ("13" if family == "rcl" else "1b"),
                      width=width, family=family, count=count, memory=True)
            h.run(prefix + ("c0" if width == 8 else "c1") + modrm + "01", width=width, family=family, count=1)
    for width, prefix in ((16, "66f3"), (32, "f3"), (64, "f348")):
        for source in [0, 1, (1 << width) - 1] + [1 << bit for bit in range(width)]:
            h.run(prefix + "0fbcc3", width=width, family="tzcnt", values=(0, source))
        for modrm in ("c0", "03"):
            h.run(prefix + "0fbc" + modrm, width=width, family="tzcnt", memory=modrm == "03")
    for code in ("c9", "66c9", "67c9", "6766c9"):
        for _ in range(12):
            h.run(code, memory=True, setup=lambda s, r, a: s.update(rbp=STACK + 32))
    for code in ("d7", "67d7", "64d7", "65d7", "6467d7", "6567d7"):
        for index in (0, 1, 31):
            def setup(slots, _regions, _address):
                slots["rax"] = (slots["rax"] & ~255) | index
                slots["rbx"] = 32 if code.startswith(("64", "65")) else DATA + 32
                if "67" in code: slots["rbx"] |= 0xcafef00d00000000
            h.run(code, memory=True, setup=setup)
    for opcode in (0xa4, 0xaa, 0xac, 0xa6, 0xae):
        for width, prefix in ((8, ""), (16, "66"), (32, ""), (64, "48")):
            for address_prefix in ("", "67"):
                for segment in ("", "64", "65"):
                    code = segment + address_prefix + prefix + f"{opcode + (width != 8):02x}"
                    for flags in (0, FLAG_MASK):
                        def setup(slots, _regions, _address):
                            slots["rsi"] = 32 if segment else DATA + 32
                            slots["rdi"] = DATA + 80
                            if address_prefix:
                                slots["rsi"] |= 0xcafef00d00000000
                                slots["rdi"] |= 0xcafef00d00000000
                        h.run(code, memory=True, setup=setup, old_flags=flags)
    h.guard_stop("c9", {"rbp": DATA}, [(DATA, b"\0" * 7)])
    h.guard_stop("a5", {"rsi": DATA, "rdi": STACK}, [(DATA, b"\0" * 4), (STACK, b"\0" * 3)])
    bad = 0x800000000000
    for code in ("ffe0", "ffd0"):
        h.guard_stop(code, {"rax": bad, "rsp": STACK + 16}, [(STACK, b"\x5a" * 32)])
    for code in ("ff23", "ff13"):
        h.guard_stop(code, {"rbx": DATA, "rsp": STACK + 16}, [(DATA, bad.to_bytes(8, "little")), (STACK, b"\x5a" * 32)])
    for code in ("c3", "c21000"):
        h.guard_stop(code, {"rsp": DATA}, [(DATA, bad.to_bytes(8, "little"))])
    boundary = 0x7ffffffffff0
    h.guard_stop("e920000000", {}, address=boundary)
    h.guard_stop("e820000000", {"rsp": STACK + 16}, [(STACK, b"\x5a" * 32)], address=boundary)
    for code, taken, not_taken in (("747f", {"zf": 1}, {"zf": 0}), ("e37f", {"rcx": 0}, {"rcx": 1}),
                                   ("e27f", {"rcx": 2}, {"rcx": 1})):
        h.guard_stop(code, taken, address=boundary)
        response = h.request(bytes.fromhex(code), boundary, not_taken, [])
        assert response["Outcome"] == "Normal" and int(response["next"], 16) == boundary + 2, (code, response)
        h.checks += 1


def memory_pop_and_bits(h):
    for prefix, width in (("", 64), ("66", 16)):
        for operand in ("03", "0424", "4424f8", "442402", "04cb"):
            for flags in (0, FLAG_MASK):
                h.run(prefix + "8f" + operand, memory=True, old_flags=flags,
                      setup=lambda s, r, a: s.update(rcx=2))
        for code in (prefix + "418f0424", "64" + prefix + "8f03", "65" + prefix + "8f03",
                     "67" + prefix + "8f03", "67" + prefix + "8f0424"):
            def setup(slots, _regions, _address):
                slots["r12"] = DATA + 33
                if code.startswith(("64", "65")): slots["rbx"] = 33
                if code.startswith("67"): slots["rbx"] |= 0xcafef00d00000000
            h.run(code, memory=True, setup=setup)
        h.guard_stop(prefix + "8f03", {"rsp": STACK, "rbx": DATA},
                     [(STACK, b"\x5a" * (width // 8)), (DATA, b"\0" * (width // 8 - 1))])
        h.guard_stop(prefix + "8f03", {"rsp": STACK, "rbx": DATA},
                     [(STACK, b"\x5a" * (width // 8 - 1)), (DATA, b"\0" * (width // 8))])
    # 地址宽度只约束目的寻址；栈读和 RSP 自增仍为 64 位。
    high_stack = 0x100000000 + STACK
    h.machine.mem_map(high_stack, 0x1000)
    for prefix in ("", "66"):
        def setup(slots, regions, _address):
            slots["rsp"] = high_stack + 64
            regions.append((high_stack, bytearray(RNG.randbytes(128))))
        h.run("67" + prefix + "8f0424", memory=True, setup=setup)

    for width, prefix in ((16, "66"), (32, ""), (64, "48")):
        for opcode, group in (("a3", "23"), ("ab", "2b"), ("b3", "33"), ("bb", "3b")):
            for offset in (-2 * width - 1, -width, -1, 0, 1, width - 1, width, 2 * width + 1):
                for flags in (0, FLAG_MASK):
                    def setup(slots, _regions, _address):
                        slots.update(rbx=DATA + 64, rcx=offset & ((1 << 64) - 1))
                    h.run(prefix + "0f" + opcode + "0b", width=width, family="bittest", memory=True,
                          setup=setup, old_flags=flags)
            for immediate in (0, width - 1, width, 127, 128, 255):
                h.run(prefix + "0fba" + group + f"{immediate:02x}", width=width, family="bittest", memory=True)
            # 偏移寄存器同时参与地址；FS/GS 加到按地址宽度回绕后的位串地址上。
            h.run("64" + prefix + "0f" + opcode + "1b", width=width, family="bittest", memory=True,
                  setup=lambda s, r, a: s.update(rbx=32))
            for segment in ("64", "65"):
                h.run(segment + "67" + prefix + "0f" + opcode + "0b", width=width, family="bittest", memory=True,
                      setup=lambda s, r, a: s.update(rbx=0xcafef00dfffffff8, rcx=128))
            h.guard_stop(prefix + "0f" + opcode + "0b", {"rbx": DATA, "rcx": 0},
                         [(DATA, b"\0" * (width // 8 - 1))])


def simd_sse41(h):
    # PCMPEQQ、PMIN/PMAX 的符号区别以及 PMULLD 的低 32 位乘积。
    opcodes = (0x29, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f, 0x40, 0x17)
    edges = (0, 1, 0x7f7f7f7f, 0x80808080, 0xffffffff, 0x7fffffff, 0x80000000, 0x80007fff)
    for opcode in opcodes:
        for rex, modrm in (("", "c1"), ("", "c0"), ("45", "f9"), ("", "03")):
            for index in range(24):
                def setup(slots, regions, _address):
                    if index < len(edges):
                        left, right = edges[index], edges[(index + 3) % len(edges)]
                        slots["xmm0"] = sum(left << bit for bit in range(0, 128, 32))
                        slots["xmm1"] = sum(right << bit for bit in range(0, 128, 32))
                        slots.update(xmm15=slots["xmm0"], xmm9=slots["xmm1"])
                        if regions: regions[0][1][32:48] = slots["xmm1"].to_bytes(16, "little")
                h.run("66" + rex + f"0f38{opcode:02x}" + modrm, simd=True, memory=modrm == "03", setup=setup)
        h.fault(f"660f38{opcode:02x}03", 15)
        h.guard_stop(f"660f38{opcode:02x}03", {"rbx": DATA + 1}, [(DATA + 1, b"\0" * 16)])
    # 每个 PSHUFB 控制字节都覆盖；bits 6:4 忽略，bit 7 强制结果为零。
    for rex, modrm in (("", "c1"), ("", "c0"), ("45", "f9"), ("", "03")):
        for control in range(256):
            def setup(slots, regions, _address):
                slots["xmm0"] = int.from_bytes(bytes(range(16)), "little")
                slots["xmm1"] = int.from_bytes(bytes([control]) * 16, "little")
                if modrm == "c0": slots["xmm0"] = slots["xmm1"]
                slots.update(xmm15=slots["xmm0"], xmm9=slots["xmm1"])
                if regions: regions[0][1][32:48] = slots["xmm1"].to_bytes(16, "little")
            h.run("66" + rex + "0f3800" + modrm, simd=True, memory=modrm == "03", setup=setup)
    h.fault("660f380003", 15)
    h.guard_stop("660f380003", {"rbx": DATA + 1}, [(DATA + 1, b"\0" * 16)])
    # PMOVSX/ZX 只读 m64/m32/m16；这些子宽内存形式允许非 16 字节对齐。
    for first in (0x20, 0x30):
        for delta, size in enumerate((8, 4, 2, 8, 4, 8)):
            opcode = first + delta
            for rex, modrm in (("", "c1"), ("", "c0"), ("45", "f9"), ("", "03")):
                for index in range(24):
                    def setup(slots, regions, _address):
                        value = int.from_bytes(bytes([edges[index % len(edges)] & 255]) * 16, "little") if index < 8 else RNG.getrandbits(128)
                        slots.update(xmm1=value, xmm9=value)
                        if modrm == "c0": slots["xmm0"] = value
                        if regions:
                            offset = 32 + index % 3
                            slots["rbx"] = DATA + offset
                            regions[0][1][offset:offset+16] = value.to_bytes(16, "little")
                    h.run("66" + rex + f"0f38{opcode:02x}" + modrm, simd=True, memory=modrm == "03", setup=setup)
            h.fault(f"660f38{opcode:02x}03", size - 1)


def main():
    command = ["dotnet", str(Path(sys.argv[1]) if len(sys.argv) > 1 else DLL), "serve"]
    with subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, encoding="utf-8", bufsize=1) as server:
        h = Harness(server)
        arithmetic(h)
        shifts(h)
        conditions(h)
        other_registers(h)
        memory_and_control(h)
        simd_registers(h)
        simd_memory(h)
        division_and_loops(h)
        simd_integer(h)
        floating(h)
        floating_memory(h)
        integer_remaining(h)
        memory_pop_and_bits(h)
        simd_sse41(h)
        for code in ("f0480103", "f3a4", "9d", "d3f0",
                     "0f6fc1", "0fefc1", "0f6ec3", "660f3a15c101"):
            h.reject(code)
        server.stdin.close()
        server.wait()
        assert server.returncode == 0, server.returncode
        if h.native is not None: h.native.close()
        print(json.dumps({"x64_differential": h.checks, "forms": len(h.forms), "unsupported_rejected": h.rejected, "fault_stops": h.fault_stops,
                          "native_float_checks": h.native_checks, "unicorn_float_differences": h.unicorn_fp_differences,
                          "native_only_cmp_imm8_checks": h.native_only_checks,
                          "unicorn_float_examples": h.unicorn_fp_examples,
                          "unicorn_access_differences": h.unicorn_access_differences,
                          "unicorn_legacy_high_difference_count": sum(h.unicorn_legacy_high_differences.values()),
                          "unicorn_legacy_high_difference_forms": len(h.unicorn_legacy_high_differences),
                          "scope": "production MIR + JSON roundtrip vs Unicorn; synthetic SSE also compared to native CPU data/MXCSR; no game execution or exception-delivery proof"}, indent=2))


if __name__ == "__main__":
    main()
