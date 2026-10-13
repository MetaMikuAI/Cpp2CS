"""生产 MIR 的 AVX/SSE4.2 合成差分；包含 YMM 高半、故障和硬件 MXCSR。"""
import json
import subprocess
import sys
from capstone import Cs, CS_ARCH_X86, CS_MODE_64, CS_OP_MEM

from x64_differential import Harness, RNG, DATA, GPRS, FLAGS, FLAG_MASK, FP_CONTROLS, FP_EDGES, xc
from x64_avx_native import NativeAvxOracle, FLOAT_CODES, FMA_CODES, FMA_EXTRA_CODES, FLOAT_MEMORY_CODES, ROUND_CODES, LEGACY_HIGH_CODES, MASK_CODES, vex


class NativeVectorHarness(Harness):
    def __init__(self, server, oracle):
        super().__init__(server)
        self.oracle = oracle
        self.decoder = Cs(CS_ARCH_X86, CS_MODE_64)
        self.decoder.detail = True
        self.pcmp_unicorn_differences = 0
        self.avx_native_checks = 0

    def run(self, code_hex, *, simd=False, memory=False, setup=None):
        if code_hex not in self.forms: self.forms[code_hex] = 0x10000 + len(self.forms) * 32
        address = self.forms[code_hex]
        slots = {name: RNG.getrandbits(64) for name in GPRS}
        slots.update({name: RNG.getrandbits(1) for name in FLAGS})
        slots.update({f"xmm{i}": RNG.getrandbits(128) for i in range(16)})
        slots.update({f"ymm{i}_hi": RNG.getrandbits(128) for i in range(16)})
        slots.update(mxcsr=(RNG.getrandbits(16) | 0x1f80))
        regions = [(DATA, bytearray(RNG.randbytes(128)))] if memory else []
        if memory: slots["rbx"] = DATA + 32
        if setup is not None: setup(slots, regions, address)
        hardware_case(self, self.oracle, code_hex, slots, regions, address)
        if code_hex.startswith("660f3a63"):
            self.machine.mem_write(address, bytes.fromhex(code_hex))
            self.machine.reg_write(xc.UC_X86_REG_XMM0, slots["xmm0"])
            self.machine.reg_write(xc.UC_X86_REG_XMM1, slots["xmm1"])
            self.machine.reg_write(xc.UC_X86_REG_RBX, slots["rbx"])
            self.machine.reg_write(xc.UC_X86_REG_RCX, slots["rcx"])
            self.machine.reg_write(xc.UC_X86_REG_EFLAGS, 2 | sum(slots[name] << bit for name, bit in FLAGS.items()))
            for start, data in regions: self.machine.mem_write(start, bytes(data))
            self.machine.emu_start(address, address + len(bytes.fromhex(code_hex)), count=1)
            expected = self.last_response["slots"]
            flags = sum(int(expected[name], 16) << bit for name, bit in FLAGS.items())
            if self.machine.reg_read(xc.UC_X86_REG_RCX) != int(expected["rcx"], 16) or self.machine.reg_read(xc.UC_X86_REG_EFLAGS) & FLAG_MASK != flags:
                self.pcmp_unicorn_differences += 1
        if memory:
            instruction = next(self.decoder.disasm(bytes.fromhex(code_hex), address))
            index, operand = next((index, operand) for index, operand in enumerate(instruction.operands) if operand.type == CS_OP_MEM)
            access = "Store" if index == 0 else "Load"
            assert self.last_response["Accesses"] == [f"{access}:0x{slots['rbx']:X}:{operand.size}"], (code_hex, self.last_response["Accesses"], operand.size)
            if instruction.mnemonic.startswith("vmovnt"):
                assert len(self.last_response["events"]) == 1 and self.last_response["events"][0]["NonTemporal"]
                assert self.last_response["events"][0]["AtomicWidth"] == 0


def vector_setup(slots, _regions, _address):
    slots.update({f"ymm{i}_hi": RNG.getrandbits(128) for i in range(16)})


def vectors(h):
    for vl in (128, 256):
        for opcode, pp in ((0xe7, 1), (0x2b, 0), (0x2b, 1)):
            h.run(vex(opcode, pp=pp, vl=vl, rm=3, memory=True), simd=True, memory=True, setup=vector_setup)
            h.guard_stop(vex(opcode, pp=pp, vl=vl, rm=3, memory=True), {"rbx": DATA + 1}, [(DATA + 1, b"\0" * 32)])
        for opcode, pp in ((0x10, 0), (0x11, 0), (0x28, 0), (0x29, 0), (0x10, 1), (0x11, 1),
                           (0x28, 1), (0x29, 1), (0x6f, 1), (0x7f, 1), (0x6f, 2), (0x7f, 2)):
            aligned = opcode in (0x28, 0x29) or opcode in (0x6f, 0x7f) and pp == 1
            for dest, source in ((0, 1), (0, 0), (15, 9)):
                h.run(vex(opcode, pp=pp, vl=vl, dest=dest, rm=source), simd=True, setup=vector_setup)
            for offset in ((32,) if aligned else (32, 33, 47)):
                def setup(slots, regions, address):
                    vector_setup(slots, regions, address)
                    slots["rbx"] = DATA + offset
                h.run(vex(opcode, pp=pp, vl=vl, rm=3, memory=True), simd=True, memory=True, setup=setup)
            h.fault(vex(opcode, pp=pp, vl=vl, rm=3, memory=True), vl // 8 - 1)
            if aligned: h.guard_stop(vex(opcode, pp=pp, vl=vl, rm=3, memory=True), {"rbx": DATA + 1}, [(DATA + 1, b"\0" * 32)])
        for pp, opcodes in ((0, (0x54, 0x55, 0x56, 0x57)), (1, (0x54, 0x55, 0x56, 0x57, 0xdb, 0xdf, 0xeb, 0xef))):
            for opcode in opcodes:
                for dest, first, second in ((0, 1, 2), (0, 0, 1), (0, 1, 0), (15, 9, 15)):
                    for _ in range(4): h.run(vex(opcode, pp=pp, vl=vl, source=first, dest=dest, rm=second), simd=True, setup=vector_setup)
                h.run(vex(opcode, pp=pp, vl=vl, source=1, rm=3, memory=True), simd=True, memory=True,
                      setup=lambda s, r, a: s.update(rbx=DATA + 33))
        integer = [(1, opcode) for opcode in (0xfc, 0xfd, 0xfe, 0xd4, 0xf8, 0xf9, 0xfa, 0xfb, 0xec, 0xed, 0xdc, 0xdd,
                   0xe8, 0xe9, 0xd8, 0xd9, 0x74, 0x75, 0x76, 0x64, 0x65, 0x66, 0xda, 0xde, 0xea, 0xee, 0xd5, 0xe5, 0xe4)]
        integer += [(2, opcode) for opcode in (0x29, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f, 0x40)]
        for opcode_map, opcode in integer:
            for first, second, memory in ((1, 2, False), (0, 1, False), (1, 0, False), (1, 3, True)):
                for _ in range(8):
                    h.run(vex(opcode, vl=vl, source=first, rm=second, opcode_map=opcode_map, memory=memory), simd=True, memory=memory, setup=vector_setup)
        for opcode in (0xf1, 0xf2, 0xf3, 0xd1, 0xd2, 0xd3, 0xe1, 0xe2):
            for count in (0, 1, 15, 16, 31, 32, 63, 64, 255, 0x1000000000000000):
                def setup(slots, regions, address):
                    vector_setup(slots, regions, address)
                    slots["xmm2"] = count | (RNG.getrandbits(64) << 64)
                h.run(vex(opcode, vl=vl, source=1, rm=2), simd=True, setup=setup)
        for opcode, group in ((0x71, 6), (0x72, 6), (0x73, 6), (0x71, 2), (0x72, 2), (0x73, 2), (0x71, 4), (0x72, 4), (0x73, 3), (0x73, 7)):
            for count in (0, 1, 15, 16, 31, 32, 63, 64, 255):
                h.run(vex(opcode, vl=vl, dest=group, rm=1, immediate=count), simd=True, setup=vector_setup)
        for opcode, w in ((0x45, 0), (0x45, 1), (0x46, 0), (0x47, 0), (0x47, 1)):
            for count in (0, 1, 31, 32, 63, 64, 255, 0xffffffff):
                def setup(slots, regions, address):
                    vector_setup(slots, regions, address)
                    width = 64 if w else 32
                    control = sum(count << offset for offset in range(0, 256, width))
                    slots.update(xmm2=control & ((1 << 128) - 1), ymm2_hi=control >> 128)
                h.run(vex(opcode, vl=vl, opcode_map=2, w=w, source=1, rm=2), simd=True, setup=setup)
        for opcode, pp, two in ((0xc6, 0, True), (0xc6, 1, True), (0x70, 1, False), (0x70, 2, False), (0x70, 3, False)):
            for control in range(256):
                h.run(vex(opcode, pp=pp, vl=vl, source=1 if two else 0, rm=2, immediate=control), simd=True, setup=vector_setup)
        for pp, opcodes in ((0, (0x14, 0x15)), (1, (0x14, 0x15, 0x60, 0x61, 0x62, 0x68, 0x69, 0x6a, 0x6c, 0x6d))):
            for opcode in opcodes:
                for _ in range(8): h.run(vex(opcode, pp=pp, vl=vl, source=1, rm=2), simd=True, setup=vector_setup)
        for first in (0x20, 0x30):
            for delta, size in enumerate((8, 4, 2, 8, 4, 8)):
                for _ in range(8): h.run(vex(first + delta, vl=vl, opcode_map=2), simd=True, setup=vector_setup)
                h.run(vex(first + delta, vl=vl, opcode_map=2, rm=3, memory=True), simd=True, memory=True,
                      setup=lambda s, r, a: s.update(rbx=DATA + 33))
                h.fault(vex(first + delta, vl=vl, opcode_map=2, rm=3, memory=True), size * (vl // 128) - 1)
        for _ in range(32): h.run(vex(0x00, vl=vl, opcode_map=2, source=1, rm=2), simd=True, setup=vector_setup)
        for opcode, pp in ((0x50, 0), (0x50, 1), (0xd7, 1)):
            for _ in range(16): h.run(vex(opcode, pp=pp, vl=vl), simd=True, setup=vector_setup)
    for pp in (2, 3):
        for opcode in (0x10, 0x11):
            for first, second in ((1, 2), (0, 1), (1, 0)):
                h.run(vex(opcode, pp=pp, source=first, rm=second), simd=True, setup=vector_setup)
            h.run(vex(opcode, pp=pp, rm=3, memory=True), simd=True, memory=True, setup=vector_setup)
    for w in (0, 1):
        for opcode in (0x6e, 0x7e):
            h.run(vex(opcode, w=w, rm=3), simd=True, setup=vector_setup)
            h.run(vex(opcode, w=w, rm=3, memory=True), simd=True, memory=True, setup=vector_setup)
    for opcode, pp in ((0x7e, 2), (0xd6, 1)):
        h.run(vex(opcode, pp=pp), simd=True, setup=vector_setup)
        h.run(vex(opcode, pp=pp, rm=3, memory=True), simd=True, memory=True, setup=vector_setup)
    for opcode in (0x18, 0x38):
        for control in (0, 1, 2, 127, 255):
            h.run(vex(opcode, vl=256, opcode_map=3, source=1, rm=2, immediate=control), simd=True, setup=vector_setup)
            h.run(vex(opcode + 1, vl=256, opcode_map=3, immediate=control), simd=True, setup=vector_setup)
    for code in ("c5f877", "c5fc77", "c5f810c1", "c5fa10c1", "c5f857c1"):
        h.run(code, simd=True, setup=vector_setup)


def implicit_strings(h):
    for control in range(256):
        width = 16 if control & 1 else 8
        for length in (0, 1, 128 // width - 1, 128 // width):
            for memory in (False, True):
                def setup(slots, regions, address):
                    vector_setup(slots, regions, address)
                    values = [RNG.getrandbits(width) | 1 for _ in range(128 // width)]
                    if length < len(values): values[length] = 0
                    slots["xmm0"] = sum(value << (i * width) for i, value in enumerate(values))
                    if length % 2: values = list(reversed(values))
                    slots["xmm1"] = sum(value << (i * width) for i, value in enumerate(values))
                    if regions:
                        slots["rbx"] = DATA + 33
                        regions[0][1][33:49] = slots["xmm1"].to_bytes(16, "little")
                h.run("660f3a63" + ("03" if memory else "c1") + f"{control:02x}", simd=True, memory=memory, setup=setup)
    h.fault("660f3a630300", 15)


def hardware_case(h, oracle, code, slots, regions=None, address=0x10000):
    h.forms.setdefault(code, address)
    initial = {name: RNG.getrandbits(64) for name in GPRS}
    initial.update({name: RNG.getrandbits(1) for name in FLAGS})
    initial.update({f"xmm{i}": RNG.getrandbits(128) for i in range(16)})
    initial.update({f"ymm{i}_hi": RNG.getrandbits(128) for i in range(16)})
    initial.update(mxcsr=0x1f80)
    initial.update(slots)
    expected = dict(initial)
    regions = regions or []
    result = oracle.run(code, vectors=[initial[f"xmm{i}"] | (initial[f"ymm{i}_hi"] << 128) for i in range(16)],
                        **{name: initial[name] for name in ("rax", "rbx", "rcx", "mxcsr")},
                        eflags=sum(initial[name] << bit for name, bit in FLAGS.items()),
                        memory=regions[0][1] if regions else None, memory_offset=initial["rbx"] - DATA if regions else 0)
    for i in range(16): expected.update({f"xmm{i}": result[f"ymm{i}"] & ((1 << 128) - 1), f"ymm{i}_hi": result[f"ymm{i}"] >> 128})
    for name in ("rax", "rbx", "rcx", "mxcsr"): expected[name] = result[name]
    for name, bit in FLAGS.items(): expected[name] = (result["eflags"] >> bit) & 1
    response = h.request(bytes.fromhex(code), address, initial, regions)
    h.last_response = response
    assert response["supported"] and response["Outcome"] == "Normal", (code, response)
    actual = {name: int(value, 16) for name, value in response["slots"].items()}
    assert actual == expected, (code, {name: (hex(actual[name]), hex(value)) for name, value in expected.items() if actual[name] != value}, initial)
    assert int(response["next"], 16) == address + len(bytes.fromhex(code))
    if regions:
        assert response["support"] == "NormalPathOnly"
        actual_memory = bytes(response["memory"][f"0x{DATA+i:X}"] for i in range(128))
        assert actual_memory == result["memory"], (code, "memory")
    else: assert not response["Accesses"]
    h.checks += 1
    h.avx_native_checks += 1


def floating_hardware(h, oracle):
    checks = 0
    for code in sorted(FLOAT_CODES | ROUND_CODES):
        raw = bytes.fromhex(code)
        width = (64 if raw[3] & 1 else 32) if code in ROUND_CODES else (64 if (raw[2] & 3) in (1, 3) else 32)
        edges = FP_EDGES[width]
        for index, control in enumerate(FP_CONTROLS):
            for case in range(6):
                values = [edges[(case * 3 + i + index) % len(edges)] for i in range(256 // width)]
                vectors = [sum(values[(i + vector) % len(values)] << (i * width) for i in range(len(values))) for vector in range(3)]
                slots = {f"xmm{i}": vectors[i] & ((1 << 128) - 1) for i in range(3)}
                slots.update({f"ymm{i}_hi": vectors[i] >> 128 for i in range(3)})
                slots["mxcsr"] = control | RNG.getrandbits(6)
                hardware_case(h, oracle, code, slots)
                checks += 1
    for control in range(256):
        for _ in range(4):
            hardware_case(h, oracle, "660f3a63c1" + f"{control:02x}", {})
            checks += 1
    h.guard_stop(vex(0x5e, pp=2, source=1, rm=2), {"xmm1": 0x3f800000, "xmm2": 0, "mxcsr": 0x1d80})
    # Only YMM's upper half raises #XM; no low-half result or MXCSR update may commit.
    h.guard_stop(vex(0x5e, pp=0, vl=256, source=1, rm=2),
                 {"xmm1": 0x3f800000, "xmm2": 0x3f800000, "ymm1_hi": 0x3f800000, "ymm2_hi": 0, "mxcsr": 0x1d80})
    for code in sorted(FLOAT_MEMORY_CODES | FMA_EXTRA_CODES):
        raw = bytes.fromhex(code)
        memory = raw[4] < 0xc0
        for _ in range(4):
            h.run(code, simd=True, memory=memory, setup=lambda s, r, a: s.update(rbx=DATA + 33) if r else None)
            checks += 1
        if memory:
            instruction = next(h.decoder.disasm(raw, 0x10000))
            width = next(operand.size for operand in instruction.operands if operand.type == CS_OP_MEM)
            h.fault(code, width - 1)
    for code in sorted(LEGACY_HIGH_CODES):
        for _ in range(16):
            hardware_case(h, oracle, code, {})
            checks += 1
    return checks


def halt_boundaries(h):
    for code in ("f4", "66f4", "67f4", "40f4"):
        slots = {name: RNG.getrandbits(64) for name in GPRS}
        response = h.request(bytes.fromhex(code), 0x10000, slots, [])
        assert response["supported"] and response["support"] == "ExceptionBoundaryOnly"
        assert response["Outcome"] == "Trap" and response["Event"] == "x64.#GP(0)" and response["resumeAddress"] == "0x10000"
        assert not response["Accesses"] and {k: int(v, 16) for k, v in response["slots"].items()} == slots
        h.checks += 1


def fused_hardware(h, oracle):
    checks = 0
    for code in sorted(FMA_CODES):
        raw = bytes.fromhex(code)
        width = 64 if raw[2] & 128 else 32
        exponent, fraction = (11, 52) if width == 64 else (8, 23)
        sign = 1 << (width - 1)
        infinity = ((1 << exponent) - 1) << fraction
        quiet = infinity | (1 << (fraction - 1))
        one = ((1 << (exponent - 1)) - 1) << fraction
        max_value = infinity - 1
        specials = (0, sign, 1, 1 << fraction, one, one | sign, infinity, infinity | sign,
                    quiet | 1, quiet | sign | 2, infinity | 3)
        fixtures = [(a, b, c) for a in specials[-3:] for b in specials[-3:] for c in specials[-3:]]
        fixtures += [(0, infinity, quiet | 3), (0, infinity, one), (0, infinity, infinity | 3),
                     (1, infinity, quiet | 3), (quiet | 1, 1, one), (1, infinity, one),
                     (max_value, one + (1 << fraction), max_value | sign),
                     (1, 1, one), (1, one, 0), (1 << fraction, one - 1, 0),
                     (one + 1, one - 1, one | sign), (one, one, one | sign),
                     (0, one, 0), (sign, one, 0), (0, one, sign), (sign, one, sign)]
        order = raw[3] >> 4
        for control in FP_CONTROLS:
            for index in range(len(fixtures)):
                canonical = [fixtures[(index + lane) % len(fixtures)] for lane in range(256 // width)]
                source_values = [(a, c, b) if order == 9 else (b, a, c) if order == 10 else (c, a, b) for a, b, c in canonical]
                vectors = [sum(row[operand] << (lane * width) for lane, row in enumerate(source_values)) for operand in range(3)]
                slots = {f"xmm{i}": vectors[i] & ((1 << 128) - 1) for i in range(3)}
                slots.update({f"ymm{i}_hi": vectors[i] >> 128 for i in range(3)})
                slots["mxcsr"] = control | RNG.getrandbits(6)
                hardware_case(h, oracle, code, slots)
                checks += 1
    h.guard_stop(vex(0x99, opcode_map=2, source=1, rm=2), {"xmm0": 0, "xmm1": 0, "xmm2": 0x7f800000, "mxcsr": 0x1f00})
    return checks


def masked_memory(h, oracle):
    checks = 0
    for code in sorted(MASK_CODES):
        raw = bytes.fromhex(code)
        width, vl = (64 if raw[2] & 128 else 32), (256 if raw[2] & 4 else 128)
        source = 15 - ((raw[2] >> 3) & 15)
        count, store = vl // width, raw[3] == 0x8e
        for pattern in range(1 << count):
            mask = sum((((pattern >> lane) & 1) << (width - 1) | RNG.getrandbits(width - 1)) << (lane * width) for lane in range(count))
            slots = {f"xmm{source}": mask & ((1 << 128) - 1), f"ymm{source}_hi": mask >> 128, "rbx": DATA + 33}
            hardware_case(h, oracle, code, slots, [(DATA, RNG.randbytes(128))])
            expected = [f"{'Store' if store else 'Load'}:0x{DATA+33+lane*width//8:X}:{width//8}" for lane in range(count) if pattern & (1 << lane)]
            assert h.last_response["Accesses"] == expected, (code, pattern, h.last_response["Accesses"], expected)
            checks += 1
        # Empty mask suppresses even noncanonical addresses and preserves memory.
        initial = {f"xmm{i}": RNG.getrandbits(128) for i in range(16)}
        initial.update({f"ymm{i}_hi": RNG.getrandbits(128) for i in range(16)})
        initial.update({f"xmm{source}": 0, f"ymm{source}_hi": 0, "rbx": 0x800000000000})
        result = h.request(bytes.fromhex(code), 0x10000, initial, [])
        assert result["supported"] and result["Outcome"] == "Normal" and not result["Accesses"] and not result["events"]
        expected_slots = dict(initial)
        if not store: expected_slots.update(xmm0=0, ymm0_hi=0)
        assert {k: int(v, 16) for k, v in result["slots"].items()} == expected_slots
        h.checks += 1
        h.guard_stop(code, {"rbx": 0x800000000000, f"xmm{source}": 1 << (width - 1), f"ymm{source}_hi": 0})
        # Only lane 0 is mapped; inactive following lanes must not be touched.
        initial.update({"rbx": DATA, f"xmm{source}": 1 << (width - 1), f"ymm{source}_hi": 0})
        result = h.request(bytes.fromhex(code), 0x10000, initial, [(DATA, RNG.randbytes(width // 8))])
        assert result["Outcome"] == "Normal" and len(result["Accesses"]) == 1, (code, result)
        h.checks += 1
        # An active missing lane stops without committing a load destination.
        initial.update({f"xmm{source}": 1 << (width * 2 - 1)})
        result = h.request(bytes.fromhex(code), 0x10000, initial, [(DATA, RNG.randbytes(width // 8))])
        assert result["Outcome"] == "UnmodeledFaultStop" and {k: int(v, 16) for k, v in result["slots"].items()} == initial
        h.fault_stops += 1
    return checks


def effect_contracts(h):
    for code, hint in (("0f1803", 0), ("0f180b", 1), ("0f1813", 2), ("0f181b", 3), ("0f0d0b", 8)):
        for address in (DATA, 0x800000000000):
            slots = {"rbx": address, "rax": RNG.getrandbits(64), "cf": 1}
            result = h.request(bytes.fromhex(code), 0x10000, slots, [])
            assert result["supported"] and result["support"] == "NormalPathOnly" and result["Outcome"] == "Normal"
            assert not result["Accesses"] and {k: int(v, 16) for k, v in result["slots"].items()} == slots
            assert len(result["events"]) == 1
            event = result["events"][0]
            assert event["Kind"] == "Prefetch" and event["Address"] == address and event["Option"] == hint
            h.checks += 1
    for code, kind, access in (("0faef8", 3, 2), ("0faee8", 4, 1), ("0faef0", 5, 0)):
        slots = {"rax": RNG.getrandbits(64), "cf": 1}
        result = h.request(bytes.fromhex(code), 0x10000, slots, [])
        assert result["supported"] and result["support"] == "NormalPathOnly" and result["Outcome"] == "Normal"
        assert not result["Accesses"] and {k: int(v, 16) for k, v in result["slots"].items()} == slots
        assert len(result["events"]) == 1 and result["events"][0]["Kind"] == "Barrier"
        assert result["events"][0]["Barrier"] == {"Kind": kind, "Domain": 0, "Access": access, "Option": 0}
        h.checks += 1


def main():
    with subprocess.Popen(["dotnet", sys.argv[1], "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, encoding="utf-8", bufsize=1) as server:
        oracle = NativeAvxOracle()
        h = NativeVectorHarness(server, oracle)
        vectors(h)
        implicit_strings(h)
        floating_hardware(h, oracle)
        fma_checks = fused_hardware(h, oracle)
        masked_memory(h, oracle)
        oracle.close()
        halt_boundaries(h)
        effect_contracts(h)
        server.stdin.close()
        assert server.wait() == 0
        print(json.dumps({"x64_avx_checks": h.checks, "forms": len(h.forms), "fault_stops": h.fault_stops, "native_checks": h.avx_native_checks, "fma_checks": fma_checks,
                          "pcmp_unicorn_differences": h.pcmp_unicorn_differences,
                          "scope": "synthetic MIR vs native AVX integer/FP/MXCSR/fixed-buffer memory; PCMPISTRI also vs Unicorn; Capstone memory widths; HLT SDM boundary, no host HLT or game execution"}, indent=2))


if __name__ == "__main__":
    main()
