"""Windows x64 合成 AVX/SSE4.2 硬件对照；只执行固定寄存器指令白名单。"""
import ctypes


def vex(opcode, *, pp=1, vl=128, source=0, dest=0, rm=1, opcode_map=1, w=0, memory=False, immediate=None):
    prefix = bytes((0xc4, ((dest < 8) << 7) | 0x40 | ((rm < 8) << 5) | opcode_map,
                    (w << 7) | ((15 - source) << 3) | ((vl == 256) << 2) | pp))
    modrm = ((0 if memory else 3) << 6) | ((dest & 7) << 3) | (rm & 7)
    return (prefix + bytes((opcode, modrm)) + (b"" if immediate is None else bytes((immediate,)))).hex()


def float_codes():
    result = set()
    for pp in range(4):
        scalar = pp >= 2
        for vl in ((128,) if scalar else (128, 256)):
            for opcode in (0x58, 0x59, 0x5c, 0x5e, 0x5d, 0x5f, 0x51):
                result.add(vex(opcode, pp=pp, vl=vl, source=1 if scalar or opcode != 0x51 else 0, rm=2))
            for predicate in range(32):
                result.add(vex(0xc2, pp=pp, vl=vl, source=1, rm=2, immediate=predicate))
    for pp in (0, 1):
        for opcode in (0x2e, 0x2f): result.add(vex(opcode, pp=pp, rm=1))
    for pp in (2, 3):
        for w in (0, 1):
            result.add(vex(0x2a, pp=pp, w=w, source=1, rm=3))
            for opcode in (0x2c, 0x2d): result.add(vex(opcode, pp=pp, w=w, rm=1))
        result.add(vex(0x5a, pp=pp, source=1, rm=2))
    for pp, opcode in ((0, 0x5a), (1, 0x5a), (0, 0x5b), (1, 0x5b), (2, 0x5b), (1, 0xe6), (2, 0xe6), (3, 0xe6)):
        for vl in (128, 256): result.add(vex(opcode, pp=pp, vl=vl))
    return frozenset(result)


FLOAT_CODES = float_codes()
FMA_CODES = frozenset(vex(order + kind + scalar, opcode_map=2, w=w, vl=vl, source=1, rm=2)
                     for order in (0x90, 0xa0, 0xb0) for kind in (8, 10, 12, 14) for w in (0, 1)
                     for scalar in (0, 1) for vl in ((128,) if scalar else (128, 256)))
FMA_EXTRA_CODES = frozenset(vex(raw[3], opcode_map=2, w=raw[2] >> 7, vl=256 if raw[2] & 4 else 128,
                              dest=dest, source=source, rm=rm, memory=memory)
                            for raw in map(bytes.fromhex, FMA_CODES)
                            for dest, source, rm, memory in ((0, 0, 1, False), (0, 1, 0, False), (0, 0, 0, False), (15, 9, 15, False), (0, 1, 3, True)))
FLOAT_MEMORY_CODES = frozenset((raw[:4] + b"\x03" + raw[5:]).hex() for raw in map(bytes.fromhex, FLOAT_CODES))
ROUND_CODES = frozenset(vex(opcode, opcode_map=3, vl=vl, source=1 if opcode >= 10 else 0, rm=2, immediate=control)
                       for opcode in (8, 9, 10, 11) for vl in ((128,) if opcode >= 10 else (128, 256)) for control in range(16))
LEGACY_HIGH_CODES = frozenset(("0f10c1", "0f14c1", "660f60c1", "660fd5c1", "f30f10c1", "f20f10c1"))
MASK_CODES = frozenset(vex(opcode, opcode_map=2, w=w, vl=vl, source=source, rm=3, memory=True)
                       for opcode in (0x8c, 0x8e) for w in (0, 1) for vl in (128, 256) for source in (0, 1))


def vector_codes():
    codes = set()
    def add(opcode, **options): codes.add(vex(opcode, **options))
    for vl in (128, 256):
        for opcode, pp in ((0xe7, 1), (0x2b, 0), (0x2b, 1)):
            add(opcode, pp=pp, vl=vl, rm=3, memory=True)
        for opcode, pp in ((0x10, 0), (0x11, 0), (0x28, 0), (0x29, 0), (0x10, 1), (0x11, 1),
                           (0x28, 1), (0x29, 1), (0x6f, 1), (0x7f, 1), (0x6f, 2), (0x7f, 2)):
            for dest, rm in ((0, 1), (0, 0), (15, 9)): add(opcode, pp=pp, vl=vl, dest=dest, rm=rm)
            add(opcode, pp=pp, vl=vl, rm=3, memory=True)
        binary = [(1, pp, opcode) for pp, opcodes in ((0, (0x54, 0x55, 0x56, 0x57)),
                  (1, (0x54, 0x55, 0x56, 0x57, 0xdb, 0xdf, 0xeb, 0xef,
                       0xfc, 0xfd, 0xfe, 0xd4, 0xf8, 0xf9, 0xfa, 0xfb, 0xec, 0xed, 0xdc, 0xdd,
                       0xe8, 0xe9, 0xd8, 0xd9, 0x74, 0x75, 0x76, 0x64, 0x65, 0x66, 0xda, 0xde, 0xea, 0xee, 0xd5, 0xe5, 0xe4))) for opcode in opcodes]
        binary += [(2, 1, opcode) for opcode in (0x29, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f, 0x40, 0x00)]
        binary += [(1, pp, opcode) for pp, opcodes in ((0, (0x14, 0x15)), (1, (0x14, 0x15, 0x60, 0x61, 0x62, 0x68, 0x69, 0x6a, 0x6c, 0x6d))) for opcode in opcodes]
        for opcode_map, pp, opcode in binary:
            for dest, first, second in ((0, 1, 2), (0, 0, 1), (0, 1, 0), (15, 9, 15)):
                add(opcode, pp=pp, vl=vl, source=first, dest=dest, rm=second, opcode_map=opcode_map)
            add(opcode, pp=pp, vl=vl, source=1, rm=3, memory=True, opcode_map=opcode_map)
        for opcode in (0xf1, 0xf2, 0xf3, 0xd1, 0xd2, 0xd3, 0xe1, 0xe2): add(opcode, vl=vl, source=1, rm=2)
        for opcode, group in ((0x71, 6), (0x72, 6), (0x73, 6), (0x71, 2), (0x72, 2), (0x73, 2), (0x71, 4), (0x72, 4), (0x73, 3), (0x73, 7)):
            for count in (0, 1, 15, 16, 31, 32, 63, 64, 255): add(opcode, vl=vl, dest=group, immediate=count)
        for opcode, w in ((0x45, 0), (0x45, 1), (0x46, 0), (0x47, 0), (0x47, 1)): add(opcode, vl=vl, opcode_map=2, w=w, source=1, rm=2)
        for opcode, pp, two in ((0xc6, 0, True), (0xc6, 1, True), (0x70, 1, False), (0x70, 2, False), (0x70, 3, False)):
            for control in range(256): add(opcode, pp=pp, vl=vl, source=1 if two else 0, rm=2, immediate=control)
        for first in (0x20, 0x30):
            for delta in range(6):
                add(first + delta, vl=vl, opcode_map=2)
                add(first + delta, vl=vl, opcode_map=2, rm=3, memory=True)
        for opcode, pp in ((0x50, 0), (0x50, 1), (0xd7, 1)): add(opcode, pp=pp, vl=vl)
    for pp in (2, 3):
        for opcode in (0x10, 0x11):
            for first, second in ((1, 2), (0, 1), (1, 0)): add(opcode, pp=pp, source=first, rm=second)
            add(opcode, pp=pp, rm=3, memory=True)
    for w in (0, 1):
        for opcode in (0x6e, 0x7e):
            add(opcode, w=w, rm=3)
            add(opcode, w=w, rm=3, memory=True)
    for opcode, pp in ((0x7e, 2), (0xd6, 1)):
        add(opcode, pp=pp)
        add(opcode, pp=pp, rm=3, memory=True)
    for opcode in (0x18, 0x38):
        for control in (0, 1, 2, 127, 255):
            add(opcode, vl=256, opcode_map=3, source=1, rm=2, immediate=control)
            add(opcode + 1, vl=256, opcode_map=3, immediate=control)
    return codes | {"c5f877", "c5fc77", "c5f810c1", "c5fa10c1", "c5f857c1"}


VECTOR_CODES = frozenset(vector_codes())
ALLOWED_CODES = FLOAT_CODES | FMA_CODES | FMA_EXTRA_CODES | FLOAT_MEMORY_CODES | ROUND_CODES | LEGACY_HIGH_CODES | MASK_CODES | VECTOR_CODES | frozenset("660f3a63" + modrm + f"{control:02x}" for control in range(256) for modrm in ("c1", "03"))


def vector_memory(register, base, offset, store):
    # VMOVDQU YMMn,[R10+disp32] or [RSP+disp32]; fixed helper addressing only.
    prefix = bytes((0xc4, ((register < 8) << 7) | 0x40 | ((base < 8) << 5) | 1, 0x7e))
    return prefix + bytes((0x7f if store else 0x6f, 0x80 | ((register & 7) << 3) | (base & 7))) + (b"\x24" if base == 4 else b"") + offset.to_bytes(4, "little")


class NativeAvxOracle:
    def __init__(self):
        self.kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        self.kernel.IsProcessorFeaturePresent.argtypes = (ctypes.c_ulong,)
        self.kernel.IsProcessorFeaturePresent.restype = ctypes.c_int
        if not all(self.kernel.IsProcessorFeaturePresent(feature) for feature in (38, 39, 40)):
            raise RuntimeError("native oracle requires OS-enabled AVX/AVX2 and SSE4.2")
        self.kernel.VirtualAlloc.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong, ctypes.c_ulong)
        self.kernel.VirtualAlloc.restype = ctypes.c_void_p
        self.kernel.VirtualProtect.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong, ctypes.POINTER(ctypes.c_ulong))
        self.kernel.VirtualProtect.restype = ctypes.c_int
        self.kernel.VirtualFree.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong)
        self.kernel.VirtualFree.restype = ctypes.c_int
        self.kernel.FlushInstructionCache.argtypes = (ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t)
        self.kernel.FlushInstructionCache.restype = ctypes.c_int
        self.functions = {}
        self.backing = ctypes.create_string_buffer(704 + 31)
        self.buffer = (ctypes.c_uint64 * 88).from_buffer(self.backing, -ctypes.addressof(self.backing) % 32)
        # CPUID.1:ECX.FMA is independent of the AVX2 feature bit.
        self.functions["cpuid_fma"] = self.allocate(bytes.fromhex("53 b801000000 0fa2 89c8 c1e80c 83e001 5b c3"), ctypes.WINFUNCTYPE(ctypes.c_uint32))
        if self.functions["cpuid_fma"][1]() == 0:
            self.close()
            raise RuntimeError("native oracle requires FMA")

    def function(self, code):
        if code not in ALLOWED_CODES: raise ValueError(f"not a whitelisted synthetic instruction: {code}")
        if code in self.functions: return self.functions[code][1]
        # R10: YMM0..15[512], RAX/RBX/RCX[24], MXCSR/flags[8], padding[32], data[128].
        # Restore all nonvolatile YMM registers, RBX, MXCSR and flags.
        before = bytes.fromhex("53 9c 4881ec58010000 4989ca 0fae1c24")
        before += b"".join(vector_memory(i, 4, 16 + (i - 6) * 32, True) for i in range(6, 16))
        before += bytes.fromhex("410fae9218020000")
        before += b"".join(vector_memory(i, 10, i * 32, False) for i in range(16))
        before += bytes.fromhex("498b8200020000 498b9a08020000 498b8a10020000 458b9a1c020000 4153 9d")
        # This harness fence completes NT writes before Python reads the buffer.
        after = bytes.fromhex("0faef8 410fae9a18020000 9c 415b 45899a1c020000")
        after += b"".join(vector_memory(i, 10, i * 32, True) for i in range(16))
        after += bytes.fromhex("49898200020000 49899a08020000 49898a10020000 0fae1424")
        after += b"".join(vector_memory(i, 4, 16 + (i - 6) * 32, False) for i in range(6, 16))
        after += bytes.fromhex("4881c458010000 9d 5b c3")
        machine_code = before + bytes.fromhex(code) + after
        self.functions[code] = self.allocate(machine_code, ctypes.WINFUNCTYPE(None, ctypes.POINTER(ctypes.c_uint64)))
        return self.functions[code][1]

    def allocate(self, machine_code, prototype):
        address = self.kernel.VirtualAlloc(None, len(machine_code), 0x3000, 0x04)
        if not address: raise OSError(ctypes.get_last_error(), "VirtualAlloc")
        ctypes.memmove(address, machine_code, len(machine_code))
        old = ctypes.c_ulong()
        if not self.kernel.VirtualProtect(address, len(machine_code), 0x20, ctypes.byref(old)):
            raise OSError(ctypes.get_last_error(), "VirtualProtect")
        if not self.kernel.FlushInstructionCache(ctypes.c_void_p(-1), address, len(machine_code)):
            raise OSError(ctypes.get_last_error(), "FlushInstructionCache")
        return address, prototype(address)

    def run(self, code, *, ymm0=0, ymm1=0, ymm2=0, vectors=None, rax=0, rbx=0, rcx=0, mxcsr=0x1f80, eflags=0x202, memory=None, memory_offset=0):
        vectors = vectors if vectors is not None else [ymm0, ymm1, ymm2] + [0] * 13
        for index, vector in enumerate(vectors):
            for word in range(4): self.buffer[index * 4 + word] = (vector >> (word * 64)) & ((1 << 64) - 1)
        if memory is not None:
            assert len(memory) == 128 and 0 <= memory_offset <= 96
            ctypes.memmove(ctypes.addressof(self.buffer) + 576, bytes(memory), 128)
        self.buffer[64], self.buffer[65], self.buffer[66] = rax, rbx if memory is None else ctypes.addressof(self.buffer) + 576 + memory_offset, rcx
        self.buffer[67] = ((mxcsr & 0xffff) | 0x1f80) | (((eflags & 0xcd5) | 0x202) << 32)
        self.function(code)(self.buffer)
        result = {f"ymm{index}": sum(self.buffer[index * 4 + word] << (64 * word) for word in range(4)) for index in range(16)}
        result.update(rax=self.buffer[64], rbx=self.buffer[65] if memory is None else rbx, rcx=self.buffer[66], mxcsr=self.buffer[67] & 0xffffffff, eflags=self.buffer[67] >> 32)
        if memory is not None: result["memory"] = ctypes.string_at(ctypes.addressof(self.buffer) + 576, 128)
        return result

    def close(self):
        for address, _ in self.functions.values():
            if not self.kernel.VirtualFree(address, 0, 0x8000): raise OSError(ctypes.get_last_error(), "VirtualFree")
        self.functions.clear()


if __name__ == "__main__":
    oracle = NativeAvxOracle()
    third = oracle.run(vex(0x5e, pp=2, source=1, rm=2), ymm1=0x3f800000, ymm2=0x40400000)
    assert third["ymm0"] == 0x3eaaaaab and third["mxcsr"] == 0x1fa0, third
    match = oracle.run("660f3a63c100", ymm0=0x0041, ymm1=0x4241)
    assert match["rcx"] == 0 and match["eflags"] & 1, match
    oracle.close()
    print("AVX native oracle: 2 calibration checks passed")
