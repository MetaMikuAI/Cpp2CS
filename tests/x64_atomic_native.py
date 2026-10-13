"""Windows x64 锁定合成指令硬件对照，固定指令集和自有内存。"""
import ctypes


def atomic_codes():
    forms = []
    for width in (8, 16, 32, 64):
        size = "66" if width == 16 else "48" if width == 64 else ""
        for name, opcode in (("add", 0x00), ("or", 0x08), ("adc", 0x10), ("sbb", 0x18), ("and", 0x20), ("sub", 0x28), ("xor", 0x30)):
            forms.append(("f0" + size + f"{opcode + (width != 8):02x}0f", width, "logical" if name in ("and", "or", "xor") else "plain", name))
        for name, group in (("inc", 0), ("dec", 1), ("not", 2), ("neg", 3)):
            opcode = (0xfe if group < 2 else 0xf6) + (width != 8)
            forms.append(("f0" + size + f"{opcode:02x}{(group << 3) | 7:02x}", width, "plain", name))
        for name, opcode in (("xadd", 0xc0), ("cmpxchg", 0xb0)):
            forms.append(("f0" + size + f"0f{opcode + (width != 8):02x}0f", width, "plain", name))
        for lock in ("", "f0"):
            forms.append((lock + size + ("860f" if width == 8 else "870f"), width, "plain", "xchg"))
        for group, name in ((0, "add"), (1, "or"), (2, "adc"), (3, "sbb"), (4, "and"), (5, "sub"), (6, "xor")):
            forms.append(("f0" + size + ("80" if width == 8 else "83") + f"{(group << 3) | 7:02x}ff", width,
                          "logical" if name in ("and", "or", "xor") else "plain", name + "_immediate"))
        if width != 8:
            for name, opcode, group in (("bts", 0xab, 5), ("btr", 0xb3, 6), ("btc", 0xbb, 7)):
                forms.append(("f0" + size + f"0f{opcode:02x}0f", width, "bittest", name))
                for immediate in (0, width - 1, width, 255):
                    forms.append(("f0" + size + f"0fba{(group << 3) | 7:02x}{immediate:02x}", width, "bittest", name + "_immediate"))
    forms += [("f00fc70f", 64, "plain", "cmpxchg8b"), ("f0480fc70f", 128, "plain", "cmpxchg16b")]
    return tuple(forms)


FORMS = atomic_codes()
ALLOWED = frozenset(code for code, *_ in FORMS)


class NativeAtomicOracle:
    def __init__(self):
        self.kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        self.kernel.IsProcessorFeaturePresent.argtypes = (ctypes.c_ulong,)
        self.kernel.IsProcessorFeaturePresent.restype = ctypes.c_int
        if not self.kernel.IsProcessorFeaturePresent(14): raise RuntimeError("CMPXCHG16B hardware support required")
        self.kernel.VirtualAlloc.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong, ctypes.c_ulong)
        self.kernel.VirtualAlloc.restype = ctypes.c_void_p
        self.kernel.VirtualProtect.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong, ctypes.POINTER(ctypes.c_ulong))
        self.kernel.VirtualProtect.restype = ctypes.c_int
        self.kernel.VirtualFree.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong)
        self.kernel.VirtualFree.restype = ctypes.c_int
        self.cache = {}

    def helper(self, code_hex):
        assert code_hex in ALLOWED
        if code_hex in self.cache: return self.cache[code_hex][1]
        code = bytes.fromhex("9c5356574989ca")  # preserve flags, RBX/RSI/RDI; R10 = context
        code += bytes.fromhex("498b02498b5a08498b4a10498b5218498b7220498b7a28")
        code += bytes.fromhex("41ff72309d")  # load only caller-provided arithmetic flags
        code += bytes.fromhex(code_hex)
        code += bytes.fromhex("49890249895a0849894a10498952189c415b4d895a30")
        code += bytes.fromhex("5f5e5b9dc3")
        address = self.kernel.VirtualAlloc(None, len(code), 0x3000, 0x04)
        if not address: raise ctypes.WinError(ctypes.get_last_error())
        ctypes.memmove(address, code, len(code))
        old = ctypes.c_ulong()
        if not self.kernel.VirtualProtect(address, len(code), 0x20, ctypes.byref(old)):
            raise ctypes.WinError(ctypes.get_last_error())
        function = ctypes.WINFUNCTYPE(None, ctypes.c_void_p)(address)
        self.cache[code_hex] = (address, function)
        return function

    def run(self, code_hex, slots, data):
        storage = ctypes.create_string_buffer(len(data) + 31)
        base = (ctypes.addressof(storage) + 15) & ~15
        ctypes.memmove(base, bytes(data), len(data))
        values = (ctypes.c_uint64 * 7)(slots["rax"], slots["rbx"], slots["rcx"], slots["rdx"], slots["rsi"], base + 256,
                                       2 | sum(slots[name] << bit for name, bit in {"cf": 0, "pf": 2, "af": 4, "zf": 6, "sf": 7, "of": 11}.items()))
        self.helper(code_hex)(ctypes.addressof(values))
        return {name: values[index] for index, name in enumerate(("rax", "rbx", "rcx", "rdx"))}, values[6], ctypes.string_at(base, len(data))

    def close(self):
        for address, _function in self.cache.values():
            if not self.kernel.VirtualFree(address, 0, 0x8000): raise ctypes.WinError(ctypes.get_last_error())
        self.cache.clear()
