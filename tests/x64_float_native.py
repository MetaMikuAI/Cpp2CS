"""Windows x64 硬件对照：只执行白名单内的合成 SSE 指令，恢复宿主状态。"""

import ctypes


def _allowed_codes():
    codes = set()
    for prefix in ("", "66", "f3", "f2"):
        for opcode in ("58", "59", "5c", "5e", "5d", "5f", "51"):
            codes.add(prefix + "0f" + opcode + "c1")
        for predicate in (*range(8), 255):
            codes.add(prefix + "0fc2c1" + f"{predicate:02x}")
    for prefix in ("", "66"):
        for opcode in ("2e", "2f"):
            codes.add(prefix + "0f" + opcode + "c1")
    for prefix in ("f3", "f2"):
        for rex in ("", "48"):
            codes.add(prefix + rex + "0f2ac3")
            for opcode in ("2c", "2d"):
                codes.add(prefix + rex + "0f" + opcode + "c1")
    codes.update(("f30f5ac1", "f20f5ac1", "0f5ac1", "660f5ac1", "0f5bc1",
                  "f30f5bc1", "660f5bc1", "f30fe6c1", "f20fe6c1", "660fe6c1"))
    return frozenset(codes)


ALLOWED_CODES = _allowed_codes()


class NativeFloatOracle:
    def __init__(self):
        self._kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        self._kernel.VirtualAlloc.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong, ctypes.c_ulong)
        self._kernel.VirtualAlloc.restype = ctypes.c_void_p
        self._kernel.VirtualProtect.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong,
                                               ctypes.POINTER(ctypes.c_ulong))
        self._kernel.VirtualProtect.restype = ctypes.c_int
        self._kernel.VirtualFree.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong)
        self._kernel.VirtualFree.restype = ctypes.c_int
        self._kernel.FlushInstructionCache.argtypes = (ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t)
        self._kernel.FlushInstructionCache.restype = ctypes.c_int
        self._functions = {}
        self._buffer = (ctypes.c_uint64 * 7)()

    def _function(self, code_hex):
        if code_hex not in ALLOWED_CODES:
            raise ValueError(f"instruction is not in the synthetic SSE whitelist: {code_hex}")
        if code_hex in self._functions:
            return self._functions[code_hex][1]
        # RCX points to {xmm0[16],xmm1[16],rax[8],rbx[8],mxcsr[4],eflags[4]}.
        # Preserve RBX, RFLAGS, MXCSR; XMM0/1, RAX, R10/11 are ABI-volatile.
        before = bytes.fromhex(
            "53 9c 4883ec10 4989ca 0fae1c24 410fae5230 "
            "f3410f6f02 f3410f6f4a10 498b4220 498b5a28 458b5a34 4153 9d")
        after = bytes.fromhex(
            "410fae5a30 9c 415b 45895a34 f3410f7f02 f3410f7f4a10 "
            "49894220 49895a28 0fae1424 4883c410 9d 5b c3")
        code = before + bytes.fromhex(code_hex) + after
        address = self._kernel.VirtualAlloc(None, len(code), 0x3000, 0x04)
        if not address:
            raise OSError(ctypes.get_last_error(), "VirtualAlloc")
        ctypes.memmove(address, code, len(code))
        old_protection = ctypes.c_ulong()
        if not self._kernel.VirtualProtect(address, len(code), 0x20, ctypes.byref(old_protection)):
            raise OSError(ctypes.get_last_error(), "VirtualProtect")
        if not self._kernel.FlushInstructionCache(ctypes.c_void_p(-1), address, len(code)):
            raise OSError(ctypes.get_last_error(), "FlushInstructionCache")
        function = ctypes.WINFUNCTYPE(None, ctypes.POINTER(ctypes.c_uint64))(address)
        self._functions[code_hex] = (address, function)
        return function

    def run(self, code_hex, *, xmm0=0, xmm1=0, rax=0, rbx=0, mxcsr=0x1F80, eflags=0x202):
        code_hex = code_hex.lower().replace(" ", "")
        function = self._function(code_hex)
        mask64 = (1 << 64) - 1
        self._buffer[0] = xmm0 & mask64
        self._buffer[1] = (xmm0 >> 64) & mask64
        self._buffer[2] = xmm1 & mask64
        self._buffer[3] = (xmm1 >> 64) & mask64
        self._buffer[4] = rax & mask64
        self._buffer[5] = rbx & mask64
        # Reserved MXCSR bits remain zero; all exceptions are masked in the host test.
        self._buffer[6] = ((mxcsr & 0xFFFF) | 0x1F80) | (((eflags & 0xCD5) | 0x202) << 32)
        function(self._buffer)
        return {"xmm0": self._buffer[0] | (self._buffer[1] << 64),
                "xmm1": self._buffer[2] | (self._buffer[3] << 64),
                "rax": self._buffer[4], "rbx": self._buffer[5],
                "mxcsr": self._buffer[6] & 0xFFFFFFFF,
                "eflags": self._buffer[6] >> 32}

    def close(self):
        for address, _function in self._functions.values():
            if not self._kernel.VirtualFree(address, 0, 0x8000):
                raise OSError(ctypes.get_last_error(), "VirtualFree")
        self._functions.clear()

    def __enter__(self):
        return self

    def __exit__(self, _type, _value, _traceback):
        self.close()


if __name__ == "__main__":
    with NativeFloatOracle() as oracle:
        third = oracle.run("f30f5ec1", xmm0=0x3F800000, xmm1=0x40400000)
        assert third["xmm0"] == 0x3EAAAAAB and third["mxcsr"] == 0x1FA0, third
        tiny = oracle.run("f30f59c1", xmm0=0x00800000, xmm1=0x3F000000, mxcsr=0x9F80)
        assert tiny["xmm0"] == 0 and tiny["mxcsr"] == 0x9FB0, tiny
        quiet = oracle.run("f30f5dc1", xmm0=0x7FC00001, xmm1=0x3F800000)
        assert quiet["xmm0"] == 0x3F800000 and quiet["mxcsr"] == 0x1F81, quiet
        print("x64 native SSE oracle: 3 calibration cases passed")
