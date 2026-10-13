"""ENTER 的生产 MIR、Unicorn 与 Windows x64 原生合成差分。"""

import ctypes
import json
import random
import subprocess
import sys

from unicorn import Uc, UC_ARCH_X86, UC_MODE_64, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
from unicorn import x86_const as xc

from x64_float_native import NativeFloatOracle


FLAGS = {"cf": 0, "pf": 2, "af": 4, "zf": 6, "sf": 7, "df": 10, "of": 11}
FLAG_MASK = sum(1 << bit for bit in FLAGS.values())
RNG = random.Random(0xC226)
CODE = 0x10000


def enter_code(allocation, nesting, prefix=""):
    assert 0 <= allocation <= 65535 and 0 <= nesting <= 255
    assert prefix in ("", "66", "67", "6766", "48", "6648", "4866")
    return prefix + "c8" + allocation.to_bytes(2, "little").hex() + f"{nesting:02x}"


class NativeEnterOracle(NativeFloatOracle):
    """仅执行固定 ENTER 形式；栈指向本类分配的缓冲区，恢复 RSP/RBP/RFLAGS。"""

    def __init__(self):
        super().__init__()
        self.stack = (ctypes.c_ubyte * 0x24000)()
        self.base = ctypes.addressof(self.stack)
        self.boundary = (self.base + 0x10200) & ~0xffff
        self.context = (ctypes.c_uint64 * 3)()

    def _function(self, code_hex):
        code = bytes.fromhex(code_hex)
        prefix = code[:-4].hex()
        assert prefix in ("", "66", "67", "6766", "48", "6648", "4866") and code[-4] == 0xc8
        if code_hex in self._functions:
            return self._functions[code_hex][1]
        # R10=context, R11=host RSP. All instructions around ENTER preserve flags.
        before = bytes.fromhex("55 9c 4989ca 4989e3 41ff7210 9d 498b22 498b6a08")
        after = bytes.fromhex("498922 49896a08 4c89dc 9c 58 49894210 9d 5d c3")
        machine_code = before + code + after
        address = self._kernel.VirtualAlloc(None, len(machine_code), 0x3000, 0x04)
        if not address:
            raise OSError(ctypes.get_last_error(), "VirtualAlloc")
        ctypes.memmove(address, machine_code, len(machine_code))
        old_protection = ctypes.c_ulong()
        if not self._kernel.VirtualProtect(address, len(machine_code), 0x20, ctypes.byref(old_protection)):
            raise OSError(ctypes.get_last_error(), "VirtualProtect")
        if not self._kernel.FlushInstructionCache(ctypes.c_void_p(-1), address, len(machine_code)):
            raise OSError(ctypes.get_last_error(), "FlushInstructionCache")
        function = ctypes.WINFUNCTYPE(None, ctypes.POINTER(ctypes.c_uint64))(address)
        self._functions[code_hex] = (address, function)
        return function

    def run_enter(self, code_hex, rsp, rbp, memory, flags):
        assert self.base + 0x10000 < rsp < self.base + len(self.stack) - 0x200
        assert self.base + 0x100 < rbp < self.base + len(self.stack) - 0x100
        for address, data in memory:
            assert self.base <= address and address + len(data) <= self.base + len(self.stack)
            ctypes.memmove(address, bytes(data), len(data))
        self.context[:] = (rsp, rbp, (flags & FLAG_MASK) | 0x202)
        self._function(code_hex)(self.context)
        return {"rsp": self.context[0], "rbp": self.context[1], "flags": self.context[2],
                "memory": [ctypes.string_at(address, len(data)) for address, data in memory]}


class StackHarness:
    def __init__(self, server, native):
        self.server, self.native = server, native
        self.machine = Uc(UC_ARCH_X86, UC_MODE_64)
        self.machine.mem_map(CODE, 0x100000)
        low = native.base & ~0xfff
        high = (native.base + len(native.stack) + 0xfff) & ~0xfff
        self.machine.mem_map(low, high - low)
        self.accesses = []
        self.machine.hook_add(UC_HOOK_MEM_READ, lambda _u, _a, where, size, _v, _d: self.accesses.append(f"Load:0x{where:X}:{size}"))
        self.machine.hook_add(UC_HOOK_MEM_WRITE, lambda _u, _a, where, size, _v, _d: self.accesses.append(f"Store:0x{where:X}:{size}"))
        self.forms = {}
        self.checks = 0
        self.native_checks = 0
        self.fault_checks = 0
        self.rejected = 0
        self.unicorn_frame_differences = 0

    def request(self, code, slots, memory, permissions):
        if code not in self.forms:
            self.forms[code] = CODE + len(self.forms) * 16
        request = {"arch": "x64", "bytes": code, "address": hex(self.forms[code]),
                   "slots": {k: hex(v) for k, v in slots.items()},
                   "memory": [{"address": hex(a), "bytes": bytes(d).hex()} for a, d in memory],
                   "writePermissions": permissions, "roundtrip": self.checks % 7 == 0}
        self.server.stdin.write(json.dumps(request) + "\n")
        self.server.stdin.flush()
        line = self.server.stdout.readline()
        assert line, ("CLI exited", self.server.poll(), code)
        return json.loads(line)

    def run(self, allocation, nesting, prefix="", distance=128, rsp=None, rbp=None):
        rsp = self.native.boundary + 0x11000 if rsp is None else rsp
        rbp = rsp + distance if rbp is None else rbp
        code = enter_code(allocation, nesting, prefix)
        width = 2 if prefix in ("66", "6766", "4866") else 8
        level = nesting & 31
        final = rsp - width * (1 if not level else level + 1) - allocation
        spans = sorted([(rsp - 0x180, rsp + 0x40), (rbp - 0x180, rbp + 0x40)])
        if spans[0][1] >= spans[1][0]:
            spans = [(spans[0][0], max(x[1] for x in spans))]
        memory = [(start, RNG.randbytes(end - start)) for start, end in spans]
        flags = RNG.getrandbits(12) & FLAG_MASK
        slots = {"rsp": rsp, "rbp": rbp, **{k: (flags >> bit) & 1 for k, bit in FLAGS.items()}}
        permissions = [{"address": hex(final), "size": 1, "allowed": True}]
        response = self.request(code, slots, memory, permissions)
        assert response["supported"] and response["support"] == "NormalPathOnly", (code, response)
        assert response["Outcome"] == "Normal", (code, response)
        address = self.forms[code]
        self.machine.mem_write(address, bytes.fromhex(code))
        for start, data in memory:
            self.machine.mem_write(start, data)
        self.machine.reg_write(xc.UC_X86_REG_RSP, rsp)
        self.machine.reg_write(xc.UC_X86_REG_RBP, rbp)
        self.machine.reg_write(xc.UC_X86_REG_EFLAGS, flags | 2)
        self.accesses.clear()
        self.machine.emu_start(address, address + len(bytes.fromhex(code)), count=1)
        hardware = self.native.run_enter(code, rsp, rbp, memory, flags)
        actual = {k: int(v, 16) for k, v in response["slots"].items()}
        for name in ("rsp", "rbp"):
            emulator = self.machine.reg_read(getattr(xc, "UC_X86_REG_" + name.upper()))
            assert actual[name] == hardware[name], (code, name, actual[name], hardware[name], slots)
            if name == "rbp" and width == 2 and emulator != hardware[name]:
                assert emulator == rsp - width
                assert hardware[name] == (rbp & ~0xffff) | ((rsp - width) & 0xffff)
                self.unicorn_frame_differences += 1
            else:
                assert actual[name] == emulator, (code, name, actual[name], emulator, slots)
        actual_flags = sum(actual[k] << bit for k, bit in FLAGS.items())
        assert actual_flags == flags == hardware["flags"] & FLAG_MASK == self.machine.reg_read(xc.UC_X86_REG_EFLAGS) & FLAG_MASK
        assert int(response["next"], 16) == self.machine.reg_read(xc.UC_X86_REG_RIP) == address + len(bytes.fromhex(code))
        for index, (start, data) in enumerate(memory):
            actual_data = bytes(response["memory"][f"0x{start + i:X}"] for i in range(len(data)))
            assert actual_data == hardware["memory"][index] == bytes(self.machine.mem_read(start, len(data))), (code, "memory", slots)
        assert response["Accesses"] == self.accesses, (code, response["Accesses"], self.accesses)
        events = response["events"]
        assert len(events) == len(response["Accesses"]) + 1
        assert events[-1]["Kind"] == "WriteProbe" and events[-1]["Address"] == final and events[-1]["SizeBytes"] == 1
        assert all(event["Outcome"] == "Completed" for event in events)
        self.checks += 1
        self.native_checks += 1


def differential(h):
    for prefix in ("", "66"):
        for nesting in range(256):
            for allocation in (0, 1, 65535):
                h.run(allocation, nesting, prefix)
        for nesting in range(32):
            for distance in (-128, -8, -2, 0, 2, 8, 128):
                h.run(37, nesting, prefix, distance)
        for allocation in (15, 16, 255, 256, 4095, 4096, 32768, 65534):
            for nesting in (0, 1, 2, 31):
                h.run(allocation, nesting, prefix, distance=8)
    for prefix in ("67", "6766", "48", "6648", "4866"):
        for nesting in (0, 1, 2, 31, 32, 63, 255):
            h.run(7, nesting, prefix)
    # BP writes retain the original high 48 bits, including when frame reads cross 64 KiB.
    boundary = h.native.boundary
    for nesting in (0, 1, 2, 3, 31, 255):
        h.run(0, nesting, "66", rbp=boundary + 2)
        h.run(0, nesting, "66", rsp=boundary + 0x10001, rbp=boundary + 0x10300)


def fault_contracts(h):
    for prefix, width in (("", 8), ("66", 2)):
        code = enter_code(16, 2, prefix)
        rsp, rbp = 0x50080, 0x50100
        slots = {"rsp": rsp, "rbp": rbp}
        first, source, second, third = rsp - width, rbp - width, rsp - width * 2, rsp - width * 3
        final = third - 16
        full = [(rsp - 0x80, bytes(0x100))]
        for permitted, outcome in ((None, "UnmodeledEnvironmentStop"), (False, "UnmodeledFaultStop"), (True, "Normal")):
            permissions = [] if permitted is None else [{"address": hex(final), "size": 1, "allowed": permitted}]
            response = h.request(code, slots, full, permissions)
            assert response["Outcome"] == outcome and response["support"] == "NormalPathOnly", response
            assert response["events"][-1]["Kind"] == "WriteProbe"
            if permitted is not True:
                assert {k: int(v, 16) for k, v in response["slots"].items()} == slots
                assert response["next"] is None
            h.fault_checks += 1
        for memory, expected in (([], [f"Store:0x{first:X}:{width}"]),
                                 ([(first, bytes(width))], [f"Store:0x{first:X}:{width}", f"Load:0x{source:X}:{width}"]),
                                 ([(first, bytes(width)), (source, bytes(width))], [f"Store:0x{first:X}:{width}", f"Load:0x{source:X}:{width}", f"Store:0x{second:X}:{width}"])):
            response = h.request(code, slots, memory, [])
            assert response["Outcome"] == "UnmodeledFaultStop" and response["next"] is None
            assert response["Accesses"] == expected
            assert {k: int(v, 16) for k, v in response["slots"].items()} == slots
            assert response["events"][-1]["Outcome"] == "UnmodeledFaultStop"
            h.fault_checks += 1
        for updates in ({"rsp": 0x800000000008}, {"rsp": 0x800000000001}, {"rbp": 0x800000000010}):
            response = h.request(code, slots | updates, full, [])
            assert response["Outcome"] == "UnmodeledFaultStop" and response["next"] is None
            assert {k: int(v, 16) for k, v in response["slots"].items()} == slots | updates
            assert not any(event["Kind"] == "WriteProbe" for event in response["events"])
            h.fault_checks += 1
        # The probe needs permission evidence, not a fictitious data read or store.
        response = h.request(enter_code(0x1000, 0, prefix), slots, [(first, bytes(width))],
                             [{"address": hex(first - 0x1000), "size": 1, "allowed": True}])
        assert response["Outcome"] == "Normal" and response["Accesses"] == [f"Store:0x{first:X}:{width}"]
        assert len(response["memory"]) == width
        h.fault_checks += 1
        for available in range(1, width):
            response = h.request(code, slots, [(first, bytes(available))], [])
            assert response["Outcome"] == "UnmodeledFaultStop"
            assert all(value == 0 for value in response["memory"].values())
            assert {k: int(v, 16) for k, v in response["slots"].items()} == slots
            h.fault_checks += 1
        response = h.request(code, slots, full, [{"address": hex(first), "size": width, "allowed": False}])
        assert response["Outcome"] == "UnmodeledFaultStop" and len(response["events"]) == 1
        assert all(value == 0 for value in response["memory"].values())
        h.fault_checks += 1
        response = h.request(enter_code(0, 0, prefix), {"rsp": width - 1, "rbp": rbp}, [], [])
        assert response["Outcome"] == "UnmodeledFaultStop" and response["Accesses"] == []
        assert response["events"] == []
        h.fault_checks += 1
        # The first push is canonical but the allocation enters the canonical-address hole.
        high_rsp = 0xffff800000000000 + width
        response = h.request(enter_code(1, 0, prefix), {"rsp": high_rsp, "rbp": rbp},
                             [(high_rsp - width, bytes(width))], [])
        assert response["Outcome"] == "UnmodeledFaultStop"
        assert response["Accesses"] == [f"Store:0x{high_rsp - width:X}:{width}"]
        assert len(response["events"]) == 1 and response["events"][0]["Outcome"] == "Completed"
        h.fault_checks += 1
    for prefix in ("f0", "f2", "f3"):
        response = h.request(prefix + enter_code(0, 0), {}, [], [])
        assert not response["supported"], response
        h.rejected += 1


if __name__ == "__main__":
    with NativeEnterOracle() as native, subprocess.Popen(["dotnet", sys.argv[1], "serve"], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, text=True, encoding="utf-8", bufsize=1) as server:
        harness = StackHarness(server, native)
        differential(harness)
        fault_contracts(harness)
        server.stdin.close()
        assert server.wait() == 0
        print(json.dumps({"checks": harness.checks, "forms": len(harness.forms), "nativeChecks": harness.native_checks,
                          "faultContracts": harness.fault_checks, "rejected": harness.rejected,
                          "unicorn16BitFrameDifferences": harness.unicorn_frame_differences}, indent=2))
