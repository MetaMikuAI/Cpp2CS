"""段选择子硬件差分与 INT1/禁用扩展的 MIR 边界合同；不触发宿主异常。"""

import argparse
from collections import Counter
import ctypes
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess

from x64_float_native import NativeFloatOracle


ROOT = Path(__file__).resolve().parents[1]
CODE, DATA = 0x10000, 0x50000
SEGMENTS = ("es", "cs", "ss", "ds", "fs", "gs")
GPRS = ("rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", *(f"r{i}" for i in range(8, 16)))
FLAGS = ("cf", "pf", "af", "zf", "sf", "df", "of")
RNG = random.Random(0xC22651)


def segment_code(segment, width, register=0, memory=False, prefix=""):
    assert segment in range(6) and width in (16, 32, 64) and register in range(16)
    assert prefix in ("", "64", "65", "67")
    rex = (0x48 if width == 64 else 0x40) | (register >= 8)
    return prefix + ("66" if width == 16 else "") + (f"{rex:02x}" if rex != 0x40 else "") + "8c" + f"{(0 if memory else 0xc0) | (segment << 3) | (register & 7):02x}"


NATIVE_CODES = {segment_code(segment, width, register, prefix=prefix): (register, False)
                for segment, width, register, prefix in itertools.product(range(6), (16, 32, 64), (0, 8, 9, 11), ("", "64", "65"))}
NATIVE_CODES.update({segment_code(segment, width, 2, True): (0, True)
                     for segment, width in itertools.product(range(6), (16, 32, 64))})


class NativeSegmentOracle(NativeFloatOracle):
    """仅执行 8C/r 白名单；不修改段状态，仅写独立缓冲区或易失 GPR。"""

    def __init__(self):
        super().__init__()
        self.memory = (ctypes.c_ubyte * 24)()

    def function(self, code):
        assert code in NATIVE_CODES, code
        if code in self._functions:
            return self._functions[code][1]
        register, memory = NATIVE_CODES[code]
        # RCX=initial GPR, RDX=buffer. Capture flags with only flag-preserving helpers.
        before = bytes.fromhex("9c415a4c895208")
        before += bytes((0x49 if register >= 8 else 0x48, 0x89, 0xc8 | (register & 7)))
        after = bytes.fromhex("9c415a4c895210")
        if register != 0 and not memory:
            after += bytes((0x4c, 0x89, 0xc0 | ((register & 7) << 3)))
        machine_code = before + bytes.fromhex(code) + after + b"\xc3"
        address = self._kernel.VirtualAlloc(None, len(machine_code), 0x3000, 0x04)
        if not address:
            raise OSError(ctypes.get_last_error(), "VirtualAlloc")
        ctypes.memmove(address, machine_code, len(machine_code))
        old = ctypes.c_ulong()
        if not self._kernel.VirtualProtect(address, len(machine_code), 0x20, ctypes.byref(old)):
            raise OSError(ctypes.get_last_error(), "VirtualProtect")
        if not self._kernel.FlushInstructionCache(ctypes.c_void_p(-1), address, len(machine_code)):
            raise OSError(ctypes.get_last_error(), "FlushInstructionCache")
        function = ctypes.WINFUNCTYPE(ctypes.c_uint64, ctypes.c_uint64, ctypes.c_void_p)(address)
        self._functions[code] = address, function
        return function

    def run_segment(self, code, initial):
        data = RNG.randbytes(8)
        ctypes.memmove(self.memory, data, len(data))
        result = self.function(code)(initial, ctypes.addressof(self.memory))
        flags = bytes(self.memory)[8:]
        assert flags[:8] == flags[8:], (code, flags.hex())
        return result, data, bytes(self.memory)[:8]


class Harness:
    def __init__(self, server):
        self.server = server
        self.counts = Counter()
        self.forms = set()

    def execute(self, code, slots=None, memory=None, **extra):
        self.forms.add(code)
        request = dict(arch="x64", bytes=code, address=hex(CODE), roundtrip=True,
                       slots={name: hex(value) for name, value in (slots or {}).items()},
                       memory=[dict(address=hex(start), bytes=data.hex()) for start, data in (memory or [])], **extra)
        self.server.stdin.write(json.dumps(request) + "\n")
        self.server.stdin.flush()
        line = self.server.stdout.readline()
        assert line, ("production CLI exited", self.server.poll(), request)
        return json.loads(line)

    def normal(self, code, slots, expected, memory=None, expected_memory=None):
        result = self.execute(code, slots, memory)
        assert result["supported"] and result["Outcome"] == "Normal", (code, result)
        assert int(result["next"], 16) == CODE + len(bytes.fromhex(code)), (code, result)
        assert {name: int(value, 16) for name, value in result["slots"].items()} == expected, (code, slots, result, expected)
        if memory:
            start, data = memory[0]
            actual = bytes(result["memory"][f"0x{start + index:X}"] for index in range(len(data)))
            assert actual == expected_memory, (code, actual.hex(), expected_memory.hex())
            assert result["Accesses"] == [f"Store:0x{start:X}:2"], result
            assert len(result["events"]) == 1 and result["events"][0]["SizeBytes"] == 2, result
            assert result["support"] == "NormalPathOnly", result
        else:
            assert result["events"] == result["Accesses"] == [], result
            assert result["support"] == "Exact", result
        return result


def native_segments(harness, oracle):
    selectors = {name: oracle.run_segment(segment_code(index, 32), 0)[0] for index, name in enumerate(SEGMENTS)}
    for segment, width, register, prefix in itertools.product(range(6), (16, 32, 64), (0, 8, 9, 11), ("", "64", "65")):
        code = segment_code(segment, width, register, prefix=prefix)
        for initial in (0, (1 << 64) - 1, 0xA5B6C7D8E9F01234, RNG.getrandbits(64)):
            value, before, after = oracle.run_segment(code, initial)
            assert before == after, code
            expected_value = (initial & ~65535) | selectors[SEGMENTS[segment]] if width == 16 else selectors[SEGMENTS[segment]]
            assert value == expected_value, (code, hex(value), hex(expected_value))
            slots = dict(selectors, **{GPRS[register]: initial}, fsbase=0xFEDCBA9876543210, gsbase=0x123456789ABCDEF0)
            slots.update({flag: RNG.getrandbits(1) for flag in FLAGS})
            harness.normal(code, slots, dict(slots, **{GPRS[register]: value}))
            harness.counts["native-segment-register"] += 1
    for segment, width in itertools.product(range(6), (16, 32, 64)):
        code = segment_code(segment, width, 2, True)
        for _ in range(8):
            _, before, after = oracle.run_segment(code, RNG.getrandbits(64))
            assert after == selectors[SEGMENTS[segment]].to_bytes(2, "little") + before[2:], code
            slots = dict(selectors, rdx=DATA, fsbase=1 << 63, gsbase=0xDEAD)
            slots.update({flag: RNG.getrandbits(1) for flag in FLAGS})
            harness.normal(code, slots, slots, [(DATA, before)], after)
            harness.counts["native-segment-memory"] += 1
    return selectors


def segment_contracts(harness):
    for segment, width, register, selector in itertools.product(range(6), (16, 32, 64), range(16), (0, 3, 0xABCD, 0xFFFF)):
        code = segment_code(segment, width, register)
        initial = RNG.getrandbits(64)
        slots = {SEGMENTS[segment]: selector, GPRS[register]: initial}
        expected = (initial & ~65535) | selector if width == 16 else selector
        harness.normal(code, slots, dict(slots, **{GPRS[register]: expected}))
        harness.counts["synthetic-selector-and-gpr"] += 1
    for segment, prefix, width, selector in itertools.product(range(6), ("64", "65"), (16, 32, 64), (0, 0xFFFF)):
        code = segment_code(segment, width, 0, True, prefix)
        slots = dict.fromkeys(SEGMENTS, 0x1234)
        slots.update(rax=0x120, fsbase=DATA - 0x120, gsbase=DATA - 0x120)
        slots[SEGMENTS[segment]] = selector
        before = RNG.randbytes(8)
        harness.normal(code, slots, slots, [(DATA, before)], selector.to_bytes(2, "little") + before[2:])
        harness.counts["synthetic-selector-base-independence"] += 1
    for prefix in ("", "66", "48", "67", "6748"):
        code = prefix + "8c2a"  # MOV [RDX/EDX],GS; memory width remains 16.
        slots = dict(gs=0xABCD, rdx=DATA)
        harness.normal(code, slots, slots, [(DATA, b"\x12\x34")], b"\xcd\xab")
        harness.counts["synthetic-two-byte-mapping"] += 1
        result = harness.execute(code, slots, [(DATA, b"\x12")])
        assert result["supported"] and result["Outcome"] == "UnmodeledFaultStop", result
        assert {name: int(value, 16) for name, value in result["slots"].items()} == slots, result
        assert result["memory"] == {f"0x{DATA:X}": 0x12}, result
        harness.counts["synthetic-short-mapping"] += 1


def boundaries(harness):
    codes = {prefix + "f1": ("x64.#DB", CODE + len(bytes.fromhex(prefix)) + 1)
             for prefix in ("", "41", "43", "4e", "64", "65", "66", "67")}
    codes.update({code: ("x64.#UD", CODE) for code in ("62f2e50840c0", "62f2fd083fca", "62f2e5894000", "62f2fd193f08")})
    for code, (event, resume) in codes.items():
        for populated in (False, True):
            slots = {name: RNG.getrandbits(64) for name in GPRS} if populated else {}
            if populated:
                slots.update({name: RNG.getrandbits(16) for name in SEGMENTS})
                slots.update({name: RNG.getrandbits(1) for name in FLAGS})
                slots.update({f"xmm{i}": RNG.getrandbits(128) for i in range(16)})
                slots.update({f"ymm{i}_hi": RNG.getrandbits(128) for i in range(16)})
            data = RNG.randbytes(16)
            result = harness.execute(code, slots, [(DATA, data)],
                                     schedule=[dict(beforeEvent=0, address=hex(DATA), bytes="ff", invalidateExclusive=True)])
            assert result["supported"] and result["support"] == "ExceptionBoundaryOnly", (code, result)
            assert result["Outcome"] == "Trap" and result["Event"] == event, (code, result)
            assert result["next"] is None and int(result["resumeAddress"], 16) == resume, result
            assert {name: int(value, 16) for name, value in result["slots"].items()} == slots, result
            assert result["memory"] == {f"0x{DATA + index:X}": value for index, value in enumerate(data)}, result
            assert result["events"] == result["Accesses"] == result["appliedSchedule"] == [], result
            assert len(result["remainingSchedule"]) == 1, result
            harness.counts["synthetic-exception-boundary"] += 1
    rejected = ("f2f1", "f3f1", "f38ce0", "f28ce0", "8ee0", "8e00", "8ed0", "0f02c0", "f301cc",
                "62f2e54840c0", "62f2fd483fca", "62f1fd086fc0")
    for code in rejected:
        result = harness.execute(code, evaluate=False)
        assert not result["supported"] and result["decoded"], (code, result)
        harness.counts["unsupported-contract"] += 1
    for code in ("62f2e58840c0", "62f2e50840", "8ec8", "f18c00", "f08ce0"):
        result = harness.execute(code, evaluate=False)
        assert not result["supported"], (code, result)
        if code != "f18c00":
            assert not result["decoded"], (code, result)
        harness.counts["invalid-or-boundary-mismatch"] += 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dll", type=Path, default=ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll")
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/x64-profile-checks.json")
    args = parser.parse_args()
    oracle = NativeSegmentOracle()
    with subprocess.Popen(["dotnet", str(args.dll), "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          text=True, encoding="utf-8") as server:
        harness = Harness(server)
        selectors = native_segments(harness, oracle)
        segment_contracts(harness)
        boundaries(harness)
        server.stdin.close()
        assert server.wait() == 0
    oracle.close()
    sources = ("src/Cpp2CS/X64/X64SystemRead.cs", "src/Cpp2CS/X64/X64Lifter.cs", "src/Cpp2CS/Ir/Model.cs",
               "src/Cpp2CS/Ir/MachineProfile.cs", "tests/x64_profile_checks.py", "tests/x64_float_native.py")
    report = dict(checks=sum(harness.counts.values()), checksByGroup=harness.counts, encodings=len(harness.forms),
                  nativeChecks=sum(count for group, count in harness.counts.items() if group.startswith("native-")),
                  observedHostSelectors=selectors, productSha256=hashlib.sha256(args.dll.read_bytes()).hexdigest(),
                  sourceSha256={name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in sources},
                  scope="Only segment-selector reads run on hardware. Arbitrary selectors, FS/GS base mappings and exception boundaries are separate MIR contracts; no host INT1/EVEX fault or exception-delivery/game execution.")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
