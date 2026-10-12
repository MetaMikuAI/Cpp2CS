"""合成 INT3 与 Unicorn 异常钩子对照；不模拟异常分派或处理器。"""
import json
import random
import subprocess
import sys

from unicorn import Uc, UC_ARCH_X86, UC_MODE_64, UC_HOOK_INTR
from unicorn import x86_const as x86

CODE = 0x10000
MEMORY = 0x20000
REGISTERS = ("rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15")
FLAG_BITS = {"cf": 0, "pf": 2, "af": 4, "zf": 6, "sf": 7, "df": 10, "of": 11}


def main():
    rng = random.Random(803)
    checks = 0
    with subprocess.Popen(["dotnet", sys.argv[1], "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, encoding="utf-8") as product:
        for code in (bytes.fromhex(text) for text in ("cc", "66cc", "67cc", "40cc")):
            for _ in range(16):
                cpu = Uc(UC_ARCH_X86, UC_MODE_64)
                cpu.mem_map(CODE, 4096)
                cpu.mem_map(MEMORY, 4096)
                cpu.mem_write(CODE, code)
                data = rng.randbytes(64)
                cpu.mem_write(MEMORY, data)
                slots = {register: rng.getrandbits(64) for register in REGISTERS}
                slots.update({f"xmm{i}": rng.getrandbits(128) for i in range(16)})
                slots.update({name: rng.getrandbits(1) for name in FLAG_BITS})
                slots["mxcsr"] = 0x1F80
                for register in (*REGISTERS, *(f"xmm{i}" for i in range(16)), "mxcsr"):
                    cpu.reg_write(getattr(x86, "UC_X86_REG_" + register.upper()), slots[register])
                eflags = 0x202 | sum(slots[name] << bit for name, bit in FLAG_BITS.items())
                cpu.reg_write(x86.UC_X86_REG_EFLAGS, eflags)
                events = []

                def interrupt(machine, vector, _context):
                    events.append((vector, machine.reg_read(x86.UC_X86_REG_RIP)))
                    machine.emu_stop()

                cpu.hook_add(UC_HOOK_INTR, interrupt)
                cpu.emu_start(CODE, CODE + len(code), count=1)
                assert events == [(3, CODE + len(code))], (code.hex(), events)
                for register in (*REGISTERS, *(f"xmm{i}" for i in range(16)), "mxcsr"):
                    assert cpu.reg_read(getattr(x86, "UC_X86_REG_" + register.upper())) == slots[register]
                assert cpu.reg_read(x86.UC_X86_REG_EFLAGS) == eflags
                assert bytes(cpu.mem_read(MEMORY, 64)) == data
                request = {"arch": "x64", "bytes": code.hex(), "address": hex(CODE), "roundtrip": True,
                           "slots": {name: hex(value) for name, value in slots.items()},
                           "memory": [{"address": hex(MEMORY), "bytes": data.hex()}]}
                product.stdin.write(json.dumps(request) + "\n")
                product.stdin.flush()
                result = json.loads(product.stdout.readline())
                assert result["supported"] and result["support"] == "ExceptionBoundaryOnly", result
                assert result["Outcome"] == "Trap" and result["Event"] == "x64.#BP" and result["next"] is None
                assert int(result["resumeAddress"], 16) == events[0][1]
                assert {name: int(value, 16) for name, value in result["slots"].items()} == slots
                assert not result["Accesses"]
                assert {int(address, 16): value for address, value in result["memory"].items()} == {MEMORY + i: value for i, value in enumerate(data)}
                checks += 1
        product.stdin.close()
        assert product.wait() == 0
    print(json.dumps({"int3_boundary_checks": checks, "passed": True,
                      "scope": "Synthetic instruction event and saved RIP only; no IDT checks, exception delivery, handler or game execution."}))


if __name__ == "__main__":
    main()
