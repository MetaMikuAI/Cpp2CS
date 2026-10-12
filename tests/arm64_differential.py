"""真实 ARM64 规则 → MIR → 解释器，与 Unicorn 的独立单指令对照。"""

import argparse
import collections
import itertools
import json
import pathlib
import random
import subprocess

import capstone
import unicorn
from capstone import Cs, CS_ARCH_ARM64
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_READ
from unicorn import arm64_const as arm


ROOT = pathlib.Path(__file__).resolve().parents[1]
CODE = 0x10000
MEMORY = 0x30000
BASE = MEMORY + 0x200
SEED = 808064


def corpus(rng):
    for sf in (0, 1):
        for op in range(4):
            for immediate in (0, 1, 4095):
                for shift in (0, 1):
                    yield "addsub.immediate", (sf << 31) | (op << 29) | 0x11000000 | (shift << 22) | (immediate << 10) | (1 << 5), False
            for shift_kind in range(3):
                for amount in (0, 1, 31 if sf == 0 else 63):
                    yield "addsub.shifted", (sf << 31) | (op << 29) | 0x0B000000 | (shift_kind << 22) | (2 << 16) | (amount << 10) | (1 << 5), False
            for option in (0, 1, 2, 4, 5, 6) + ((3, 7) if sf else ()):
                yield "addsub.extended", (sf << 31) | (op << 29) | 0x0B200000 | (2 << 16) | (option << 13) | (4 << 10) | (1 << 5), False
            yield "addsub.carry", (sf << 31) | (op << 29) | 0x1A000000 | (2 << 16) | (1 << 5), False
            for invert in (0, 1):
                for shift_kind in range(4):
                    yield "logical.register", (sf << 31) | (op << 29) | 0x0A000000 | (shift_kind << 22) | (invert << 21) | (2 << 16) | (7 << 10) | (1 << 5), False
            for size in (2, 4, 8, 16, 32) + ((64,) if sf else ()):
                n = int(size == 64)
                imms = ((~(size - 1) << 1) & 63) | (size // 2 - 1)
                yield "logical.immediate", (sf << 31) | (op << 29) | 0x12000000 | (n << 22) | (1 << 16) | (imms << 10) | (1 << 5), False
        for op in (0, 2, 3):
            for hw in range(2 << sf):
                yield "move.wide", (sf << 31) | (op << 29) | 0x12800000 | (hw << 21) | (0xABCD << 5), False
        for op in range(3):
            for rotate, end in ((0, 0), (1, 7), (7, 1), (0, 31), (31, 31)) + (((63, 0), (0, 63), (63, 63)) if sf else ()):
                yield "bitfield", (sf << 31) | (op << 29) | 0x13000000 | (sf << 22) | (rotate << 16) | (end << 10) | (1 << 5), False
        for shift in (0, 1, 31 if sf == 0 else 63):
            yield "extract", (sf << 31) | 0x13800000 | (sf << 22) | (2 << 16) | (shift << 10) | (1 << 5), False
        for op in range(4):
            for cond in range(16):
                yield "conditional.select", (sf << 31) | ((op >> 1) << 30) | 0x1A800000 | (2 << 16) | (cond << 12) | ((op & 1) << 10) | (1 << 5), False
        for subtract in (0, 1):
            for immediate in (0, 1):
                for cond in range(16):
                    yield "conditional.compare", (sf << 31) | (subtract << 30) | 0x3A400000 | (2 << 16) | (cond << 12) | (immediate << 11) | (1 << 5) | 0xA, False
        for op in range(8, 12):
            yield "shift.variable", (sf << 31) | 0x1AC00000 | (2 << 16) | (op << 10) | (1 << 5), False
        for op in range(5):
            if op != 3 or sf:
                yield "integer.unary", (sf << 31) | 0x5AC00000 | (op << 10) | (1 << 5), False
        for subtract in (0, 1):
            yield "multiply.add", (sf << 31) | 0x1B000000 | (2 << 16) | (subtract << 15) | (3 << 10) | (1 << 5), False
    for page in (0, 1):
        for imm in (0, 1, 0x1FFFFF):
            yield "adr", 0x10000000 | (page << 31) | ((imm & 3) << 29) | ((imm >> 2) << 5), False
    for link in (0, 1):
        yield "branch.direct", 0x14000010 | (link << 31), False
    for cond in range(16):
        yield "branch.condition", 0x54000000 | (16 << 5) | cond, False
    for sf in (0, 1):
        for invert in (0, 1):
            yield "branch.zero", 0x34000000 | (sf << 31) | (invert << 24) | (16 << 5) | 1, False
            yield "branch.bit", 0x36000000 | (sf << 31) | (invert << 24) | (7 << 19) | (16 << 5) | 1, False
    for word in (0xD61F0020, 0xD63F03C0, 0xD65F03C0):
        yield "branch.register", word, False
    for word in (0xD53B4200, 0xD51B4201):
        yield "nzcv.transfer", word, False
    yield "nop", 0xD503201F, False
    for family, word in (
        ("addsub.shifted", 0xEB02003F),  # cmp x1,x2
        ("addsub.shifted", 0xAB02003F),  # cmn x1,x2
        ("addsub.shifted", 0xCB0103E0),  # neg x0,x1
        ("logical.register", 0xEA02003F),  # tst x1,x2
        ("logical.register", 0xAA2103E0),  # mvn x0,x1
        ("conditional.select", 0x9A9F17E0),  # cset x0,eq
        ("conditional.select", 0xDA9F13E0),  # csetm x0,eq
        ("conditional.select", 0x9A811421),  # cinc x1,x1,eq
        ("addsub.carry", 0xBA020021),  # adcs x1,x1,x2
        ("addsub.carry", 0xFA020022),  # sbcs x2,x1,x2
        ("addsub.immediate", 0x910043FF),  # add sp,sp,#16
        ("addsub.immediate", 0xB10043FF),  # cmn sp,#16
        ("logical.immediate", 0xB24003FF),  # orr sp,xzr,#1
    ):
        yield family, word, False
    for vector in (0, 1):
        for size in range(4):
            for opcode in range(4):
                valid = (opcode < 2 or size == 0) if vector else not ((opcode == 2 and size == 3) or (opcode == 3 and size >= 2))
                if not valid:
                    continue
                prefix = (size << 30) | (vector << 26) | (opcode << 22) | (3 << 5)
                yield "memory.unsigned", prefix | 0x39000000 | (2 << 10), True
                for mode in (0, 1, 3):
                    yield "memory.unscaled", prefix | 0x38000000 | ((-16 & 511) << 12) | (mode << 10), True
                for option in (2, 3, 6, 7):
                    for scale in (0, 1):
                        yield "memory.register", prefix | 0x38200800 | (4 << 16) | (option << 13) | (scale << 12), True
        for opcode in range(3):
            for load in (0, 1):
                for mode in range(4):
                    if not vector and opcode == 1 and (not load or mode == 0):
                        continue
                    yield "memory.pair", 0x28000000 | (opcode << 30) | (vector << 26) | (mode << 23) | (load << 22) | ((-2 & 127) << 15) | (1 << 10) | (3 << 5), True
            yield "memory.literal", 0x18000000 | (opcode << 30) | (vector << 26) | (8 << 5), True
    for word in (0xF940007F, 0xB940007F, 0x3940007F, 0xF900007F, 0xF94003E0, 0xF81F0FE0):
        yield "memory.zero-or-sp", word, True
    templates = list(corpus_random_templates())
    for _ in range(300):
        form, base, variable_mask = rng.choice(templates)
        word = base | (rng.getrandbits(32) & variable_mask)
        yield form, word, False
    yield from simd_corpus()


def simd_corpus():
    for imm5 in range(1, 32):
        if not imm5 & 15:
            continue
        size = (imm5 & -imm5).bit_length() - 1
        for q in (0, 1):
            for rd, rn in ((0, 1), (1, 1), (31, 31)):
                prefix = (q << 30) | (imm5 << 16) | (rn << 5) | rd
                if size < 3 or q:
                    yield "simd.dup.element", 0x0E000400 | prefix, False
                    yield "simd.dup.general", 0x0E000C00 | prefix, False
                if (q and size == 3) or (not q and size < 3):
                    yield "simd.umov", 0x0E003C00 | prefix, False
                if size < (3 if q else 2):
                    yield "simd.smov", 0x0E002C00 | prefix, False
        for rd, rn in ((0, 1), (1, 1), (31, 31)):
            prefix = (imm5 << 16) | (rn << 5) | rd
            yield "simd.dup.scalar", 0x5E000400 | prefix, False
            yield "simd.ins.general", 0x4E001C00 | prefix, False
            for imm4 in (0, 15):
                yield "simd.ins.element", 0x6E000400 | (imm4 << 11) | prefix, False
    for q in (0, 1):
        for opcode in range(8):
            for rd, rn, rm in ((0, 1, 2), (1, 1, 2), (2, 1, 2), (0, 1, 1), (31, 31, 31)):
                yield "simd.logical", 0x0E201C00 | (q << 30) | ((opcode >> 2) << 29) | ((opcode & 3) << 22) | (rm << 16) | (rn << 5) | rd, False
        for rd, rn in ((0, 1), (1, 1)):
            yield "simd.not", 0x2E205800 | (q << 30) | (rn << 5) | rd, False
        for offset in range(8 << q):
            yield "simd.extract", 0x2E000000 | (q << 30) | (2 << 16) | (offset << 11) | (1 << 5), False
            yield "simd.extract", 0x2E000000 | (q << 30) | (1 << 16) | (offset << 11) | (1 << 5) | 1, False
        for size in range(4):
            if size == 3 and not q:
                continue
            for subtract in (0, 1):
                for rd in (0, 1, 2):
                    yield "simd.addsub", 0x0E208400 | (q << 30) | (subtract << 29) | (size << 22) | (2 << 16) | (1 << 5) | rd, False
        for subtract in (0, 1):
            yield "simd.addsub.scalar", 0x5EE08400 | (subtract << 29) | (2 << 16) | (1 << 5) | 1, False
        for op in (0, 1):
            for cmode in range(16):
                if cmode == 15 and op and not q:
                    continue
                for immediate in range(256):
                    yield "simd.immediate", 0x0F000400 | (q << 30) | (op << 29) | ((immediate >> 5) << 16) | (cmode << 12) | ((immediate & 31) << 5), False
    for prefix in (0x1E260000, 0x1E270000, 0x9E660000, 0x9E670000, 0x9EAE0000, 0x9EAF0000):
        for rd, rn in ((0, 1), (1, 1), (31, 31)):
            yield "fmov.general", prefix | (rn << 5) | rd, False
    for double in (0, 1):
        for rd, rn in ((0, 1), (1, 1), (31, 31)):
            yield "fmov.register", 0x1E204000 | (double << 22) | (rn << 5) | rd, False
        for immediate in range(256):
            yield "fmov.immediate", 0x1E201000 | (double << 22) | (immediate << 13), False
    for unsigned in (0, 1):
        for subtract in (0, 1):
            for rd, rn, rm, ra in ((0, 1, 2, 3), (1, 1, 2, 1), (2, 1, 2, 2), (0, 1, 2, 31), (31, 31, 31, 31)):
                yield "multiply.long", 0x9B200000 | (unsigned << 23) | (rm << 16) | (subtract << 15) | (ra << 10) | (rn << 5) | rd, False
        for rd, rn, rm in ((0, 1, 2), (1, 1, 2), (2, 1, 2), (31, 31, 31)):
            yield "multiply.high", 0x9B407C00 | (unsigned << 23) | (rm << 16) | (rn << 5) | rd, False
    for sf in (0, 1):
        for signed in (0, 1):
            for rd, rn, rm in ((0, 1, 2), (1, 1, 2), (2, 1, 2), (0, 1, 31), (31, 31, 31)):
                yield "integer.divide", 0x1AC00800 | (sf << 31) | (signed << 10) | (rm << 16) | (rn << 5) | rd, False


def corpus_random_templates():
    yield "random.add-immediate", 0x91000000, 0x607FFFFF
    yield "random.add-shifted", 0x8B000000, 0x605FFFFF
    yield "random.logical", 0x8A000000, 0x60FFFFFF
    yield "random.bitfield", 0xD3400000, 0x003FFFFF
    yield "random.move", 0xD2800000, 0x007FFFFF


def classification_boundaries():
    for q, op, scalar, imm5, opcode in itertools.product(range(2), range(2), range(2), range(32), range(32)):
        yield "simd-copy-fields", 0x0E000420 | (q << 30) | (op << 29) | (scalar << 28) | (imm5 << 16) | (opcode << 11)
    for q, op, scalar, size, opcode in itertools.product(range(2), range(2), range(2), range(4), range(64)):
        yield "simd-three-fields", 0x0E220020 | (q << 30) | (op << 29) | (scalar << 28) | (size << 22) | (opcode << 10)
    for sf, s, ftype, rmode, opcode in itertools.product(range(2), range(2), range(4), range(4), range(8)):
        yield "fmov-general-fields", 0x1E200020 | (sf << 31) | (s << 29) | (ftype << 22) | (rmode << 19) | (opcode << 16)
    for q, op, o2, cmode in itertools.product(range(2), range(2), range(2), range(16)):
        yield "simd-immediate-fields", 0x0F050540 | (q << 30) | (op << 29) | (o2 << 11) | (cmode << 12)
    for sf, op, ra, subtract in itertools.product(range(2), range(8), range(32), range(2)):
        yield "multiply-fields", 0x1B020020 | (sf << 31) | (op << 21) | (ra << 10) | (subtract << 15)
    seeds = set()
    seed_counts = collections.Counter()
    for family, word, _ in simd_corpus():
        if seed_counts[family] < 8:
            seeds.add(word)
            seed_counts[family] += 1
    for word in sorted(seeds):
        for bit in range(32):
            if bit >= 10:
                yield "new-rule-single-bit-neighbors", word ^ (1 << bit)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dll", type=pathlib.Path, default=ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll")
    parser.add_argument("--output", type=pathlib.Path, default=ROOT / "artifacts/arm64-differential.json")
    parser.add_argument("--fuzz-words", type=int, default=200000)
    args = parser.parse_args()
    rng = random.Random(SEED)
    decoder = Cs(CS_ARCH_ARM64, 0)
    machine = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    machine.mem_map(CODE, 0x2000)
    machine.mem_map(MEMORY, 0x2000)
    machine.reg_write(arm.UC_ARM64_REG_CPACR_EL1, 0x300000)
    reads_writes = []
    machine.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, lambda _uc, access, address, size, _value, _data: reads_writes.append(("Load" if access == UC_MEM_READ else "Store", address, size)))
    child = subprocess.Popen(["dotnet", str(args.dll), "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, encoding="utf-8")
    counts = collections.Counter()
    forms = set()
    roundtrips = set()
    edges = (0, 1, 15, 16, 31, 32, 63, 64, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF)

    def require(condition, message):
        if not condition:
            child.terminate()
            child.wait()
            raise AssertionError(message)

    def request(payload):
        child.stdin.write(json.dumps(payload) + "\n")
        child.stdin.flush()
        line = child.stdout.readline()
        require(bool(line), "Product CLI ended before returning a result")
        return json.loads(line)

    def registers():
        slots = {f"x{i}": rng.getrandbits(64) for i in range(31)}
        slots.update({f"v{i}": rng.getrandbits(128) for i in range(32)})
        slots.update(sp=BASE, n=0, z=0, c=0, v=0, fpcr=0, fpsr=0, tpidr_el0=0x12340000)
        return slots

    cases = list(corpus(rng))
    for case_index, (family, word, memory_case) in enumerate(cases):
        code = word.to_bytes(4, "little")
        decoded = list(decoder.disasm(code, CODE))
        require(len(decoded) == 1, f"Generated fixture is not decoded: {family} {word:08x}")
        instruction = decoded[0]
        condition_family = family in ("conditional.select", "conditional.compare", "branch.condition", "nzcv.transfer")
        variations = range(16) if condition_family else range(10 if family.startswith("multiply.") or family == "integer.divide" else 8 if family == "addsub.carry" else 1 if family in ("simd.immediate", "fmov.immediate") else 4 if not memory_case else 2)
        for variation in variations:
            slots = registers()
            slots["x1"] = edges[(case_index + variation) % len(edges)]
            slots["x2"] = edges[(case_index * 3 + variation * 5) % len(edges)]
            nzcv = variation if condition_family else (0 if variation % 2 == 0 else 15)
            if family == "addsub.carry":
                width = 64 if word >> 31 else 32
                carry_edges = ((0, 0, 0), (0, (1 << width) - 1, 0), (1 << (width - 1), (1 << (width - 1)) - 1, 0), ((1 << width) - 1, 0, 1), ((1 << (width - 1)) - 1, 0, 1), (1 << (width - 1), 0, 0))
                if variation < len(carry_edges):
                    slots["x1"], slots["x2"], old_carry = carry_edges[variation]
                    nzcv = (nzcv & ~2) | (old_carry << 1)
            if family == "nzcv.transfer":
                slots["x1"] = (variation << 28) | 0xABCD000F0000000F
            if family.startswith("multiply.") or family == "integer.divide":
                wide = word >> 31
                width = 64 if wide else 32
                mask = (1 << width) - 1
                arithmetic_edges = ((0, 0), (1, 0), (mask, 1), (mask, mask), (1 << (width - 1), mask), (1 << (width - 1), 1), ((1 << (width - 1)) - 1, 2), (0x80000000, 0xFFFFFFFF), (0xFFFFFFFF00000001, 0x80000000), (0x12345678, 7))
                slots["x1"], slots["x2"] = arithmetic_edges[variation]
            if family.startswith("simd.") or family.startswith("fmov."):
                if variation == 0:
                    slots["v0"] = (1 << 128) - 1
                    slots["v1"] = 0x7FC000007F800001FF80000000000001
                    slots["v2"] = (1 << 128) - 1
                elif variation == 1:
                    slots["v1"] = (1 << 128) - 1
                    slots["v2"] = 0x01010101010101010101010101010101
                slots["fpcr"] = 0x03400000
                slots["fpsr"] = 0x0800009F
            for i, flag in enumerate(("n", "z", "c", "v")):
                slots[flag] = (nzcv >> (3 - i)) & 1
            if family == "branch.register":
                slots[f"x{(word >> 5) & 31}"] = CODE + 0x40
            memory = []
            if memory_case:
                slots["x3"] = BASE
                slots["x4"] = 8
                data = rng.randbytes(0x400)
                memory.append({"address": hex(MEMORY), "bytes": data.hex()})
                machine.mem_write(MEMORY, data)
                if family == "memory.literal":
                    literal = rng.randbytes(64)
                    memory.append({"address": hex(CODE + 0x20), "bytes": literal.hex()})
                    machine.mem_write(CODE + 0x20, literal)
            for i in range(31):
                machine.reg_write(getattr(arm, f"UC_ARM64_REG_X{i}"), slots[f"x{i}"])
            for i in range(32):
                machine.reg_write(getattr(arm, f"UC_ARM64_REG_Q{i}"), slots[f"v{i}"])
            machine.reg_write(arm.UC_ARM64_REG_SP, slots["sp"])
            machine.reg_write(arm.UC_ARM64_REG_NZCV, nzcv << 28)
            machine.reg_write(arm.UC_ARM64_REG_FPCR, slots["fpcr"])
            machine.reg_write(arm.UC_ARM64_REG_FPSR, slots["fpsr"])
            machine.mem_write(CODE, code)
            machine.ctl_remove_cache(CODE, CODE + 4)
            reads_writes.clear()
            machine.emu_start(CODE, CODE + 4, count=1)
            roundtrip = family not in roundtrips or variation == 15
            result = request({"arch": "arm64", "bytes": code.hex(), "address": hex(CODE), "slots": {key: hex(value) for key, value in slots.items()}, "memory": memory, "roundtrip": roundtrip})
            label = f"{family} {word:08x} {instruction.mnemonic} {instruction.op_str} variation={variation}"
            require(result["supported"], f"Unexpected unsupported: {label}: {result}")
            require(result["Outcome"] == "Normal", f"Unexpected outcome: {label}: {result['Outcome']}")
            observed = {key: int(value, 16) for key, value in result["slots"].items()}
            expected = dict(slots)
            for i in range(31):
                expected[f"x{i}"] = machine.reg_read(getattr(arm, f"UC_ARM64_REG_X{i}"))
            for i in range(32):
                expected[f"v{i}"] = machine.reg_read(getattr(arm, f"UC_ARM64_REG_Q{i}"))
            expected["sp"] = machine.reg_read(arm.UC_ARM64_REG_SP)
            expected["fpcr"] = machine.reg_read(arm.UC_ARM64_REG_FPCR)
            expected["fpsr"] = machine.reg_read(arm.UC_ARM64_REG_FPSR)
            flags = machine.reg_read(arm.UC_ARM64_REG_NZCV) >> 28
            for i, flag in enumerate(("n", "z", "c", "v")):
                expected[flag] = (flags >> (3 - i)) & 1
            for slot, value in expected.items():
                require(observed.get(slot, 0) == value, f"State mismatch {label} slot={slot}: IR={observed.get(slot, 0):x} Unicorn={value:x}")
            require(int(result["next"], 16) == machine.reg_read(arm.UC_ARM64_REG_PC), f"PC mismatch {label}")
            ir_access = []
            for access in result["Accesses"]:
                kind, address, size = access.split(":")
                ir_access.extend((kind, int(address, 16) + byte) for byte in range(int(size)))
            cpu_access = [(kind, address + byte) for kind, address, size in reads_writes for byte in range(size)]
            require(ir_access == cpu_access, f"Memory access mismatch {label}: {ir_access} != {cpu_access}")
            for region in memory:
                address = int(region["address"], 16)
                actual = machine.mem_read(address, len(region["bytes"]) // 2)
                for offset, byte in enumerate(actual):
                    require(result["memory"][f"0x{address + offset:X}"] == byte, f"Memory byte mismatch {label} at {address + offset:x}")
            counts[family] += 1
            forms.add(result["Form"])
            if roundtrip:
                roundtrips.add(family)

    rejected = [
        0x12400000,  # 32-bit logical immediate N=1
        0x12C00000,  # 32-bit move-wide hw=2
        0x0BC00000,  # add/sub shifted with reserved ROR
        0x0B008000,  # 32-bit shift amount 32
        0xF8408463,  # ldr x3,[x3],#8: constrained writeback overlap
        0xA9400060,  # ldp x0,x0,[x3]: constrained duplicate destination
        0xD53BD060,  # unmodeled system register
        0x1E202000,  # FP compare is explicitly unsupported
        0xC85F7C20,  # exclusive load is explicitly unsupported
        0x0E000400,  # SIMD duplicate imm5=0
        0x0E080400,  # Q=0 duplicate D lane is reserved
        0x0E042C00,  # SMOV Wd,Sn has no sign extension
        0x4E013C00,  # UMOV Xd,Bn is reserved
        0x0EE08400,  # Q=0 vector ADD D is reserved
        0x2E004000,  # Q=0 EXT offset=8 is reserved
        0x2F00F400,  # Q=0 vector double FMOV immediate is reserved
        0x1EA04000,  # reserved FMOV register ftype
        0x1EE04000,  # FP16 is not part of this implementation profile
        0x1E660000,  # mismatched 32-bit GPR and double FMOV
        0x9B400000,  # SMULH Ra reserved bits are not all ones
        0xFFFFFFFF,
    ]
    for word in rejected:
        result = request({"arch": "arm64", "bytes": word.to_bytes(4, "little").hex(), "address": hex(CODE), "slots": {}})
        require(not result["supported"], f"Reserved/unmodeled encoding accepted: {word:08x}")
    fuzz_rng = random.Random(SEED ^ 0xBAD)
    fuzz_groups = (
        ("all-bits", 0, 0xFFFFFFFF),
        ("extract", 0x13800000, 0xE07FFFFF),
        ("conditional-compare", 0x3A400000, 0xC0FFFFFF),
        ("conditional-select", 0x1A800000, 0xE07FFFFF),
        ("extended-addsub", 0x0B200000, 0xE0DFFFFF),
        ("multiply", 0x1B000000, 0xE0FFFFFF),
        ("carry-addsub", 0x1A000000, 0xE0FFFFFF),
        ("simd-copy", 0x0E000400, 0x71FFFFFF),
        ("simd-immediate", 0x0F000400, 0x70FFFFFF),
        ("simd-three-registers", 0x0E200400, 0x71FFFFFF),
        ("fmov", 0x1E200000, 0x80FFFFFF),
        ("multiply-long-high", 0x9B000000, 0x00FFFFFF),
    )
    fuzz_counts = collections.Counter()
    counterexamples = []
    def random_classification_words():
        for index in range(args.fuzz_words):
            group, base, variable_mask = fuzz_groups[index % len(fuzz_groups)]
            yield group, base | (fuzz_rng.getrandbits(32) & variable_mask)

    random_words = random_classification_words()
    for group, word in itertools.chain(random_words, classification_boundaries()):
        raw = word.to_bytes(4, "little")
        result = request({"arch": "arm64", "bytes": raw.hex(), "address": hex(CODE), "evaluate": False})
        fuzz_counts[group] += 1
        if result["supported"]:
            fuzz_counts["product_supported"] += 1
            decoded = list(decoder.disasm(raw, CODE))
            if len(decoded) != 1:
                counterexamples.append({"word": f"0x{word:08X}", "bytes": raw.hex(), "group": group, "product": result})
    classification_words = sum(value for key, value in fuzz_counts.items() if key != "product_supported")
    classification = {"seed": SEED ^ 0xBAD, "words": classification_words, "random_words": args.fuzz_words, "counts": dict(fuzz_counts), "supported_but_capstone_invalid": counterexamples, "scope": "Decoder disagreement inventory; any counterexample requires ISA review before attributing an error to the lifter or decoder", "capstone": capstone.__version__}
    classification_path = args.output.with_name(args.output.stem + "-classification.json")
    classification_path.parent.mkdir(parents=True, exist_ok=True)
    classification_path.write_text(json.dumps(classification, indent=2) + "\n", encoding="utf-8")
    child.stdin.close()
    require(child.wait() == 0, "Product CLI failed")
    summary = {"seed": SEED, "cases": sum(counts.values()), "families": dict(sorted(counts.items())), "rules": sorted(forms), "roundtrip_families": sorted(roundtrips), "rejected_cases": len(rejected), "classification_words": classification_words, "classification_disagreements": len(counterexamples), "capstone": capstone.__version__, "unicorn": unicorn.__version__, "scope": "Product MIR interpreter versus independent emulator; synthetic single instructions, mapped memory and normal outcomes; not hardware, game, fault, weak-memory or whole-program proof"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
