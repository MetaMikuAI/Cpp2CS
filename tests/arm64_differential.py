"""真实 ARM64 规则 → MIR → 解释器，与 Unicorn 的独立单指令对照。"""

import argparse
import collections
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


def corpus_random_templates():
    yield "random.add-immediate", 0x91000000, 0x607FFFFF
    yield "random.add-shifted", 0x8B000000, 0x605FFFFF
    yield "random.logical", 0x8A000000, 0x60FFFFFF
    yield "random.bitfield", 0xD3400000, 0x003FFFFF
    yield "random.move", 0xD2800000, 0x007FFFFF


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
        variations = range(16) if condition_family else range(8 if family == "addsub.carry" else 4 if not memory_case else 2)
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
            machine.reg_write(arm.UC_ARM64_REG_FPCR, 0)
            machine.reg_write(arm.UC_ARM64_REG_FPSR, 0)
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
    )
    fuzz_counts = collections.Counter()
    counterexamples = []
    for index in range(args.fuzz_words):
        group, base, variable_mask = fuzz_groups[index % len(fuzz_groups)]
        word = base | (fuzz_rng.getrandbits(32) & variable_mask)
        raw = word.to_bytes(4, "little")
        result = request({"arch": "arm64", "bytes": raw.hex(), "address": hex(CODE), "evaluate": False})
        fuzz_counts[group] += 1
        if result["supported"]:
            fuzz_counts["product_supported"] += 1
            decoded = list(decoder.disasm(raw, CODE))
            if len(decoded) != 1:
                counterexamples.append({"word": f"0x{word:08X}", "bytes": raw.hex(), "group": group, "product": result})
    classification = {"seed": SEED ^ 0xBAD, "words": args.fuzz_words, "counts": dict(fuzz_counts), "supported_but_capstone_invalid": counterexamples, "scope": "Decoder disagreement inventory; any counterexample requires ISA review before attributing an error to the lifter or decoder", "capstone": capstone.__version__}
    classification_path = args.output.with_name(args.output.stem + "-classification.json")
    classification_path.parent.mkdir(parents=True, exist_ok=True)
    classification_path.write_text(json.dumps(classification, indent=2) + "\n", encoding="utf-8")
    child.stdin.close()
    require(child.wait() == 0, "Product CLI failed")
    summary = {"seed": SEED, "cases": sum(counts.values()), "families": dict(sorted(counts.items())), "rules": sorted(forms), "roundtrip_families": sorted(roundtrips), "rejected_cases": len(rejected), "classification_words": args.fuzz_words, "classification_disagreements": len(counterexamples), "capstone": capstone.__version__, "unicorn": unicorn.__version__, "scope": "Product MIR interpreter versus independent emulator; synthetic single instructions, mapped memory and normal outcomes; not hardware, game, fault, weak-memory or whole-program proof"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
