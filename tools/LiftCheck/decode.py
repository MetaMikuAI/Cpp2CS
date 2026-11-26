"""按指令字复用反汇编，计数按 FDE 中的实际出现次数展开。"""
import argparse
from collections import Counter
from pathlib import Path
from itertools import islice
import re
import struct

from capstone import Cs, CS_ARCH_ARM64, CS_MODE_ARM

IMM = re.compile(r"#(-?0x[0-9a-f]+|-?[0-9]+)(?![.0-9a-z])")
REG = re.compile(r"\b(fp|lr)\b")


def normalize(text):
    text = REG.sub(lambda m: "x29" if m[0] == "fp" else "x30", text)
    text = IMM.sub(lambda m: "#" + str(int(m[1], 0)), text).strip()
    # 回写偏移按 64 位补码显示。逻辑立即数按目标寄存器宽度显示位型。
    if "], #" in text:
        prefix, imm = text.rsplit("#", 1)
        value = int(imm)
        if (1 << 63) <= value < (1 << 64):
            text = prefix + "#" + str(value - (1 << 64))
    elif text.startswith(("tst ", "ands ", "and ", "eor ", "orr ")) and ", #" in text:
        prefix, imm = text.rsplit("#", 1)
        width = 32 if text.split()[1].startswith("w") else 64
        value = int(imm)
        if -(1 << (width - 1)) <= value < 0:
            text = prefix + "#" + str(value + (1 << width))
    return text


def decoded_rows(cs, source):
    origin = 1 << 32
    cs.skipdata = True
    while lines := list(islice(source, 2048)):
        rows = [line.rstrip("\n").split("\t") for line in lines]
        code = struct.pack(f"<{len(rows)}I", *(int(row[0], 16) for row in rows))
        for j, (row, insn) in enumerate(zip(rows, cs.disasm_lite(code, origin), strict=True)):
            pc, size, name, operands = insn
            if pc != origin + 4 * j or size != 4:
                raise ValueError("反汇编没有按 A64 指令字对齐")
            if name == ".byte":
                yield *row, None, "?"
                continue
            # 分批反汇编时每个字的 PC 不同。只平移架构定义为 PC 相对的地址操作数。
            relative = name in ("b", "bl", "cbz", "cbnz", "tbz", "tbnz", "adr", "adrp") or name.startswith("b.")
            literal = name in ("ldr", "ldrsw", "prfm") and "[" not in operands and ", #" in operands
            if relative or literal:
                leading, sep, immediate = operands.rpartition("#")
                if not sep:
                    raise ValueError("PC 相对目标缺少立即数")
                basis = pc & ~4095 if name == "adrp" else pc
                operands = leading + "#" + hex((int(immediate, 0) + origin - basis) % (1 << 64))
            yield *row, name, (name + " " + operands).strip()


def compare(prefix):
    path = lambda suffix: Path(prefix + suffix)
    cs = Cs(CS_ARCH_ARM64, CS_MODE_ARM)
    totals, mnemonics, rejected = Counter(), {}, Counter()
    with path(".words.local.tsv").open() as words, path(".differences.local.tsv").open("w") as differences:
        for word, count, ours, mnemonic, reference in decoded_rows(cs, words):
            code, count = int(word, 16), int(count)
            if ours != "?" and ours == reference:
                totals["一致"] += count
                continue
            reference = normalize(reference)
            ours = normalize(ours)
            if ours == "?":
                category = "双方未解码" if mnemonic is None else "前端未解码"
                mnemonics[code] = mnemonic or "?"
            elif mnemonic is None:
                category = "Capstone 未解码"
            elif reference == ours:
                category = "一致"
            elif ours.startswith("mov ") and reference.startswith("mov ") and ", #" in ours and ", #" in reference:
                bits = 32 if ours.startswith("mov w") else 64
                reg, value = ours.split(", #")
                other, other_value = reference.split(", #")
                category = "一致" if reg == other and (int(value) - int(other_value)) % (1 << bits) == 0 else "操作数"
            else:
                category = "操作数" if reference.split()[0] == ours.split()[0] else "助记符"
            totals[category] += count
            if category != "一致":
                differences.write(f"{word}\t{count}\t{category}\t{ours}\t{reference}\n")
    with path(".unknown.local.bin").open("rb") as source:
        while raw := source.read(4):
            count, = struct.unpack("<I", raw)
            words = struct.unpack(f"<{count}I", source.read(count * 4))
            rejected.update({mnemonics[word] for word in words})
    with path(".decode.local.tsv").open("w") as out:
        for category, count in totals.most_common():
            print(category, count, sep="\t", file=out)
    with path(".unsupported.local.tsv").open("w") as out:
        for mnemonic, count in sorted(rejected.items(), key=lambda item: (-item[1], item[0])):
            print(mnemonic, count, sep="\t", file=out)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("prefix", nargs="+")
    for prefix in parser.parse_args().prefix:
        compare(prefix)
