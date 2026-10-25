"""从映像的托管代码节（il2cpp）按助记符分层抽取指令字，生成 arm64_oracle.py 的输入。

用法: python -I sample_words.py <libil2cpp.so> <输出.txt> [每个助记符的基础配额]
每个助记符取出现次数最多的若干个不同指令字，再按固定种子随机补足；配额随该助记符的不同指令字数增长。
每个指令字用它在映像中第一次出现的地址作 pc（adr/adrp/分支的结果依赖 pc），各配一个奇数、一个偶数 seed。
"""
import random
import sys
from collections import Counter, defaultdict

import capstone
import numpy as np
from elftools.elf.elffile import ELFFile


def main():
    path, out_path = sys.argv[1], sys.argv[2]
    base = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    with open(path, 'rb') as f:
        elf = ELFFile(f)
        section = elf.get_section_by_name('il2cpp')
        address = section['sh_addr']
        words = np.frombuffer(section.data(), dtype='<u4')

    counts = Counter(words.tolist())
    unique, first = np.unique(words, return_index=True)
    first_pc = {int(w): address + 4 * int(i) for w, i in zip(unique, first)}

    cs = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM)
    by_mnemonic = defaultdict(list)
    for word in counts:
        insn = next(cs.disasm(word.to_bytes(4, 'little'), first_pc[word]), None)
        by_mnemonic[insn.mnemonic if insn else '(invalid)'].append(word)

    rng = random.Random(10)
    lines = []
    for mnemonic in sorted(by_mnemonic):
        group = sorted(by_mnemonic[mnemonic], key=lambda w: -counts[w])
        quota = min(len(group), base + int(len(group) ** 0.5) * 2)
        chosen = group[:quota // 2]
        rest = group[quota // 2:]
        chosen += rng.sample(rest, min(len(rest), quota - len(chosen)))
        for word in chosen:
            for seed in (2 * rng.randrange(1 << 20) + 1, 2 * rng.randrange(1 << 20)):
                lines.append(f'{first_pc[word]:x} {word:08x} {seed}\n')

    with open(out_path, 'w') as out:
        out.writelines(lines)
    print(f'{len(counts)} 个不同指令字，{len(by_mnemonic)} 个助记符，抽取 {len(lines)} 行')


main()
