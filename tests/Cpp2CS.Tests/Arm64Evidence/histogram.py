"""从定向检查输出的编码计数生成独立反汇编的助记符直方图。"""
import collections
import json
import struct
import sys
import capstone
cs = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_LITTLE_ENDIAN)
counts = collections.Counter()
with open(sys.argv[1]) as stream:
    for item in json.load(stream):
        decoded = list(cs.disasm(struct.pack('<I', item['word']), 0))
        counts[item['category'], decoded[0].mnemonic if decoded else 'unallocated'] += item['count']
for (category, mnemonic), count in sorted(counts.items(), key=lambda p: (-p[1], p[0])):
    print(f'{category}\t{mnemonic}\t{count}')
