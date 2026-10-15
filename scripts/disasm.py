"""反汇编辅助：python disasm.py <binary> <va> [count]。只用于人工查看代码形态。"""
import struct, sys
import capstone

def segments(data):
    if data[:4] == b'\x7fELF':
        phoff, = struct.unpack_from('<Q', data, 0x20)
        phentsize, phnum = struct.unpack_from('<HH', data, 0x36)
        for i in range(phnum):
            p_type, flags, off, va, pa, filesz, memsz, align = struct.unpack_from('<IIQQQQQQ', data, phoff + i * phentsize)
            if p_type == 1: yield va, off, filesz
        return
    pe = struct.unpack_from('<I', data, 0x3c)[0]
    nsec, = struct.unpack_from('<H', data, pe + 6)
    optsize, = struct.unpack_from('<H', data, pe + 20)
    base, = struct.unpack_from('<Q', data, pe + 24 + 24)
    sec = pe + 24 + optsize
    for i in range(nsec):
        vsize, va, rawsize, raw = struct.unpack_from('<IIII', data, sec + i * 40 + 8)
        yield base + va, raw, rawsize

def main():
    path, va, count = sys.argv[1], int(sys.argv[2], 16), int(sys.argv[3]) if len(sys.argv) > 3 else 80
    data = open(path, 'rb').read()
    for start, off, size in segments(data):
        if start <= va < start + size:
            code = data[off + va - start: off + va - start + count * 15]
            break
    else:
        raise SystemExit('地址不在映射段内')
    arm = data[:4] == b'\x7fELF'
    md = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM) if arm else capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    for n, ins in enumerate(md.disasm(code, va)):
        if n >= count: break
        print(f'{ins.address:x}: {ins.mnemonic} {ins.op_str}')

main()
