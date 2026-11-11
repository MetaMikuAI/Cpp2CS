"""固定种子的单指令证据；在仓库外的虚拟环境中安装 requirements.txt 后运行。"""
import gzip
import hashlib
import json
import pathlib
import random
import struct
import sys
import zlib
import capstone
import unicorn
from unicorn import arm64_const as reg

PC = 0x100000
DATA = 0x200000
MASK = (1 << 64) - 1
R = random.Random(0xA64C21A)
CS = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_LITTLE_ENDIAN)
X = [getattr(reg, f'UC_ARM64_REG_X{i}') for i in range(31)] + [reg.UC_ARM64_REG_SP]
Q = [getattr(reg, f'UC_ARM64_REG_Q{i}') for i in range(32)]
BOUNDARY = [0, MASK, 1 << 63, (1 << 63) - 1, 1, 31, 32, 63, 64, 65, 0x80000000, 0x7fffffff]
CASES = []

def instruction(group, word, expected, index, memory=False, branch=False, divide=False):
    encoded = struct.pack('<I', word)
    decoded = list(CS.disasm(encoded, PC))
    if len(decoded) != 1 or decoded[0].mnemonic not in expected.split():
        raise AssertionError((group, hex(word), [(d.mnemonic, d.op_str) for d in decoded], expected))
    u = unicorn.Uc(unicorn.UC_ARCH_ARM64, unicorn.UC_MODE_ARM)
    u.mem_map(PC - 0x10000, 0x30000)
    u.mem_map(DATA, 0x10000)
    u.mem_write(PC, encoded)
    content = R.randbytes(0x10000)
    u.mem_write(DATA, content)
    state_random = random.Random(0x640000 + index)
    for i, r in enumerate(X):
        value = BOUNDARY[(index + i) % len(BOUNDARY)] if index < len(BOUNDARY) else state_random.getrandbits(64)
        u.reg_write(r, value)
    for r in Q:
        u.reg_write(r, state_random.getrandbits(128))
    u.reg_write(reg.UC_ARM64_REG_NZCV, (index % 16) << 28)
    u.reg_write(reg.UC_ARM64_REG_TPIDR_EL0, DATA + 0x1230)
    if memory:
        u.reg_write(X[(word >> 5) & 31], DATA + 0x8000)
        if (word & 0x3b200c00) == 0x38200800:
            u.reg_write(X[(word >> 16) & 31], [0, 1, 7, 0xffffffffffffffff][index % 4])
            # 无符号窄索引不取负值。
            if ((word >> 13) & 7) == 2:
                u.reg_write(X[(word >> 16) & 31], index % 8)
    if branch and (word & 0xfe000000) == 0xd6000000:
        u.reg_write(X[(word >> 5) & 31], PC + 0x100)
    if divide:
        a, b = [(0, 0), (1 << 63, MASK), (0x80000000, 0xffffffff), (MASK, 0), (MASK, 1), (1, MASK)][index % 6]
        if index < 12:
            u.reg_write(X[(word >> 5) & 31], a)
            u.reg_write(X[(word >> 16) & 31], b)
    def snapshot():
        return [str(u.reg_read(r)) for r in X + Q] + [str((u.reg_read(reg.UC_ARM64_REG_NZCV) >> bit) & 1) for bit in (31, 30, 29, 28)]
    before = snapshot()
    accesses = []
    trapped = []
    def access(uc, kind, address, size, value, _):
        if kind == unicorn.UC_MEM_READ:
            accesses.append(['read', str(address), size * 8, str(int.from_bytes(uc.mem_read(address, size), 'little'))])
        else:
            accesses.append(['write', str(address), size * 8, str(value & ((1 << (size * 8)) - 1))])
    def interrupt(uc, number, _):
        trapped.append(number)
        uc.emu_stop()
    u.hook_add(unicorn.UC_HOOK_MEM_READ | unicorn.UC_HOOK_MEM_WRITE, access)
    u.hook_add(unicorn.UC_HOOK_INTR, interrupt)
    u.emu_start(PC, PC + 4, count=1)
    # SIMD 的 128 位访问在模拟器中可能分成两个 64 位钩子；保存原始事件，检查端按字节比较。
    CASES.append(dict(group=group, word=word, mnemonic=decoded[0].mnemonic, before=before, after=snapshot(),
                      accesses=accesses, next=u.reg_read(reg.UC_ARM64_REG_PC), trap=bool(trapped)))

def fields(i):
    # 保留独立源；覆盖零寄存器与栈指针另用专门模板。
    return (R.randrange(0, 29), R.randrange(0, 29), R.randrange(0, 29))

def main():
    for i in range(24):
        d, n, m = fields(i)
        for sf in (0, 1):
            w = 32 << sf
            common = (sf << 31) | (n << 5) | d
            for sub in (0, 1):
                for flags in (0, 1):
                    prefix = common | (sub << 30) | (flags << 29)
                    instruction('add-immediate', prefix | 0x11000000 | (R.randrange(4096) << 10) | ((i % 2) << 22), 'add adds sub subs cmp cmn', i)
                    instruction('add-shifted', prefix | 0x0b000000 | (m << 16) | ((i % 3) << 22) | (([0, 1, w - 1, w // 2][i % 4]) << 10), 'add adds sub subs cmp cmn neg negs', i)
                    instruction('add-extended', prefix | 0x0b200000 | (m << 16) | ((i % 8) << 13) | ((i % 5) << 10), 'add adds sub subs cmp cmn', i)
                    instruction('add-carry', prefix | 0x1a000000 | (m << 16), 'adc adcs sbc sbcs ngc ngcs', i)
            for opc in range(4):
                instruction('logical-shifted', common | 0x0a000000 | (opc << 29) | (m << 16) | ((i % 4) << 22) | ((i % 2) << 21) | (([0, 1, w - 1, w // 2][i % 4]) << 10), 'and orr eor ands bic orn eon bics mov mvn tst', i)
                # 元素宽为操作数宽；同时有全零/全一以外的所有连续一长度。
                instruction('logical-immediate', common | 0x12000000 | (opc << 29) | (sf << 22) | (([0, 1, w - 1, w // 2][i % 4]) << 16) | ((i % (w-1)) << 10), 'and orr eor ands mov tst', i)
                instruction('conditional-select', common | 0x1a800000 | ((opc >> 1) << 30) | ((opc & 1) << 10) | (m << 16) | ((i % 16) << 12), 'csel csinc csinv csneg cinc cinv cneg cset csetm', i)
            for opc in (0, 2, 3):
                instruction('wide-move', (sf << 31) | 0x12800000 | (opc << 29) | (R.randrange(1 << 16) << 5) | ((i % (w // 16)) << 21) | d, 'mov movk movn movz', i)
            for opc in range(3):
                instruction('bitfield', common | 0x13000000 | (opc << 29) | (sf << 22) | (([0, 1, w - 1, w // 2][i % 4]) << 16) | (R.randrange(w) << 10), 'sbfm bfm ubfm bfi bfxil sbfx ubfx sbfiz ubfiz asr lsr lsl sxtb sxth sxtw uxtb uxth', i)
            instruction('extract', common | 0x13800000 | (sf << 22) | (m << 16) | (([0, 1, w - 1, w // 2][i % 4]) << 10), 'extr ror', i)
            for sub in (0, 1):
                for immediate in (0, 1):
                    instruction('conditional-compare', (sf << 31) | 0x3a400000 | (sub << 30) | (n << 5) | (m << 16) | (immediate << 11) | ((i % 16) << 12) | (i % 16), 'ccmn ccmp', i)
            for opcode in (2, 3, 8, 9, 10, 11):
                instruction('divide' if opcode < 8 else 'variable-shift', common | 0x1ac00000 | (m << 16) | (opcode << 10), 'udiv sdiv lsl lsr asr ror', i, divide=opcode < 8)
            for opcode in range(6):
                if opcode == 3 and not sf: continue
                instruction('one-source', common | 0x5ac00000 | (opcode << 10), 'rbit rev16 rev32 rev clz cls', i)
            for sub in (0, 1):
                instruction('multiply-add', common | 0x1b000000 | (m << 16) | (R.randrange(32) << 10) | (sub << 15), 'madd msub mul mneg', i)
        for opcode in (1, 5, 2, 6):
            high = opcode in (2, 6)
            instruction('multiply-high' if high else 'multiply-long', 0x9b000000 | (opcode << 21) | (m << 16) | ((31 if high else R.randrange(32)) << 10) | ((0 if high else i % 2) << 15) | (n << 5) | d, 'smaddl smsubl umaddl umsubl smull smnegl umull umnegl smulh umulh', i)
        for page in (0, 1):
            instruction('pc-relative', 0x10000000 | (page << 31) | (R.randrange(4) << 29) | (R.randrange(1 << 19) << 5) | d, 'adr adrp', i)
        for link in (0, 1):
            instruction('branch-link' if link else 'branch', 0x14000000 | (link << 31) | (R.randrange(128) - 64 & 0x3ffffff), 'b bl', i, branch=True)
        instruction('branch-condition', 0x54000000 | ((R.randrange(128)-64 & 0x7ffff) << 5) | (i % 16), 'b.eq b.ne b.hs b.lo b.mi b.pl b.vs b.vc b.hi b.ls b.ge b.lt b.gt b.le b.al b.nv', i, branch=True)
        for test in (False, True):
            word = (0x36000000 | (R.randrange(64) << 19)) if test else 0x34000000
            word |= (i % 2) << 24 | ((R.randrange(128)-64 & 0x3fff) << 5) | d | ((i % 2) << 31)
            instruction('test-branch' if test else 'compare-branch', word, 'tbz tbnz cbz cbnz', i, branch=True)
        for op, name in ((0xd61f0000, 'br'), (0xd63f0000, 'blr'), (0xd65f0000, 'ret')):
            instruction('register-' + name, op | ((30 if name == 'ret' and i % 2 == 0 else n) << 5), name, i, branch=True)
        instruction('thread-pointer', 0xd53bd040 | d, 'mrs', i)
        instruction('hint', 0xd503201f | ((i % 6) << 5), 'nop yield wfe wfi sev sevl', i)
        instruction('trap', (0xd4200000 if i % 2 else 0xd4400000) | (R.randrange(1 << 16) << 5), 'brk hlt', i)
        for vec in (0, 1):
            for size in range(4):
                for opc in range(4):
                    if vec and opc >= 2 and size != 0: continue
                    if not vec and (opc == 3 and size >= 2 or opc == 2 and size == 3): continue
                    base = (size << 30) | (vec << 26) | (opc << 22) | (31 << 5) | d
                    for mode in ('unsigned', 'unscaled', 'pre', 'post', 'register'):
                        if mode == 'unsigned': word = base | 0x39000000 | (R.randrange(32) << 10)
                        elif mode == 'register': word = base | 0x38200800 | (30 << 16) | ([2, 3, 6, 7][i % 4] << 13) | ((i % 2) << 12)
                        else: word = base | 0x38000000 | ((R.randrange(64)-32 & 511) << 12) | ({'unscaled': 0, 'pre': 3, 'post': 1}[mode] << 10)
                        instruction(('simd-' if vec else 'integer-') + 'memory-' + mode, word, 'ldr str ldrb strb ldrh strh ldrsb ldrsh ldrsw ldur stur ldurb sturb ldurh sturh ldursb ldursh ldursw', i, memory=True)
            for opc in range(3):
                for load in (0, 1):
                    for mode in range(4):
                        if not vec and opc == 1 and (not load or mode == 0): continue
                        word = 0x28000000 | (vec << 26) | (opc << 30) | (load << 22) | (mode << 23) | ((R.randrange(32)-16 & 127) << 15) | (30 << 10) | (31 << 5) | d
                        instruction(('simd-' if vec else 'integer-') + 'pair', word, 'stp ldp stnp ldnp ldpsw', i, memory=True)
            for opc in range(3):
                # 文字池位于已映射的数据页。
                word = 0x18000000 | (vec << 26) | (opc << 30) | (((DATA + 0x100 - PC) // 4 & 0x7ffff) << 5) | d
                # 正偏移必须小于 1 MiB；使用代码页中的字节作为文字池。
                word = (word & ~0x00ffffe0) | (64 << 5)
                instruction(('simd-' if vec else 'integer-') + 'literal', word, 'ldr ldrsw', i)
    for i in range(24):
        for sf in (0, 1):
            for sub in (0, 1):
                for flags in (0, 1):
                    word = (sf << 31) | 0x11000000 | (sub << 30) | (flags << 29) | (R.randrange(4096) << 10) | (31 << 5) | 31
                    instruction('stack-zero-register', word, 'add sub cmp cmn', i)
            for length in range(1, 6 + sf):
                size = 1 << length
                imms = ((~(size - 1) << 1) & 63) | R.randrange(size - 1)
                word = (sf << 31) | 0x12000000 | ((1 if size == 64 else 0) << 22) | (R.randrange(64) << 16) | (imms << 10) | (31 << 5)
                instruction('logical-replicated', word, 'and', i)
        for size in range(4):
            for opc in range(4):
                if opc == 3 and size >= 2 or opc == 2 and size == 3: continue
                word = (size << 30) | 0x38000800 | (opc << 22) | ((R.randrange(64)-32 & 511) << 12) | (31 << 5) | (i % 29)
                instruction('integer-memory-unprivileged', word, 'ldtr sttr ldtrb sttrb ldtrh sttrh ldtrsb ldtrsh ldtrsw', i, memory=True)
        instruction('prefetch', 0xf98003e0 | (i << 10), 'prfm', i, memory=True)
        instruction('prefetch', 0xf88003e0 | (i << 12), 'prfum', i, memory=True)
        instruction('prefetch', 0xd8000000 | (64 << 5), 'prfm', i)
        instruction('branch-target-hint', 0xd503241f | ((i % 4) << 6), 'bti', i)
    for flags in range(16):
        for condition in range(16):
            instruction('condition-matrix', 0x54000200 | condition, 'b.eq b.ne b.hs b.lo b.mi b.pl b.vs b.vc b.hi b.ls b.ge b.lt b.gt b.le b.al b.nv', flags, branch=True)
            instruction('select-matrix', 0x9a810002 | (condition << 12), 'csel', flags)
            for subtract in (0, 1):
                instruction('compare-matrix', 0xba420025 | (subtract << 30) | (condition << 12), 'ccmp ccmn', flags)
    document = dict(schema=1, generator_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                    capstone=capstone.__version__, unicorn=unicorn.__version__, python=sys.version.split()[0], zlib=zlib.ZLIB_VERSION, cases=CASES)
    payload = json.dumps(document, sort_keys=True, separators=(',', ':')).encode()
    output = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path(__file__).with_name('evidence.json.gz')
    output.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    print(json.dumps(dict(cases=len(CASES), compressed=output.stat().st_size, sha256=hashlib.sha256(output.read_bytes()).hexdigest())))

if __name__ == '__main__': main()
