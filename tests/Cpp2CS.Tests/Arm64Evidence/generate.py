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

def instruction(group, word, expected, index, memory=False, branch=False, divide=False, fp=0, result=0, lanes=1, low=0, packed=False, integer=0):
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
    if integer:
        # 有符号边界、无符号高位与浮点有效位宽边界上的平局。
        precision = 24 if integer == 32 else 53
        values = [0, (1 << integer)-1, 1 << (integer-1), (1 << (integer-1))-1,
                  1, (1 << precision)+1, (1 << precision)+3]
        for j, r in enumerate(Q):
            u.reg_write(r, sum(values[(index+j+lane) % len(values)] << (lane*integer) for lane in range(128 // integer)))
        u.reg_write(reg.UC_ARM64_REG_FPCR, 0)
        u.reg_write(reg.UC_ARM64_REG_FPSR, 0)
    if fp:
        import math
        values = [0.0, -0.0, 1.0, -1.0, math.inf, -math.inf, math.nan,
                  0.5, -0.5, 1.5, 2.5, -2.5, 2.0**31, -2.0**31,
                  2.0**32, 2.0**63, -2.0**63, 2.0**64]
        pack = '<f' if fp == 32 else '<d'
        edges = [int.from_bytes(struct.pack(pack, v), 'little') for v in values]
        edges += [1, (1 << (fp - 1)) | 1, 0x7f800001 if fp == 32 else 0x7ff0000000000001,
                  0x007fffff if fp == 32 else 0x000fffffffffffff,
                  0x00800000 if fp == 32 else 0x0010000000000000]
        for j, r in enumerate(Q):
            bits = edges[(index + j) % len(edges)] if index < len(edges) * 2 else state_random.getrandbits(fp)
            if packed:
                bits = sum(edges[(index + j + lane) % len(edges)] << (lane * fp) for lane in range(128 // fp))
                u.reg_write(r, bits)
            else:
                u.reg_write(r, (state_random.getrandbits(128 - fp) << fp) | bits)
        u.reg_write(reg.UC_ARM64_REG_FPCR, 0)
        u.reg_write(reg.UC_ARM64_REG_FPSR, 0)
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
                      accesses=accesses, next=u.reg_read(reg.UC_ARM64_REG_PC), trap=bool(trapped), float_result=result, float_lanes=lanes, float_low=low))

def fields(i):
    # 保留独立源；覆盖零寄存器与栈指针另用专门模板。
    return (R.randrange(0, 29), R.randrange(0, 29), R.randrange(0, 29))

def floating_cases():
    # 所有源寄存器独立；完整高位带随机值，验证标量写入清零。
    for i in range(48):
        for typ in (0, 1):
            width = 32 << typ
            base = 0x1e200000 | (typ << 22) | (1 << 5)
            for opcode, name in enumerate(('fmul', 'fdiv', 'fadd', 'fsub', 'fmax', 'fmin', 'fmaxnm', 'fminnm', 'fnmul')):
                instruction('float-binary', base | 0x800 | (2 << 16) | (opcode << 12), name, i, fp=width, result=width)
            for opcode, name in ((0, 'fmov'), (1, 'fabs'), (2, 'fneg'), (3, 'fsqrt'), (8, 'frintn'), (9, 'frintp'), (10, 'frintm'), (11, 'frintz'), (14, 'frintx'), (15, 'frinti')):
                instruction('float-unary', base | 0x4000 | (opcode << 15), name, i, fp=width, result=width if opcode >= 3 else 0)
            instruction('float-convert', base | 0x4000 | ((5 - typ) << 15), 'fcvt', i, fp=width, result=64 >> typ)
            instruction('float-immediate', 0x1e201000 | (typ << 22) | ((i * 5 % 256) << 13), 'fmov', i)
            for negate in (0, 1):
                for subtract in (0, 1):
                    instruction('float-fused', 0x1f000000 | (typ << 22) | (negate << 21) | (2 << 16) | (subtract << 15) | (3 << 10) | (1 << 5), 'fmadd fmsub fnmadd fnmsub', i, fp=width, result=width)
            for signal in (0, 1):
                for zero in (0, 1):
                    instruction('float-compare', base | 0x2000 | ((0 if zero else 2) << 16) | (zero << 3) | (signal << 4), 'fcmp fcmpe', i, fp=width)
                instruction('float-conditional-compare', base | 0x400 | (2 << 16) | ((i % 16) << 12) | (signal << 4) | (i % 16), 'fccmp fccmpe', i, fp=width)
            instruction('float-select', base | 0xc00 | (2 << 16) | ((i % 16) << 12), 'fcsel', i, fp=width)
            for sf in (0, 1):
                for unsigned in (0, 1):
                    instruction('integer-to-float', base | (sf << 31) | ((2 + unsigned) << 16), 'scvtf ucvtf', i, fp=width, result=width)
                    for rounding in range(4):
                        instruction('float-to-integer', base | (sf << 31) | (unsigned << 16) | (rounding << 19), 'fcvtns fcvtnu fcvtps fcvtpu fcvtms fcvtmu fcvtzs fcvtzu', i, fp=width)
            for opcode in (6, 7):
                instruction('float-bit-move', base | (typ << 31) | (opcode << 16), 'fmov', i, fp=width)
        for op in (0x9eae0020, 0x9eaf0020):
            instruction('float-bit-move', op, 'fmov', i)
    for i in range(16):
        for q in (0, 1):
            instruction('vector-register-move', 0x0ea11c20 | (q << 30), 'mov', i)
            for mode in range(16):
                for op in (0, 1):
                    if mode == 15 and op and not q: continue
                    imm = [0, 255, 128, 1, 85, 170][i % 6]
                    word = 0x0f000400 | (q << 30) | (op << 29) | (mode << 12) | ((imm >> 5) << 16) | ((imm & 31) << 5)
                    instruction('vector-immediate', word, 'movi mvni orr bic fmov', i)
            for size in range(4):
                bits = 8 << size
                lane = i % (128 // bits)
                imm = (lane << (size + 1)) | (1 << size)
                if size < 3 or q:
                    instruction('vector-duplicate', 0x0e000400 | (q << 30) | (imm << 16) | (1 << 5), 'dup', i)
                    instruction('vector-duplicate', 0x0e000c00 | (q << 30) | ((1 << size) << 16) | (1 << 5), 'dup', i)
                if (q and size == 3) or (not q and size < 3):
                    instruction('vector-extract', 0x0e003c00 | (q << 30) | (imm << 16) | (1 << 5), 'umov mov', i)
                if bits < (64 if q else 32):
                    instruction('vector-extract', 0x0e002c00 | (q << 30) | (imm << 16) | (1 << 5), 'smov', i)
                if q:
                    instruction('vector-insert', 0x4e001c20 | (imm << 16), 'mov ins', i)
                    instruction('vector-insert', 0x6e000420 | (imm << 16) | ((lane << size) << 11), 'mov ins', i)
                    instruction('vector-scalar-duplicate', 0x5e000420 | (imm << 16), 'mov dup', i)
            for widen in (0, 1):
                instruction('vector-float-convert', (0x0e617820 if widen else 0x0e616820) | (q << 30), 'fcvtl fcvtl2 fcvtn fcvtn2', i,
                            fp=32 if widen else 64, result=64 if widen else 32, lanes=2, low=64 if q and not widen else 0)
            for size in range(3):
                instruction('vector-narrow', 0x0e212820 | (q << 30) | (size << 22), 'xtn xtn2', i)
                for unsigned in (0, 1):
                    bits = 8 << size
                    instruction('vector-widen', 0x0f00a420 | (q << 30) | (unsigned << 29) | ((bits + i % bits) << 16), 'sshll sshll2 ushll ushll2 sxtl sxtl2 uxtl uxtl2', i)

def vector_cases():
    # Arm 编码类：二寄存器杂项、三操作数同型、按元素、提取、归约、单结构访存。
    for i in range(12):
        for q, sz in ((0, 0), (1, 0), (1, 1)):
            bits = 32 << sz
            lanes = (64 << q) // bits
            for u in (0, 1):
                instruction('vector-integer-float', 0x0e21d820 | (q << 30) | (u << 29) | (sz << 22),
                            'scvtf ucvtf', i, result=bits, lanes=lanes, integer=bits)
            instruction('vector-absolute', 0x0ea0f820 | (q << 30) | (sz << 22), 'fabs', i, fp=bits, packed=True)
            for u, size, opcode, name in ((0, sz, 0x1a, 'fadd'), (0, sz+2, 0x1a, 'fsub'),
                                          (1, sz, 0x1b, 'fmul'), (1, sz, 0x1f, 'fdiv'), (1, sz+2, 0x1a, 'fabd')):
                instruction('vector-float-binary', 0x0e220420 | (q << 30) | (u << 29) | (size << 22) | (opcode << 11),
                            name, i, fp=bits, result=bits, lanes=lanes, packed=True)
        for sz in (0, 1):
            bits = 32 << sz
            for u in (0, 1):
                instruction('vector-scalar-integer-float', 0x5e21d820 | (u << 29) | (sz << 22), 'scvtf ucvtf', i, result=bits, integer=bits)
            instruction('vector-scalar-absolute-difference', 0x7ea2d420 | (sz << 22), 'fabd', i, fp=bits, result=bits, packed=True)
        for scalar, q, size in ((0, 0, 2), (0, 1, 2), (0, 1, 3), (1, 1, 2), (1, 1, 3)):
            bits = 32 << (size & 1)
            for lane in range(128 // bits):
                h, l = (lane >> 1, lane & 1) if bits == 32 else (lane, 0)
                instruction('vector-float-element', 0x0f129020 | (scalar << 28) | (q << 30) | (size << 22) | (h << 11) | (l << 21),
                            'fmul', i, fp=bits, result=bits, lanes=1 if scalar else (64 << q) // bits, packed=True)
        for q in (0, 1):
            for size in range(3):
                instruction('vector-reverse', 0x0e200820 | (q << 30) | (size << 22), 'rev64', i)
            for offset in (0, (8 << q)-1):
                instruction('vector-concatenate-extract', 0x2e020020 | (q << 30) | (offset << 11), 'ext', i)
            for size in range(4):
                if size == 3 and q == 0: continue
                for u in (0, 1):
                    instruction('vector-integer-binary', 0x0e228420 | (q << 30) | (u << 29) | (size << 22), 'add sub', i)
                if size == 3:
                    instruction('vector-integer-binary', 0x4ee23420, 'cmgt', i)
                    continue
                for opcode, name in ((0x13, 'mul'), (0xc, 'smax'), (0xd, 'smin'), (0x6, 'cmgt')):
                    instruction('vector-integer-binary', 0x0e220420 | (q << 30) | (size << 22) | (opcode << 11), name, i)
                if size != 2 or q:
                    instruction('vector-integer-reduction', 0x0e31b820 | (q << 30) | (size << 22), 'addv', i)
            for scale in range(4):
                lane = i % (8 >> scale)
                opcode, sf, size = ((0, lane >> 2, lane & 3) if scale == 0 else
                                    (2, lane >> 1, (lane & 1) << 1) if scale == 1 else
                                    (4, lane, 0) if scale == 2 else (4, 0, 1))
                for load in (0, 1):
                    for post, m in ((0, 0), (1, 31), (1, 2)):
                        instruction('vector-lane-memory', 0x0d000020 | (q << 30) | (post << 23) | (load << 22) | (m << 16) | (opcode << 13) | (sf << 12) | (size << 10),
                                    'ld1 st1', i, memory=True)
                for post, m in ((0, 0), (1, 31), (1, 2)):
                    instruction('vector-replicate-memory', 0x0d40c020 | (q << 30) | (post << 23) | (m << 16) | (scale << 10), 'ld1r', i, memory=True)
        for sf, typ, scale in ((0, 0, 54), (0, 1, 32), (1, 0, 0), (1, 1, 63)):
            instruction('float-fixed-integer', 0x1e180020 | (sf << 31) | (typ << 22) | (scale << 10), 'fcvtzs', i, fp=32 << typ)

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
    floating_cases()
    vector_cases()
    document = dict(schema=1, generator_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                    capstone=capstone.__version__, unicorn=unicorn.__version__, python=sys.version.split()[0], zlib=zlib.ZLIB_VERSION, cases=CASES)
    payload = json.dumps(document, sort_keys=True, separators=(',', ':')).encode()
    output = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path(__file__).with_name('evidence.json.gz')
    output.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    print(json.dumps(dict(cases=len(CASES), compressed=output.stat().st_size, sha256=hashlib.sha256(output.read_bytes()).hexdigest())))

if __name__ == '__main__': main()
