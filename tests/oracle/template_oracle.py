"""L2 模板等价性测试：在 Unicorn 中执行模板实例的原机器码，按模板语义构造运行时结构的各种取值，核对出口、helper 调用与结果。

用法: python -I template_oracle.py <libil2cpp.so> <template-instances.jsonl> [每个模板的实例上限]
      环境变量 ORACLE_SAMPLES 控制每类结果打印的样例数（默认 3）。
实例由 `cpp2cs idioms` 写出（template-instances.jsonl）：起点（模板在起始块内第一条相关指令）、出口地址、
输入的放置方式（"slot:地址"、"xN"，多个以 "+" 连接；或 {base, offset, width}：对象字段），以及
env（起点处持有常量的寄存器，如 GOT 项）、derived（起点处持有输入对象字段的寄存器）、block 与 path（起始块与唯一前驱链）。

执行环境：映像的 PT_LOAD 段按 VA 映射，RELATIVE 重定位写入（GOT 由此指向槽位）；寄存器先填入不可访问的毒值，
沿前驱链与起始块执行起点之前的指令（重建传播删去的地址寄存器），再放置输入。helper 地址设桩：记录 x0–x2，按配置返回。
判定：pass / fail；输入不足以决定结果时为 inconclusive——读写毒值地址出错，或毒值（经寄存器或内存传递的污点）
流进条件分支、间接跳转目标、helper 参数或被检查的结果寄存器。映像中被写入的字节在每次执行后恢复。
"""
import json
import random
import re
import struct
import sys
from collections import defaultdict

from capstone import Cs, CS_ARCH_ARM64, CS_MODE_ARM
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UcError, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_PROT_ALL
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_X29, UC_ARM64_REG_X30, UC_ARM64_REG_SP, UC_ARM64_REG_PC, UC_ARM64_REG_NZCV

HEAP = 0x100000000000
HEAP_SIZE = 0x100000
STACK = 0x200000000000
STACK_SIZE = 0x100000
LIMIT = 4000
SAMPLES = int(__import__('os').environ.get('ORACLE_SAMPLES', '3'))
# capstone 寄存器名 → X 下标（w 与 x 同一寄存器；fp/lr 为 x29/x30）
REGISTER = {**{f'x{i}': i for i in range(29)}, **{f'w{i}': i for i in range(31)}, 'x29': 29, 'fp': 29, 'x30': 30, 'lr': 30}
# 由寄存器决定走向的指令（条件分支、间接跳转）；helper 桩检查的参数个数
DECIDES = {'cbz', 'cbnz', 'tbz', 'tbnz', 'br', 'blr', 'braa', 'brab', 'blraa', 'blrab'}
ARITY = {'InitMetadata': 1, 'helper': 1, 'lookup': 3, 'throw': 0}
NO_DESTINATION = {'cmp', 'cmn', 'tst', 'ccmp', 'ccmn', 'fcmp', 'fcmpe', 'fccmp', 'fccmpe', 'cbz', 'cbnz', 'tbz', 'tbnz', 'br', 'blr', 'ret', 'b', 'bl', 'prfm', 'braa', 'brab', 'blraa', 'blrab'}
# 只写部分位、其余保留的指令：目的寄存器同时被读
READ_DESTINATION = {'movk', 'bfi', 'bfxil', 'bfm', 'ins'}
FLAG_WRITERS = {'cmp', 'cmn', 'tst', 'ccmp', 'ccmn', 'fcmp', 'fcmpe', 'fccmp', 'fccmpe', 'adds', 'subs', 'ands', 'bics', 'adcs', 'sbcs', 'negs', 'ngcs'}
FLAG_READERS = {'csel', 'csinc', 'csinv', 'csneg', 'cset', 'csetm', 'cinc', 'cinv', 'cneg', 'ccmp', 'ccmn', 'adc', 'adcs', 'sbc', 'sbcs', 'fcsel', 'fccmp', 'fccmpe', 'ngc', 'ngcs'}
BRANCHES = {'b', 'br', 'ret', 'cbz', 'cbnz', 'tbz', 'tbnz', 'braa', 'brab', 'retaa', 'retab'}

X = [UC_ARM64_REG_X0 + i for i in range(29)] + [UC_ARM64_REG_X29, UC_ARM64_REG_X30]


def registers_accessed(insn):
    """按 ARM64 操作数格式求指令读写的通用寄存器与标志位（capstone 的 regs_access 对 cmp 等别名指令报告有误）。"""
    m, ops = insn.mnemonic, insn.op_str
    tokens = re.findall(r'\b([xw]\d+|fp|lr)\b', ops)
    if m in ('ldp', 'ldnp', 'ldpsw', 'ldxp', 'ldaxp'):
        written, read = tokens[:2], tokens[2:]
    elif m.startswith('st') and not m.startswith(('stxr', 'stlxr', 'stxp', 'stlxp')):
        written, read = [], tokens
    elif m in NO_DESTINATION or m.startswith('b.'):
        written, read = [], tokens
    elif m in READ_DESTINATION:
        written, read = tokens[:1], tokens
    else:
        written, read = tokens[:1], tokens[1:]
    # 前变址（!）与后变址（], #imm）写回基址寄存器
    base = re.search(r'\[([xw]\d+|sp)', ops)
    if base and ('!' in ops or re.search(r'\],\s*#', ops)) and base.group(1) != 'sp':
        written = written + [base.group(1)]
    if m.startswith('b.') or m in FLAG_READERS:
        read = read + ['nzcv']
    if m in FLAG_WRITERS:
        written = written + ['nzcv']
    return tuple(read), tuple(written)


def poison(i):
    return 0x5A5A000000000000 | (i << 20)


class Machine:
    def __init__(self, path):
        self.mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
        with open(path, 'rb') as f:
            elf = ELFFile(f)
            for seg in elf.iter_segments():
                if seg['p_type'] != 'PT_LOAD':
                    continue
                start = seg['p_vaddr'] & ~0xFFF
                end = (seg['p_vaddr'] + seg['p_memsz'] + 0xFFF) & ~0xFFF
                self.mu.mem_map(start, end - start, UC_PROT_ALL)
                self.mu.mem_write(seg['p_vaddr'], seg.data())
            for section in elf.iter_sections():
                if section['sh_type'] != 'SHT_RELA':
                    continue
                for r in section.iter_relocations():
                    kind = r['r_info_type']
                    if kind == 1027:  # R_AARCH64_RELATIVE
                        self.mu.mem_write(r['r_offset'], struct.pack('<Q', r['r_addend'] & (2 ** 64 - 1)))
                    elif kind in (257, 1025, 1026):  # ABS64 / GLOB_DAT / JUMP_SLOT：外部符号，填毒值
                        self.mu.mem_write(r['r_offset'], struct.pack('<Q', 0x6B6B000000000000 | (r['r_offset'] & 0xFFFFFFFF)))
        self.mu.mem_map(HEAP, HEAP_SIZE, UC_PROT_ALL)
        self.mu.mem_map(STACK, STACK_SIZE, UC_PROT_ALL)
        self.saved = {}
        self.mu.hook_add(UC_HOOK_MEM_WRITE, self.on_write)
        self.mu.hook_add(UC_HOOK_MEM_READ, self.on_read)
        self.mu.hook_add(UC_HOOK_CODE, self.on_code)
        self.exits = {}
        self.stubs = {}
        self.env = {}
        self.derived = {}
        self.block = 0
        self.tracking = False
        self.access = {}
        self.store_dirty, self.current_written, self.dirty_memory, self.clean_stack = False, [], set(), set()
        self.path = []
        self.cs = Cs(CS_ARCH_ARM64, CS_MODE_ARM)
        self.cs.detail = True

    def on_read(self, uc, access, address, size, value, data):
        # 栈上没有在模板中写过的字节是前缀或毒值留下的，同样带污点
        if self.tracking and any(a in self.dirty_memory or (STACK <= a < STACK + STACK_SIZE and a not in self.clean_stack)
                                 for a in range(address, address + size)):
            self.dirty.update(self.current_written)

    def on_write(self, uc, access, address, size, value, data):
        if self.tracking:
            for a in range(address, address + size):
                if self.store_dirty:
                    self.dirty_memory.add(a)
                else:
                    self.dirty_memory.discard(a)
                    self.clean_stack.add(a)
        if HEAP <= address < HEAP + HEAP_SIZE or STACK <= address < STACK + STACK_SIZE:
            return
        for a in range(address, address + size):
            if a not in self.saved:
                self.saved[a] = bytes(uc.mem_read(a, 1))

    def on_code(self, uc, address, size, data):
        # 调用出口本身读取目标寄存器，也要检查
        if self.tracking and address not in self.stubs and self.exits.get(address, 'call') == 'call':
            self.taint(uc, address)
        if address in self.exits:
            self.result['exit'] = self.exits[address]
            uc.emu_stop()
            return
        if address in self.stubs:
            args = [uc.reg_read(X[i]) for i in range(3)]
            name, behaviour = self.stubs[address]
            self.result['calls'].append((name, args))
            if self.tracking and any(i in self.dirty for i in range(ARITY.get(name, 1))):
                self.tainted = self.tainted or f'{name} 的参数@0x{address:x}'
            ret = behaviour(args) if behaviour else 0
            uc.reg_write(UC_ARM64_REG_X0, ret)
            self.dirty.discard(0)
            lr = uc.reg_read(UC_ARM64_REG_X30)
            if lr >> 48:
                self.result['exit'] = 'tail:' + name
                uc.emu_stop()
                return
            uc.reg_write(UC_ARM64_REG_PC, lr)

    def taint(self, uc, address):
        """污点传播：起点时为毒值的寄存器与模板之前留下的标志位带污点，读到污点的指令写出的寄存器也带污点，
        带污点的值写入内存后再读出同样带污点。污点流进条件分支或间接跳转的目标时，结果依赖于没有布置的状态（记入 self.tainted）。"""
        if address not in self.access:
            insn = self.decode(address)
            self.access[address] = (registers_accessed(insn), insn.mnemonic) if insn else (((), ()), '')
        (read, written), mnemonic = self.access[address]
        keys = [k for k in (('nzcv' if n == 'nzcv' else REGISTER.get(n)) for n in read) if k is not None]
        dirty = any(k in self.dirty for k in keys)
        # 写内存的值是否带污点（值寄存器为方括号之前的操作数）；读内存时若读到带污点的字节，在读钩子里把目的寄存器标上
        if mnemonic.startswith('st'):
            values = re.findall(r'\b([xw]\d+|fp|lr)\b', self.decode(address).op_str.split('[')[0])
            self.store_dirty = any(REGISTER.get(v) in self.dirty for v in values)
        else:
            self.store_dirty = False
        self.current_written = [k for k in (('nzcv' if n == 'nzcv' else REGISTER.get(n)) for n in written) if k is not None]
        if dirty and (mnemonic in DECIDES or mnemonic.startswith('b.')):
            self.tainted = self.tainted or f'{mnemonic}@0x{address:x}'
        for name in written:
            key = 'nzcv' if name == 'nzcv' else REGISTER.get(name)
            if key is None:
                continue
            if dirty:
                self.dirty.add(key)
            else:
                self.dirty.discard(key)

    def write(self, address, fmt, value):
        self.mu.mem_write(address, struct.pack(fmt, value))

    def read(self, address, fmt):
        return struct.unpack(fmt, bytes(self.mu.mem_read(address, struct.calcsize(fmt))))[0]

    def run(self, start, regs, exits, stubs):
        """从 start 执行到某个出口；返回 {'exit', 'calls', 'fault', 'regs'}。堆由调用方在执行前布置，restore() 清零。"""
        for i, r in enumerate(X):
            self.mu.reg_write(r, poison(i))
        # 输入与 env 是起点处的值，只在前缀执行之后放置（前缀里的寄存器还不是它们）
        self.mu.reg_write(UC_ARM64_REG_SP, STACK + STACK_SIZE - 0x1000)
        self.mu.reg_write(UC_ARM64_REG_NZCV, 0)
        self.exits, self.stubs = {}, {}
        self.prefix(start)
        for name, v in self.env.items():
            self.mu.reg_write(X[int(name[1:])], v)
        for i, v in regs.items():
            self.mu.reg_write(X[i], v)
        # 派生寄存器：读取基址（已放置的寄存器或槽位）+ 偏移处的值；基址不可读时保持毒值
        for name, spec in self.derived.items():
            if int(name[1:]) in regs:
                continue
            base = spec['base'].split('+')[0]
            try:
                address = self.read(int(base[5:], 16), '<Q') if base.startswith('slot:') else self.mu.reg_read(X[int(base[1:])])
                value = self.read(address + spec['offset'], {8: '<B', 16: '<H', 32: '<I', 64: '<Q'}[spec['width']])
                self.mu.reg_write(X[int(name[1:])], value)
            except (UcError, struct.error):
                pass
        self.exits = {a: n for n, a in exits.items()}
        self.stubs = stubs
        self.result = {'exit': None, 'calls': [], 'fault': None}
        self.dirty = {i for i, r in enumerate(X) if self.mu.reg_read(r) >> 48 == 0x5A5A} | {'nzcv'}
        self.dirty_memory, self.store_dirty, self.current_written, self.clean_stack = set(), False, [], set()
        self.tainted, self.tracking = None, True
        try:
            self.mu.emu_start(start, 0, count=LIMIT)
        except UcError as e:
            self.result['fault'] = f'{e} @0x{self.mu.reg_read(UC_ARM64_REG_PC):x}'
        self.tracking = False
        if self.tainted and self.result['fault'] is None:
            self.result['fault'] = f'UNPLACED: {self.tainted}'
        self.result['regs'] = [self.mu.reg_read(r) for r in X]
        return self.result

    def prefix(self, start):
        """执行唯一前驱链上各块与起始块中起点之前的指令，重建被传播删去的地址寄存器：
        调用不进入（调用者保存寄存器置毒），出错的指令跳过（目的寄存器置毒），块内遇到跳转即转到链上的下一块。"""
        chain = self.path + [self.block]
        for k, block in enumerate(chain):
            stop = start if k == len(chain) - 1 else chain[k + 1]
            pc = block
            for _ in range(400):
                if pc == stop or (k == len(chain) - 1 and pc >= start):
                    break
                insn = self.decode(pc)
                if insn is None:
                    break
                if insn.mnemonic in ('bl', 'blr'):
                    for i in list(range(19)) + [30]:
                        self.mu.reg_write(X[i if i < 29 else 30], poison(i))
                    pc += 4
                    continue
                if insn.mnemonic in BRANCHES or insn.mnemonic.startswith('b.'):
                    break
                try:
                    self.mu.emu_start(pc, pc + 4, count=1)
                except UcError:
                    for name in registers_accessed(insn)[1]:
                        if REGISTER.get(name) is not None:
                            self.mu.reg_write(X[REGISTER[name]], poison(REGISTER[name]))
                pc += 4

    def decode(self, pc):
        try:
            return next(self.cs.disasm(bytes(self.mu.mem_read(pc, 4)), pc))
        except (StopIteration, UcError):
            return None

    def restore(self):
        for a, b in self.saved.items():
            self.mu.mem_write(a, b)
        self.saved = {}
        self.mu.mem_write(HEAP, b'\0' * HEAP_SIZE)


class Heap:
    def __init__(self):
        self.next = HEAP + 0x100

    def alloc(self, size=0x400):
        address = self.next
        self.next += (size + 0xFF) & ~0xFF
        return address


def place(m, regs, where, value):
    """把输入值放到记录的每个位置（以 "+" 连接）：槽位（GOT 指向的槽位里写入值）或寄存器。"""
    for w in where.split('+'):
        if w.startswith('slot:'):
            m.write(int(w[5:], 16), '<Q', value)
        else:
            regs[int(w[1:])] = value


class Conflict(Exception):
    """两个输入落到同一位置却取不同的值：这组取值无法布置。"""


def place_value(m, regs, heap, objects, spec, value):
    """按放置方式放入值：位置字符串，或 {base, offset, width[, also]}——分配（同一基址共用）一个对象，把值写入该字段，
    also 中的寄存器同时放入该值。同一位置被放入不同的值时抛出 Conflict。"""
    if isinstance(spec, str):
        for w in spec.split('+'):
            if w.startswith('x') and regs.get(int(w[1:]), value) != value:
                raise Conflict(w)
        place(m, regs, spec, value)
        return
    base = spec['base']
    if base not in objects:
        objects[base] = heap.alloc()
        place(m, regs, base, objects[base])
    field = (base, spec['offset'])
    width = spec['width']
    value &= (1 << width) - 1
    previous = objects.get(field)
    if previous is not None and previous != (value, width):
        raise Conflict(f'{base}+{spec["offset"]:#x}')
    objects[field] = (value, width)
    m.write(objects[base] + spec['offset'], {8: '<B', 16: '<H', 32: '<I', 64: '<Q'}[width], value)
    if 'also' in spec:
        place_value(m, regs, heap, objects, spec['also'], value)


def inconclusive(r):
    return r['fault'] is not None and ('UNMAPPED' in r['fault'] or 'FETCH' in r['fault'] or 'UNPLACED' in r['fault'])


# ---------- 各模板的配置与期望 ----------

def metadata_init_guard(m, inst):
    i = inst['inputs']
    guard, slots, helpers = i['guard'], i['slots'], i['helpers']
    stubs = {h: ('InitMetadata', lambda a: HEAP + 0x80) for h in helpers}
    outcomes = []
    for value in (1, 0):
        old = m.read(guard, '<B')
        m.write(guard, '<B', value)
        r = m.run(inst['head'], {}, inst['exits'], stubs)
        after = m.read(guard, '<B')
        m.write(guard, '<B', old)
        m.restore()
        if inconclusive(r):
            return 'inconclusive', r['fault']
        called = sorted(a[0] for n, a in r['calls'])
        if value == 1:
            ok = r['exit'] == 'merge' and not r['calls']
        else:
            ok = r['exit'] == 'merge' and called == sorted(slots) and after & 1 == 1
        outcomes.append((ok, f'guard={value}: exit={r["exit"]} calls={[hex(c) for c in called]} after={after} fault={r["fault"]}'))
    return verdict(outcomes)


def class_guard(field, width, enter, skip, returns_argument, rgctx=False):
    def test(m, inst):
        i = inst['inputs']
        heap = Heap()
        outcomes = []
        for value in (skip, enter):
            regs = {}
            subject = heap.alloc()
            place(m, regs, i['subject'], subject)
            m.write(subject + field, '<Q' if width == 64 else '<I' if width == 32 else '<B', value)

            def behaviour(a, subject=subject):
                if rgctx:
                    m.write(subject + field, '<Q', HEAP + 0x2000)
                return a[0] if returns_argument else 0
            r = m.run(inst['head'], regs, inst['exits'], {i['helper']: ('helper', behaviour)})
            m.restore()
            if inconclusive(r):
                return 'inconclusive', r['fault']
            if value == skip:
                ok = r['exit'] == 'merge' and not r['calls']
            else:
                ok = r['exit'] == 'merge' and len(r['calls']) == 1 and r['calls'][0][1][0] == subject
            outcomes.append((ok, f'field={value:#x}: exit={r["exit"]} calls={[(n, hex(a[0])) for n, a in r["calls"]]} fault={r["fault"]}'))
        return verdict(outcomes)
    return test


def null_check(m, inst):
    i = inst['inputs']
    heap = Heap()
    outcomes = []
    for value in (0, None):
        regs = {}
        if value is None:
            value = heap.alloc()
            m.write(value, '<Q', heap.alloc())  # klass
        place_value(m, regs, heap, {}, i['value'], value)
        r = m.run(inst['head'], regs, inst['exits'], {i['helper']: ('throw', None)})
        m.restore()
        if inconclusive(r):
            return 'inconclusive', r['fault']
        expected = 'throw' if value == 0 else 'pass'
        ok = r['exit'] == expected or (expected == 'throw' and r['calls'] and r['calls'][0][0] == 'throw')
        outcomes.append((ok, f'value={value:#x}: exit={r["exit"]} expected={expected} fault={r["fault"]}'))
    return verdict(outcomes)


def interface_dispatch(m, inst):
    i = inst['inputs']
    slot = i['slot']
    result = int(i['result'][1:])
    outcomes = []
    for case in ('hit', 'miss', 'empty'):
        heap = Heap()
        regs = {}
        obj, klass, iface, other1, other2 = (heap.alloc() for _ in range(5))
        pairs = heap.alloc()
        m.write(obj, '<Q', klass)
        place(m, regs, i['object'], obj)
        place(m, regs, i['interface'], iface)
        entries = {'hit': [(other1, 5), (iface, 7), (other2, 9)], 'miss': [(other1, 5), (other2, 9)], 'empty': []}[case]
        for k, (t, offset) in enumerate(entries):
            m.write(pairs + 16 * k, '<Q', t)
            m.write(pairs + 16 * k + 8, '<i', offset)
        m.write(klass + 0xB0, '<Q', pairs)
        m.write(klass + 0x12E, '<H', len(entries))
        slow = HEAP + 0x3000
        r = m.run(inst['head'], regs, inst['exits'], {i['helper']: ('lookup', lambda a: slow)})
        m.restore()
        if inconclusive(r):
            return 'inconclusive', r['fault']
        if result in m.dirty:
            return 'inconclusive', f'x{result} 带污点'
        got = r['regs'][result]
        if case == 'hit':
            expected = klass + 0x138 + 16 * (7 + slot)
            ok = r['exit'] == 'merge' and not r['calls'] and got == expected
        else:
            expected = slow
            ok = r['exit'] == 'merge' and len(r['calls']) == 1 and r['calls'][0][1] == [obj, iface, slot] and got == expected
        outcomes.append((ok, f'{case}: exit={r["exit"]} x{result}={got:#x} expected={expected:#x} calls={[(n, [hex(x) for x in a]) for n, a in r["calls"]]} fault={r["fault"]}'))
    return verdict(outcomes)


def inline_type_check(m, inst):
    i = inst['inputs']
    outcomes = []
    for case, depth, match in (('subclass', 4, True), ('unrelated', 4, False), ('shallower', 2, False)):
        heap = Heap()
        regs = {}
        klass, target, other = heap.alloc(), heap.alloc(), heap.alloc()
        hierarchy = heap.alloc()
        place(m, regs, i['klass'], klass)
        place(m, regs, i['type'], target)
        m.write(target + 0x130, '<B', 3)
        m.write(klass + 0x130, '<B', depth)
        m.write(klass + 0xC8, '<Q', hierarchy)
        for k in range(depth):
            m.write(hierarchy + 8 * k, '<Q', target if (match and k == 2) else other + 8 * k)
        r = m.run(inst['head'], regs, inst['exits'], {})
        m.restore()
        if inconclusive(r):
            return 'inconclusive', r['fault']
        expected = 'success' if match else 'fail'
        outcomes.append((r['exit'] == expected, f'{case}: exit={r["exit"]} expected={expected} fault={r["fault"]}'))
    return verdict(outcomes)


def bounds_check(m, inst):
    i = inst['inputs']
    mask = (1 << i['width']) - 1
    outcomes = []
    for index, length in ((0, 5), (4, 5), (5, 5), (mask, 5), (0, 0), (7, 3)):
        heap, regs, objects = Heap(), {}, {}
        try:
            place_value(m, regs, heap, objects, i['index'], index)
            place_value(m, regs, heap, objects, i['length'], length)
        except Conflict as c:
            m.restore()
            return 'inconclusive', f'UNPLACED: 索引与长度落在同一位置 {c}'
        r = m.run(inst['head'], regs, inst['exits'], {i['helper']: ('throw', None)})
        m.restore()
        if inconclusive(r):
            return 'inconclusive', r['fault']
        expected = 'throw' if index >= length else 'pass'
        ok = r['exit'] == expected or (expected == 'throw' and r['calls'] and r['calls'][0][0] == 'throw')
        outcomes.append((ok, f'index={index:#x} length={length}: exit={r["exit"]} expected={expected} fault={r["fault"]}'))
    return verdict(outcomes)


def virtual_call(m, inst):
    i = inst['inputs']
    offset = i['offset']
    heap, regs = Heap(), {}
    obj, klass = heap.alloc(), heap.alloc(offset + 0x100)
    m.write(obj, '<Q', klass)
    target, method = 0x7777000000000000 | offset, heap.alloc()
    m.write(klass + offset, '<Q', target)
    m.write(klass + offset + 8, '<Q', method)
    place(m, regs, i['object'], obj)
    r = m.run(inst['head'], regs, inst['exits'], {})
    m.restore()
    if inconclusive(r):
        return 'inconclusive', r['fault']
    if 0 in m.dirty:
        return 'inconclusive', 'x0 带污点'
    insn = m.decode(inst['exits']['call'])
    register = insn.reg_name(insn.operands[0].reg) if insn and insn.mnemonic in ('blr', 'br') else None
    called = r['regs'][int(register[1:])] if register and register[1:].isdigit() else None
    ok = r['exit'] == 'call' and called == target and r['regs'][0] == obj
    return ('pass' if ok else 'fail'), f'exit={r["exit"]} {register}={called and hex(called)} expected={target:#x} x0={r["regs"][0]:#x} obj={obj:#x} fault={r["fault"]}'


def verdict(outcomes):
    return ('pass' if all(ok for ok, _ in outcomes) else 'fail'), '; '.join(text for _, text in outcomes)


TESTS = {
    'MetadataInitGuard': metadata_init_guard,
    'ClassConstructorGuard': class_guard(0xE0, 32, 0, 1, False),
    'InitClassGuard': class_guard(0x135, 8, 0, 1, True),
    'MethodRgctxGuard': class_guard(0x38, 64, 0, HEAP + 0x2000, True, rgctx=True),
    'NullCheck': null_check,
    'InterfaceDispatch': interface_dispatch,
    'InlineTypeCheck': inline_type_check,
    'BoundsCheck': bounds_check,
    'VirtualCall': virtual_call,
}


def main():
    so, path = sys.argv[1], sys.argv[2]
    limit = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    m = Machine(so)
    by_template = defaultdict(list)
    for line in open(path):
        inst = json.loads(line)
        inst['exits'] = {k: int(v) for k, v in inst['exits'].items()}
        if inst['template'] in TESTS:
            by_template[inst['template']].append(inst)
    failed = 0
    for template, instances in sorted(by_template.items()):
        random.Random(10).shuffle(instances)
        tally = defaultdict(int)
        samples = defaultdict(list)
        for inst in instances[:limit]:
            m.env = inst['inputs'].get('env', {})
            m.derived = inst['inputs'].get('derived', {})
            m.block = inst['inputs'].get('block', inst['head'])
            m.path = inst['inputs'].get('path', [])
            outcome, detail = TESTS[template](m, inst)
            tally[outcome] += 1
            if len(samples[outcome]) < SAMPLES:
                samples[outcome].append(f'函数 0x{inst["function"]:x} 起始 0x{inst["head"]:x}: {detail}')
        failed += tally['fail']
        print(f'{template:24} pass {tally["pass"]:4}  fail {tally["fail"]:4}  inconclusive {tally["inconclusive"]:4}')
        for outcome in ('fail', 'inconclusive'):
            for s in samples[outcome]:
                print(f'    {outcome}: {s}')
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
