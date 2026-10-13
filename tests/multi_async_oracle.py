"""真实 ARM64 与生成 C# 的测试输入。外部调用使用显式桩，保留原生指令及 LSDA。"""
import argparse
import hashlib
import itertools
import json
import struct
from pathlib import Path
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_CODE, UC_HOOK_MEM_UNMAPPED
from unicorn.arm64_const import *

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--ssa', action='store_true')
parser.add_argument('--diagnostics', type=Path, default=ROOT / 'artifacts/recovered')
args = parser.parse_args()
CFG = json.loads((ROOT / 'native.local.json').read_text())
DATA = Path(CFG['Binary']).read_bytes()
with open(CFG['Binary'], 'rb') as stream:
    elf = ELFFile(stream)
    SEGMENTS = [(s['p_vaddr'], s['p_offset'], s['p_filesz'], s['p_memsz']) for s in elf.iter_segments() if s['p_type'] == 'PT_LOAD']
    RELOC = {}
    for section in elf.iter_sections():
        if section['sh_type'] == 'SHT_RELA':
            for at, info, addend in struct.iter_unpack('<QQq', section.data()):
                if info & 0xffffffff == 1027: RELOC[at] = addend
metadata = json.loads(Path(CFG['Symbols']).read_text())
META = {r['Address']: r['Name'] for key in ['ScriptMetadata', 'ScriptMetadataMethod'] for r in metadata[key]}
PAGE_META, PAGE_RELOC = {}, {}
for at, name in META.items(): PAGE_META.setdefault(at & ~4095, []).append((at, name))
for at, value in RELOC.items(): PAGE_RELOC.setdefault(at & ~4095, []).append((at, value))

def read(at, size):
    base, offset, length, memory = next(s for s in SEGMENTS if s[0] <= at and at + size <= s[0] + s[2])
    return DATA[offset + at - base:offset + at - base + size]

def regions(entry, lsda):
    data = read(lsda, 2048)
    cursor = 0
    def byte():
        nonlocal cursor
        value = data[cursor]; cursor += 1
        return value
    def uleb():
        value, shift = 0, 0
        while True:
            b = byte(); value |= (b & 127) << shift
            if b < 128: return value
            shift += 7
    assert byte() == 255
    if byte() != 255: uleb()
    assert byte() == 1
    length = uleb(); end = cursor + length
    result = []
    while cursor < end:
        start, size, pad, action = uleb(), uleb(), uleb(), uleb()
        result.append((entry + start, entry + start + size, entry + pad if pad else None))
    return result

ENTRIES = {'branch': 0x55d684c, 'generic': 0x55d4ad8, 'virtual': 0x5bea518}
REPORTS = {k: json.loads((args.diagnostics / f'0x{a:x}.json').read_text()) for k, a in ENTRIES.items()}
CODE = {k: read(a, REPORTS[k]['exceptionTable']['End'] - a) for k, a in ENTRIES.items()}
REGIONS = {k: regions(a, REPORTS[k]['exceptionTable']['Lsda']) for k, a in ENTRIES.items()}
SSA = {k: json.loads((args.diagnostics / f'0x{a:x}.ssa.json').read_text()) for k,a in ENTRIES.items()} if args.ssa else {}
THIS, STACK, SOURCE, CLASS, RUNNER = 0x200000, 0x210000, 0x220000, 0x230000, 0x240000
ITF, GENERIC_ITF, RUNNER_ITF = 0x250000, 0x250400, 0x250800
OBJ, MODEL, MASTER, RECORD, PHENOMENA = 0x280000, 0x281000, 0x282000, 0x283000, 0x284000
MI, GCLASS, RGCTX, WRAP, EXCEPTION = 0x290000, 0x291000, 0x292000, 0x293000, 0x294000
STOP = 0x700000
HELPERS = {0x49c85a8:'metadata', 0x49c871c:'class-init', 0x499e620:'class-meta', 0x49c8554:'barrier',
    0x499e914:'resolve', 0x55ea200:'schedule', 0x55e9bac:'schedule', 0x5bee820:'schedule',
    0x49c883c:'null-throw', 0xb0992a0:'begin-catch', 0x49c85bc:'exception-type', 0x49c8c68:'assignable',
    0xb0992b0:'end-catch', 0xb0992c0:'allocate-exception', 0xb0992d0:'throw-wrapper', 0x4aad07c:'unwind', 0x44102bc:'terminate',
    0x6264610:'delivery', 0x90d90b4:'manager', 0x62d75d0:'site', 0x62da348:'phenomena', 0x62da710:'phenomena-bgm',
    0x621bc48:'asset', 0x55d3e90:'bgm', 0x55d40b4:'load',
    0x710000:'status', 0x710010:'result', 0x710020:'complete', 0x710030:'fail', 0x710040:'page', 0x710050:'list'}

def run(case):
    kind = case['kind']; entry = ENTRIES[kind]
    uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    for page in range(THIS, 0x2a0000, 4096): uc.mem_map(page, 4096)
    mapped = set(range(THIS, 0x2a0000, 4096))
    def put(at, value, size=8): uc.mem_write(at, (value & ((1 << (size * 8)) - 1)).to_bytes(size, 'little'))
    def get(at, size=8): return int.from_bytes(uc.mem_read(at, size), 'little')
    def metadata_value(name):
        if name.startswith('Method$Cysharp.Threading.Tasks.UniTask.Awaiter<bool>.'): return MI
        if name.startswith('Method$Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskMethodBuilder<bool>.'): return MI + 0x100
        if name == 'Cysharp.Threading.Tasks.IUniTaskSource_TypeInfo': return ITF
        if 'IStateMachineRunnerPromise' in name: return RUNNER_ITF
        return CLASS
    def map_page(page):
        if page in mapped: return
        uc.mem_map(page, 4096); mapped.add(page)
        for base, offset, length, memory in SEGMENTS:
            begin, end = max(page, base), min(page + 4096, base + length)
            if begin < end: uc.mem_write(begin, DATA[offset + begin - base:offset + end - base])
        for at, value in PAGE_RELOC.get(page, []): put(at, value)
        for at, name in PAGE_META.get(page, []): put(at, metadata_value(name))
    def unmapped(engine, access, address, size, value, data):
        assert any(base <= address < base + memory for base, _, _, memory in SEGMENTS), hex(address)
        map_page(address & ~4095)
        return True
    uc.hook_add(UC_HOOK_MEM_UNMAPPED, unmapped)
    for page in {a & ~4095 for a in [entry, entry + len(CODE[kind]) - 1, STOP, *HELPERS]}: map_page(page)
    def x(n): return uc.reg_read(UC_ARM64_REG_X0 + n)
    def setx(n, value): uc.reg_write(UC_ARM64_REG_X0 + n, value)
    def task(index):
        source = SOURCE + index * 0x100 if case['source'] else 0
        word = (case['token'] + index) & 0xffff
        if kind == 'generic': word = (word << 16) | int(case['result'])
        return source, word
    put(THIS, -1, 4); put(THIS + 8, RUNNER if case['runner'] else 0)
    captured = 0x20 if kind != 'virtual' else 0x18
    put(THIS + captured, OBJ)
    if kind == 'branch':
        put(THIS + 0x18, 77 if case['branch'] == 0 else 88, 4); put(THIS + 0x1c, 42, 4); put(THIS + 0x28, 0x123456)
    if kind == 'generic':
        put(THIS + 0x28, MODEL); put(THIS + 0x30, int(case['fade']), 1); put(THIS + 0x38, 0x123456)
        put(MODEL + 0xf0, 101); put(MODEL + 0xf8, 102); put(MODEL + 0x110, 0x3fa00000, 4)
    put(RECORD + 0x28, 101); put(RECORD + 0x30, 102)
    put(RECORD + 0x18, 101); put(RECORD + 0x20, 102)
    put(PHENOMENA + 0x10, -1 if case['branch'] == 2 else 2, 4)
    for c in [CLASS, CLASS + 0x400, CLASS + 0x800, ITF, GENERIC_ITF, RUNNER_ITF, GCLASS, GCLASS + 0x400]:
        put(c + 0xe0, 1, 4); put(c + 0x135, 1, 1)
    put(MI + 0x20, GCLASS); put(MI + 0x120, GCLASS + 0x400)
    put(GCLASS + 0xc0, RGCTX); put(RGCTX + 5 * 8, GENERIC_ITF)
    put(GCLASS + 0x4c0, RGCTX + 0x100); put(RGCTX + 0x108, RUNNER_ITF)
    put(SOURCE, CLASS); put(SOURCE + 0x100, CLASS); put(RUNNER, CLASS + 0x400); put(OBJ, CLASS + 0x800)
    put(EXCEPTION, CLASS); put(WRAP, EXCEPTION)
    for c, table, interfaces, methods in [
        (CLASS, 0x260000, [(ITF, 0), (GENERIC_ITF, 3)], {0:0x710000, 2:0x710010, 3:0x710010}),
        (CLASS + 0x400, 0x261000, [(RUNNER_ITF, 0)], {2:0x710020, 3:0x710030})]:
        rows = [(0xabcdef, 0)] * case['interfaces'] + interfaces if case['interfaces'] else []
        put(c + 0x12e, len(rows), 2); put(c + 0xb0, table)
        for i, (itf, offset) in enumerate(rows): put(table + 16*i, itf); put(table + 16*i + 8, offset, 4)
        for slot, target in methods.items(): put(c + 0x138 + slot*16, target); put(c + 0x140 + slot*16, 0x888000 + slot)
    put(CLASS + 0x800 + 0x288, 0x710040); put(CLASS + 0x800 + 0x290, 0x888015)
    put(CLASS + 0x800 + 0x2a8, 0x710050); put(CLASS + 0x800 + 0x2b0, 0x888017)
    trace, states, active, scheduled, finished, failed, propagated = [], [], 0, False, False, False, False
    checker, pending, checks = None, None, 0
    visited = set()
    def hook(engine, pc, size, data):
        nonlocal active, scheduled, finished, failed, propagated, pending
        if checker is not None: checker.observe(pc,pending)
        if pc == STOP: engine.emu_stop(); return
        if entry <= pc < entry + len(CODE[kind]): visited.add(pc); pending=None; return
        name = HELPERS[pc]; callpc = uc.reg_read(UC_ARM64_REG_X30) - 4
        args = [x(i) for i in range(6)]; returns = {}
        if name in ['bgm', 'load', 'page', 'list']: active = 1 if name == 'list' else 0
        if name in ['status', 'result']: active = (args[0] - SOURCE) // 0x100
        label = name + str(active) if name in ['status', 'result', 'schedule'] else 'work' + str(active) if name in ['bgm', 'load', 'page', 'list'] else name
        if name in ['status', 'result', 'schedule']: trace.append(label)
        if name == 'delivery': trace.append('delivery'); returns[0] = 77
        elif name == 'manager': trace.append('manager'); returns[0] = 0 if case['missing'] == 'manager' else MASTER
        elif name == 'site':
            trace.append(f'site:{args[1]}:{args[2]}'); returns[0] = 0 if case['missing'] == 'bgm' else RECORD
        elif name == 'phenomena':
            assert args[2] == 1; trace.append(f'phenomena:{args[1]}'); returns[0] = 0 if case['missing'] == 'phenomena' else PHENOMENA
        elif name == 'phenomena-bgm': trace.append(f'phenomena-bgm:{args[1]}'); returns[0] = 0 if case['missing'] == 'bgm' else RECORD
        elif name == 'asset':
            assert args[0] == 101, (case, hex(callpc), args, get(RECORD+0x28))
            trace.append('asset:101'); returns[0] = 103
        elif name == 'bgm': assert args[:4] == [OBJ,103,102,0x123456]; trace.append('bgm:103:102'); returns = dict(enumerate(task(active)))
        elif name == 'load':
            assert args[:5] == [OBJ,101,102,int(case['fade']),0x123456] and uc.reg_read(UC_ARM64_REG_S0) == 0x3fa00000
            trace.append('load:101:102:' + str(int(case['fade'])) + ':1.25'); returns = dict(enumerate(task(active)))
        elif name in ['page', 'list']: assert args[0] == OBJ; trace.append(name); returns = dict(enumerate(task(active)))
        elif name == 'resolve':
            offset = 3 if args[1] == GENERIC_ITF else 0
            assert args[1] in [ITF, GENERIC_ITF, RUNNER_ITF], hex(args[1])
            returns[0] = get(args[0]) + 0x138 + (offset + args[2])*16
        elif name in ['status','result']:
            assert args[1] == (case['token'] + active) & 0xffff
            returns[0] = int(case['ready'][active]) if name == 'status' else int(case['result'])
        elif name == 'schedule':
            offset = {'branch':0x30,'generic':0x40,'virtual':0x20}[kind]
            assert uc.mem_read(THIS + offset, 16) == struct.pack('<QQ', *task(active))
            states.append(get(THIS,4)); scheduled = True
        elif name == 'complete':
            assert args[0] == RUNNER
            if kind == 'generic': assert args[1] == int(case['result'])
            finished = True
        elif name == 'fail': assert args[:2] == [RUNNER,EXCEPTION]; failed = True
        elif name == 'begin-catch': returns[0] = WRAP
        elif name == 'exception-type': map_page(args[0] & ~4095); returns[0] = get(args[0])
        elif name == 'assignable': returns[0] = 1
        elif name == 'class-meta': returns[0] = args[0]
        elif name in ['throw-wrapper','unwind','terminate']: raise AssertionError(name)
        thrown = name == 'null-throw' or label == case['throws']
        if thrown:
            failed = True
            region = next((r for r in REGIONS[kind] if r[0] <= callpc < r[1]), None)
            if region and region[2]:
                for i in range(19): setx(i, 0xdead0000+i)
                for i in range(8): uc.reg_write(UC_ARM64_REG_Q0+i, 0xdead00000000000000000000+i)
                setx(0, 0x295000); setx(1,1); uc.reg_write(UC_ARM64_REG_PC,region[2])
                pending=(callpc,'exception')
            else: propagated = True; engine.emu_stop()
            return
        for i in range(19): setx(i, returns.get(i, 0xdead0000+i))
        for i in range(8): uc.reg_write(UC_ARM64_REG_Q0+i, 0xdead00000000000000000000+i)
        pending=(callpc,'normal-return')
        uc.reg_write(UC_ARM64_REG_PC, callpc+4)
    uc.hook_add(UC_HOOK_CODE, hook)
    for invocation in range(3):
        scheduled = False
        uc.reg_write(UC_ARM64_REG_SP, STACK+0x800); uc.reg_write(UC_ARM64_REG_X30,STOP); setx(0,THIS)
        pending=None
        if kind in SSA:
            from ssa_lockstep import SsaLockstep
            checker=SsaLockstep(SSA[kind],uc,map_page)
        uc.emu_start(entry, STOP+4, count=10000)
        if checker is not None: checks+=checker.checks
        if not scheduled or failed or propagated: break
    assert get(THIS,4) == 0xfffffffe, (case, trace, states, hex(get(THIS,4)))
    offset = {'branch':0x30,'generic':0x40,'virtual':0x20}[kind]
    if states and not failed: assert uc.mem_read(THIS+offset,16) == bytes(16)
    if not case['runner']:
        if failed: assert get(THIS + 0x10) == EXCEPTION
        elif kind == 'generic': assert get(THIS+0x18,1) == int(case['result'])
    return {**case, 'trace':trace, 'states':states, 'failed':failed, 'propagated':propagated, 'instructionsVisited':len(visited), 'ssaChecks':checks}

def cases():
    base = dict(branch=0, missing='', source=True, ready=[True,True], result=True, fade=True, runner=True, token=0x8001, interfaces=1, throws='')
    for kind in ENTRIES:
        for branch, source, ready, result, runner, interfaces in itertools.product(range(3) if kind=='branch' else [0], [False,True], [[True,True],[False,True],[True,False],[False,False]] if kind=='virtual' else [[True,True],[False,True]], [False,True] if kind=='generic' else [True], [False,True], [0,2]):
            yield dict(base, kind=kind, branch=branch, source=source, ready=ready, result=result, fade=result, runner=runner, interfaces=interfaces)
        for thrown in ['work0','status0','result0','schedule0'] + (['work1','status1','result1','schedule1'] if kind=='virtual' else []):
            for runner in [False,True]: yield dict(base,kind=kind,ready=[False,False],throws=thrown,runner=runner)
    for branch, missing in itertools.product(range(3), ['manager','phenomena','bgm']): yield dict(base,kind='branch',branch=branch,missing=missing)
    for kind, token in itertools.product(ENTRIES, [0,0xffff]): yield dict(base,kind=kind,token=token,ready=[False,False],result=False)

if __name__ == '__main__':
    observations = [run(c) for c in cases()]
    (ROOT/'artifacts/multi-async-observations.json').write_text(json.dumps(observations,indent=2))
    result = {'status':'passed','cases':len(observations),'codeSha256':{k:hashlib.sha256(v).hexdigest() for k,v in CODE.items()},
        'suspensions':sum(len(o['states']) for o in observations),'failures':sum(o['failed'] for o in observations), 'ssaChecks':sum(o['ssaChecks'] for o in observations),
        'scope':'real ARM64 instructions; runtime and business calls stubbed; original LSDA independently decoded',
        'notValidated':['real game runtime','real UniTask scheduler','foreign exception unwinder']}
    (ROOT/'artifacts/multi-async-native.json').write_text(json.dumps(result,indent=2)); print(json.dumps(result))
