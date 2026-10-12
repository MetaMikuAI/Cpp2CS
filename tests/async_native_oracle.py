"""MoveNext 控制流与聚合值对照；运行时调用使用测试桩。"""
import hashlib
import itertools
import json
import struct
import sys
from pathlib import Path
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_CODE
from unicorn.arm64_const import *

ROOT = Path(__file__).resolve().parents[1]
config = json.loads((ROOT / 'native.local.json').read_text())
ENTRY, END = 0x55d9650, 0x55d9aa8
report = json.loads((ROOT / 'artifacts/recovered/0x55d9650.json').read_text())
flow = json.loads((ROOT / 'artifacts/recovered/0x55d9650.flow.json').read_text())
setup_abi = next(c['abi'] for c in report['nativeCalls'] if c['Address'] == 0x55d96d8)
assert setup_abi['return']['Size'] == 16
assert [(p['register'], p['ValueOffset'], p['Size']) for p in setup_abi['return']['pieces']] == [('X0', 0, 8), ('X1', 8, 8)]
assert report['entryAbi']['arguments'][0]['Type'].endswith('*')
with open(config['Binary'], 'rb') as binary:
    elf = ELFFile(binary)
    segments = list(elf.iter_segments())
    def read(at, size):
        segment = next(s for s in segments if s['p_type'] == 'PT_LOAD' and s['p_vaddr'] <= at and at + size <= s['p_vaddr'] + s['p_filesz'])
        binary.seek(segment['p_offset'] + at - segment['p_vaddr'])
        return binary.read(size)
    code = read(ENTRY, END - ENTRY)
    lsda = read(report['exceptionTable']['Lsda'], 512)

# 独立解码原始 call-site 表，异常注入不从待测控制流图选择处理器。
cursor = 0
def byte():
    global cursor
    value = lsda[cursor]
    cursor += 1
    return value
def uleb():
    value, shift = 0, 0
    while True:
        b = byte()
        value |= (b & 127) << shift
        if b < 128: return value
        shift += 7
assert byte() == 255
encoding = byte()
if encoding != 255: uleb()
assert byte() == 1
table_length = uleb()
table_end = cursor + table_length
regions = []
while cursor < table_end:
    start, length, pad, action = uleb(), uleb(), uleb(), uleb()
    regions.append((ENTRY + start, ENTRY + start + length, ENTRY + pad if pad else None, action))
assert cursor == table_end
assert regions == [(r['Start'], r['End'], r['LandingPad'], r['ActionOffset']) for r in report['exceptionTable']['ExceptionRegions']]

THIS, STACK, SOURCE, CLASS, RUNNER = 0x200000, 0x210000, 0x220000, 0x230000, 0x240000
ITF_TASK, ITF_RUNNER, SLOT, TABLE = 0x250000, 0x250100, 0x260000, 0x270000
OBJECT, EXCEPTION, WRAP, UNWIND = 0x280000, 0x290000, 0x290100, 0x290200
STOP = 0x700000
VIRTUAL = {0x710000: 'status', 0x710010: 'result', 0x710020: 'complete', 0x710030: 'fail'}
HELPERS = {0x49c85a8: 'metadata', 0x49c8830: 'allocate', 0x56aeb08: 'ctor', 0x56ab3bc: 'setup',
           0x49c871c: 'class-init', 0x49c8554: 'barrier', 0x499e914: 'resolve', 0x55ea734: 'await',
           0x49c883c: 'null-throw', 0xb0992a0: 'begin-catch', 0x49c85bc: 'exception-type',
           0x49c8c68: 'assignable', 0xb0992b0: 'end-catch', 0xb0992c0: 'allocate-exception',
           0xb0992d0: 'throw-wrapper', 0x4aad07c: 'unwind', 0x44102bc: 'terminate', **VIRTUAL}
edges = {n['Instruction']['Address']: n['Edges'] for n in flow['Nodes']}
observed_edges, observed_calls = set(), set()
outcomes = {'caught': 0, 'propagated': 0, 'suspended': 0, 'completed': 0}
ssa_program = json.loads((ROOT / 'artifacts/recovered/0x55d9650.ssa.json').read_text()) if '--ssa' in sys.argv else None
ssa_checks = 0
observations = []

def run(resumed, ready, source_present, runner_present, token_word, interfaces, throws):
    global ssa_checks
    uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    pages = {a & ~4095 for a in [ENTRY, END-1, 0xb737000, 0xb6e8000, 0xb6e7000, 0xbdd4000, 0xbdda000, STOP, *HELPERS]}
    pages.update(range(THIS, 0x2a0000, 4096))
    for page in sorted(pages): uc.mem_map(page, 4096)
    uc.mem_write(ENTRY, code)
    def put(at, value, size=8): uc.mem_write(at, (value & ((1 << (8 * size)) - 1)).to_bytes(size, 'little'))
    def get(at, size=8): return int.from_bytes(uc.mem_read(at, size), 'little')
    def x(n): return uc.reg_read(UC_ARM64_REG_X0 + n) if n < 29 else uc.reg_read(UC_ARM64_REG_X29 if n == 29 else UC_ARM64_REG_X30)
    def setx(n, value): uc.reg_write(UC_ARM64_REG_X0 + n, value)
    source = SOURCE if source_present else 0
    put(THIS, 0 if resumed else -1, 4)
    put(THIS + 8, RUNNER if runner_present else 0)
    for offset, value in [(0x18, 0x111111), (0x20, 0x222222), (0x28, 0x333333), (0x30, 0x444444)]: put(THIS + offset, value)
    payload = struct.pack('<QQ', source, token_word)
    if resumed: uc.mem_write(THIS + 0x38, payload)
    for index, (got, value) in enumerate([(0xb7376b0, 0x999999), (0xb7376b8, CLASS), (0xb6e8d20, CLASS), (0xb6e82a8, ITF_TASK), (0xb6e82b0, ITF_RUNNER), (0xb6e7cd0, CLASS)]):
        put(got, SLOT + 8 * index)
        put(SLOT + 8 * index, value)
    put(SOURCE, CLASS)
    put(RUNNER, CLASS + 0x400)
    put(EXCEPTION, CLASS)
    put(WRAP, EXCEPTION)
    for klass, interface, table, methods in [(CLASS, ITF_TASK, TABLE, {0: 0x710000, 2: 0x710010}),
                                              (CLASS + 0x400, ITF_RUNNER, TABLE + 0x100, {2: 0x710020, 3: 0x710030})]:
        put(klass + 0xe0, 1, 4)
        put(klass + 0x12e, interfaces, 2)
        put(klass + 0xb0, table)
        for index in range(interfaces):
            put(table + index * 16, interface if index == interfaces - 1 else 0xabcdef)
            put(table + index * 16 + 8, 0, 4)
        for slot, target in methods.items():
            put(klass + 0x138 + slot * 16, target)
            put(klass + 0x140 + slot * 16, 0x888888 + slot)
    for flag in [0xbdda37f, 0xbdd4c1a, 0xbdd4c1b, 0xbdd4c1c, 0xbdd4c10, 0xbdd4c0f]: put(flag, 1, 1)
    uc.reg_write(UC_ARM64_REG_SP, STACK + 0x800)
    uc.reg_write(UC_ARM64_REG_X30, STOP)
    setx(0, THIS)
    trace, pending, exit_kind = [], None, None
    injected = []
    visited = []
    checker = None
    if ssa_program is not None:
        from ssa_lockstep import SsaLockstep
        checker = SsaLockstep(ssa_program, uc)
    def hook(engine, pc, size, data):
        nonlocal pending, exit_kind
        if checker is not None: checker.observe(pc, pending)
        if pc == STOP:
            exit_kind = 'return'
            engine.emu_stop()
            return
        if ENTRY <= pc < END:
            if pending:
                before, kind = pending
                assert any(e['Target'] == pc and (e['Kind'] == kind or kind == 'exception' and e['Kind'] in ['exception-dispatch', 'exception-cleanup']) for e in edges[before]), (hex(before), hex(pc), kind)
                observed_edges.add((before, pc, kind))
                pending = None
            elif visited:
                before = visited[-1]
                assert any(e['Target'] == pc for e in edges[before]), (hex(before), hex(pc))
                observed_edges.add((before, pc, 'local'))
            visited.append(pc)
            return
        name = HELPERS[pc]
        callpc = uc.reg_read(UC_ARM64_REG_X30) - 4
        observed_calls.add(callpc)
        args = [x(i) for i in range(6)]
        if name in ['setup', 'status', 'result', 'await', 'complete', 'fail']: trace.append(name)
        if name in (throws or '').split(','):
            injected.append(name)
            region = next((r for r in regions if r[0] <= callpc < r[1]), None)
            if region and region[2]:
                for i in range(19): setx(i, 0xdead0000 + i)
                setx(0, UNWIND)
                setx(1, 1)
                pending = (callpc, 'exception')
                uc.reg_write(UC_ARM64_REG_PC, region[2])
            else:
                assert any(e['Kind'] in ['exception-unwind', 'exception-missing-callsite-terminate'] for e in edges[callpc])
                exit_kind = 'propagate'
                engine.emu_stop()
            return
        returns = {}
        if name == 'allocate': returns[0] = OBJECT
        elif name == 'setup':
            assert args == [OBJECT, 0x111111, 0x222222, 0x333333, 0x444444, 0]
            returns = {0: source, 1: token_word}
        elif name == 'resolve':
            klass = get(args[0])
            assert args[1] == (ITF_TASK if args[0] == SOURCE else ITF_RUNNER)
            returns[0] = klass + 0x138 + args[2] * 16
        elif name in ['status', 'result']:
            assert args[:2] == [SOURCE, token_word & 0xffff], args
            assert args[2] == 0x888888 + (0 if name == 'status' else 2)
            assert uc.mem_read(uc.reg_read(UC_ARM64_REG_SP), 16) == payload
            returns[0] = int(ready)
        elif name == 'await':
            assert args[:4] == [THIS + 8, uc.reg_read(UC_ARM64_REG_SP), THIS, 0x999999]
            assert uc.mem_read(THIS + 0x38, 16) == payload
            assert get(THIS, 4) == 0
        elif name == 'complete': assert args[:2] == [RUNNER, 0x88888a]
        elif name == 'fail': assert args[:3] == [RUNNER, EXCEPTION, 0x88888b]
        elif name == 'begin-catch': returns[0] = WRAP
        elif name == 'exception-type': returns[0] = CLASS
        elif name == 'assignable': returns[0] = 1
        elif name in ['throw-wrapper', 'unwind', 'terminate', 'null-throw']: raise AssertionError(name)
        for i in range(19): setx(i, returns.get(i, 0xdead0000 + i))
        pending = (callpc, 'normal-return')
        uc.reg_write(UC_ARM64_REG_PC, callpc + 4)
    uc.hook_add(UC_HOOK_CODE, hook)
    uc.emu_start(ENTRY, STOP + 4, count=10000)
    assert exit_kind is not None, 'execution budget exhausted'
    exceptional = bool(injected)
    if exit_kind == 'propagate':
        outcomes['propagated'] += 1
        assert injected[-1] in ['complete', 'fail']
    elif exceptional:
        outcomes['caught'] += 1
        assert get(THIS, 4) == 0xfffffffe and exit_kind == 'return'
        assert ('fail' in trace) if runner_present else get(THIS + 0x10) == EXCEPTION
    elif source_present and not resumed and not ready:
        outcomes['suspended'] += 1
        assert get(THIS, 4) == 0 and trace[-1] == 'await'
    else:
        outcomes['completed'] += 1
        assert get(THIS, 4) == 0xfffffffe and exit_kind == 'return'
        assert ('complete' in trace) == runner_present
    if resumed: assert uc.mem_read(THIS + 0x38, 16) == bytes(16)
    if checker is not None: ssa_checks += checker.checks
    observations.append({'resumed': resumed, 'ready': ready, 'source': source_present, 'runner': runner_present,
                         'token': token_word, 'interfaces': interfaces, 'throws': throws,
                         'trace': trace, 'exit': exit_kind, 'state': get(THIS, 4)})

cases = list(itertools.product([False, True], [False, True], [False, True], [False, True],
                               [0, 0xffff, 0xdeadbeef12348001], [0, 1, 3], [None]))
cases += [(resumed, True, True, runner, 0xdeadbeef12348001, interfaces, thrown)
          for resumed, runner, interfaces, thrown in itertools.product([False, True], [False, True], [0, 3], ['setup', 'status', 'result', 'await', 'complete'])]
cases += [(False, False, True, runner, 0xdeadbeef12348001, interfaces, 'await') for runner, interfaces in itertools.product([False, True], [0, 3])]
cases += [(False, True, True, runner, 0xdeadbeef12348001, interfaces, thrown)
          for runner, interfaces, thrown in itertools.product([False, True], [0, 3], ['allocate', 'ctor'])]
cases += [(resumed, True, True, runner, 0xdeadbeef12348001, interfaces, 'result,fail')
          for resumed, runner, interfaces in itertools.product([False, True], [False, True], [0, 3])]
for case in cases: run(*case)
result = {'status': 'passed', 'cases': len(cases), 'nativeInstructions': len(code) // 4,
          'ssaChecks': ssa_checks,
          'outcomes': outcomes,
          'observedEdges': len(observed_edges), 'observedCallSites': len(observed_calls),
          'codeSha256': hashlib.sha256(code).hexdigest(),
          'scope': 'real ARM64 with runtime stubs; aggregate transport, normal/caught-exception flow and state effects',
          'notValidated': ['generated high-level async equivalence', 'real UniTask scheduler', 'real C++ unwinder', 'foreign exceptions']}
(ROOT / 'artifacts/async-native-oracle.json').write_text(json.dumps(result, indent=2))
(ROOT / 'artifacts/async-observations.json').write_text(json.dumps(observations, indent=2))
print(json.dumps(result))
