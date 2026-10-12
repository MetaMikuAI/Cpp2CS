"""固定真机码样本的独立 ARM64/语义 IR 对照；运行时调用使用明确的测试桩。"""
import itertools
import json
import struct
import subprocess
import sys
from pathlib import Path

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_CODE
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_X30, UC_ARM64_REG_SP, UC_ARM64_REG_PC

ROOT = Path(__file__).resolve().parents[1]
INPUTS = json.loads((ROOT / 'native.local.json').read_text(encoding='utf-8'))
ENTRY, END = 0x51f7f44, 0x51f7ff0
INIT, GET, UPDATE, THROW = 0x49c85a8, 0x90d90b4, 0x63334e0, 0x49c883c
FLAG = 0xbdd850f
GOT = {0xb709e68: 0xba73378, 0xb6e8430: 0xbaa9218}
THIS, API, RESULT, MANAGER, RESPONSE, DELEGATE = [0x1000000 + n * 0x1000 for n in range(6)]
CALLBACK, RETURN, STACK = 0x2000000, 0x2001000, 0x3000000

with open(INPUTS['Binary'], 'rb') as binary:
    elf = ELFFile(binary)
    segment = next(s for s in elf.iter_segments() if s['p_vaddr'] <= ENTRY < s['p_vaddr'] + s['p_filesz'])
    binary.seek(segment['p_offset'] + ENTRY - segment['p_vaddr'])
    CODE = binary.read(END - ENTRY)


def initial_memory(case):
    memory = {}
    def put(address, value, size=8):
        for i, byte in enumerate(int(value).to_bytes(size, 'little')):
            memory[address + i] = byte
    for address, value in GOT.items():
        put(address, value)
        put(value, 0x4000000 + (value & 0xffff))
    put(FLAG, case['flag'], 1)
    put(THIS + 0x10, DELEGATE if case['callback'] else 0)
    put(API + 0x40, 0 if case['null'] == 'result' else RESULT)
    put(API + 0x98, RESPONSE)
    put(RESULT + 0x10, case['state'], 4)
    put(DELEGATE + 0x18, CALLBACK)
    put(DELEGATE + 0x40, 0x5000000)
    put(DELEGATE + 0x28, 0x5001000)
    return memory


def machine(case):
    uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    memory = initial_memory(case)
    pages = {a & ~0xfff for a in memory} | {a & ~0xfff for a in [ENTRY, INIT, GET, UPDATE, THROW, CALLBACK, RETURN, STACK]}
    for page in sorted(pages):
        uc.mem_map(page, 0x1000)
    for address, byte in memory.items():
        uc.mem_write(address, bytes([byte]))
    uc.mem_write(ENTRY, CODE)
    uc.reg_write(UC_ARM64_REG_X0, THIS)
    uc.reg_write(UC_ARM64_REG_X1, 0 if case['null'] == 'api' else API)
    uc.reg_write(UC_ARM64_REG_X30, RETURN)
    uc.reg_write(UC_ARM64_REG_SP, STACK + 0x800)
    trace = []
    def hook(engine, address, size, user_data):
        if address == INIT:
            trace.append(['metadata', engine.reg_read(UC_ARM64_REG_X0)])
        elif address == GET:
            trace.append(['singleton'])
            engine.reg_write(UC_ARM64_REG_X0, 0 if case['null'] == 'manager' else MANAGER)
        elif address == UPDATE:
            trace.append(['update', engine.reg_read(UC_ARM64_REG_X0), engine.reg_read(UC_ARM64_REG_X1), engine.reg_read(UC_ARM64_REG_X2)])
            if case['throws'] == 'update':
                trace.append(['exception', 'update'])
                engine.emu_stop()
                return
        elif address == CALLBACK:
            trace.append(['callback', engine.reg_read(UC_ARM64_REG_X1)])
            if case['throws'] == 'callback':
                trace.append(['exception', 'callback'])
            engine.emu_stop()
            return
        elif address == THROW:
            trace.append(['exception', 'null'])
            engine.emu_stop()
            return
        elif address == RETURN:
            engine.emu_stop()
            return
        else:
            return
        engine.reg_write(UC_ARM64_REG_PC, engine.reg_read(UC_ARM64_REG_X30))
    uc.hook_add(UC_HOOK_CODE, hook)
    uc.emu_start(ENTRY, RETURN + 4, count=200)
    return trace, bytes(uc.mem_read(FLAG, 1))[0]


def semantic(case, function):
    memory = initial_memory(case)
    variables = {'this': THIS, 'apiCore': 0 if case['null'] == 'api' else API,
                 'true': 1, 'false': 0, 'null': 0, 'Sekai.APIState.SuccessComplete': 18}
    trace = []
    blocks = {b['Address']: b for b in function['blocks']}
    fault = False
    def read(address, size):
        return int.from_bytes(bytes(memory.get(address + i, 0) for i in range(size)), 'little')
    def expr(node, size=8):
        nonlocal fault
        kind = node['kind']
        if kind in ('name', 'capture'):
            return variables[node['Name']]
        if kind == 'constant':
            return node['Value']
        if kind == 'global':
            return read(node['Address'], size)
        if kind == 'metadata':
            return node['Slot'] if node['IsSlot'] else read(node['Slot'], 8)
        if kind == 'member':
            receiver = expr(node['receiver'])
            if receiver == 0:
                fault = True
                return 0
            return read(receiver + node['Offset'], node['Size'])
        if kind == 'slice':
            return (expr(node['value']) >> node['BitOffset']) & ((1 << node['BitWidth']) - 1)
        if kind == 'binary':
            a, b = expr(node['left']), expr(node['right'])
            return {'==': lambda: a == b, '!=': lambda: a != b, 'is': lambda: a == b, 'is not': lambda: a != b, '&': lambda: a & b}[node['Operator']]()
        raise AssertionError('unsupported expression: ' + str(node))
    address = function['entry']
    for step in range(100):
        block = blocks[address]
        for statement in block['statements']:
            kind = statement['kind']
            if kind == 'assign':
                variables[statement['Name']] = expr(statement['value'], 1 if statement['Type'] == 'uint8_t' else 8)
            elif kind == 'store':
                memory[statement['target']['Address']] = expr(statement['value'])
            elif kind == 'throw':
                assert statement['Type'] == 'System.NullReferenceException'
                trace.append(['exception', 'null'])
                return trace, memory[FLAG]
            elif kind == 'return':
                return trace, memory[FLAG]
            elif kind == 'ensure-metadata':
                if memory[statement['Flag']] & 1 == 0:
                    trace.extend(['metadata', slot] for slot in statement['slots'])
                    memory[statement['Flag']] = 1
            elif kind == 'conditional-invoke':
                receiver = expr(statement['receiver'])
                if receiver != 0:
                    assert receiver == DELEGATE
                    trace.append(['callback', *[expr(a) for a in statement['arguments']]])
                    if case['throws'] == 'callback':
                        trace.append(['exception', 'callback'])
                        return trace, memory[FLAG]
            elif kind == 'call':
                name = statement['Name']
                arguments = [expr(a) for a in statement['arguments']]
                if name == 'Runtime.InitializeMetadata':
                    trace.append(['metadata', arguments[0]])
                elif name == 'CP.SingletonMonoBehaviour<UserDataManager>.get_Instance':
                    trace.append(['singleton'])
                    variables[statement['Result']] = 0 if case['null'] == 'manager' else MANAGER
                elif name == 'UpdateAll':
                    trace.append(['update', expr(statement['receiver']), *arguments])
                    if case['throws'] == 'update':
                        trace.append(['exception', 'update'])
                        return trace, memory[FLAG]
                elif name == 'Invoke':
                    assert expr(statement['receiver']) == DELEGATE
                    trace.append(['callback', *arguments])
                    if case['throws'] == 'callback':
                        trace.append(['exception', 'callback'])
                        return trace, memory[FLAG]
                else:
                    raise AssertionError('unexpected call: ' + name)
            else:
                raise AssertionError('unsupported statement: ' + str(statement))
            if fault:
                trace.append(['exception', 'null'])
                return trace, memory[FLAG]
        if not block['Successors']:
            return trace, memory[FLAG]
        condition = block['condition'] is None or expr(block['condition'])
        if fault:
            trace.append(['exception', 'null'])
            return trace, memory[FLAG]
        address = block['Successors'][0 if condition else 1]
    raise AssertionError('semantic execution did not terminate')


function = json.loads((ROOT / 'artifacts/recovered/0x51f7f44.semantics.json').read_text(encoding='utf-8'))
view_function = json.loads((ROOT / 'artifacts/recovered/0x51f7f44.view.semantics.json').read_text(encoding='utf-8'))
cases = [dict(flag=f, state=s, callback=c, null=n, throws=t)
         for f, s, c, n, t in itertools.product([0, 1, 2], [0, 18, 19], [False, True], ['', 'api', 'result', 'manager'], ['', 'update', 'callback'])]
for case in cases:
    actual, recovered = machine(case), semantic(case, function)
    assert actual == recovered, (case, actual, recovered)
    normalized = semantic(case, view_function)
    assert actual == normalized, (case, actual, normalized)
report = {'method':'0x51f7f44','cases':len(cases),'matched':len(cases), 'normalized_view_matched':len(cases),
          'scope':'Unicorn ARM64 instructions vs structured semantic IR; runtime helpers/calls are deterministic stubs, not real game execution'}
if '--view' in sys.argv:
    fixture = ROOT / 'artifacts/ViewFixture/bin/Release/net10.0/ViewFixture.dll'
    output = subprocess.run(['dotnet', str(fixture)], check=True, capture_output=True, text=True)
    view_cases = json.loads(output.stdout)
    for row in view_cases:
        case = {**row, 'null':'', 'throws':''}
        actual = machine(case)
        assert actual == (row['trace'], row['finalFlag']), (case, actual, row)
    report['compiled_view_cases'] = len(view_cases)
    report['compiled_view_matched'] = len(view_cases)
(ROOT / 'artifacts/native-oracle.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
print(json.dumps(report))
