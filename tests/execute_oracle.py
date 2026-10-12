"""Execute 的真实 ARM64 与两层语义 IR 对照；外部调用使用明确的测试桩。"""
import itertools
import json
from pathlib import Path
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_CODE
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_X30, UC_ARM64_REG_SP, UC_ARM64_REG_PC

ROOT = Path(__file__).resolve().parents[1]
inputs = json.loads((ROOT / 'native.local.json').read_text(encoding='utf-8'))
ENTRY, END, FLAG = 0x51f7dc4, 0x51f7f44, 0xbdd850e
THIS, INCOMING, OLD, COMBINED, BOXED, FORMATTED, NEW, RESULT, SCORE = [0x1000000 + i * 0x1000 for i in range(9)]
RETURN, STACK = 0x2000000, 0x3000000
HELPERS = {0x49c85a8:'metadata', 0xa38be58:'combine', 0x49c8720:'isinst', 0x49c8bd8:'invalid-cast',
    0x49c8554:'barrier', 0x49c8724:'box', 0xa1c4500:'format', 0x49c8830:'allocate', 0x8e58850:'ctor', 0x9fa8a80:'call'}
with open(inputs['Binary'], 'rb') as f:
    elf = ELFFile(f)
    segment = next(s for s in elf.iter_segments() if s['p_vaddr'] <= ENTRY < s['p_vaddr'] + s['p_filesz'])
    f.seek(segment['p_offset'] + ENTRY - segment['p_vaddr'])
    CODE = f.read(END - ENTRY)
    wanted = {0xb71fc58, 0xb71fca8, 0xb6ea0e0, 0xb6fb388, 0xb71fcb0}
    GOT = {r['r_offset']:r['r_addend'] for r in elf.get_section_by_name('.rela.dyn').iter_relocations() if r['r_offset'] in wanted}
assert len(GOT) == 5
SLOTS = list(GOT.values())
META = {slot:0x4000000 + index * 0x1000 for index, slot in enumerate(SLOTS)}
BOX_TYPE, DELEGATE_TYPE = META[GOT[0xb6ea0e0]], META[GOT[0xb6fb388]]


def memory_for(case):
    memory = {}
    put(memory, FLAG, case['flag'], 1)
    for at, value in GOT.items(): put(memory, at, value)
    for at, value in META.items(): put(memory, at, value)
    put(memory, THIS + 0x10, OLD if case['old'] else 0)
    put(memory, THIS + 0x48, case['user'] & ((1 << 64) - 1))
    put(memory, THIS + 0x50, SCORE)
    return memory


def put(memory, address, value, size=8):
    for i, b in enumerate(int(value).to_bytes(size, 'little', signed=False)): memory[address+i] = b


def read(memory, address, size=8):
    return int.from_bytes(bytes(memory.get(address+i, 0) for i in range(size)), 'little')


def effect(case, name, args, trace, casts):
    trace.append([name, *args])
    if name == 'invalid-cast' or name == case['throw']:
        trace.append(['exception', name])
        return 0, True
    if name == 'combine': return COMBINED if case['combine'] else 0, False
    if name == 'isinst': return (0 if casts == case['cast_fail'] else args[0]), False
    return {'box':BOXED, 'format':FORMATTED, 'allocate':NEW, 'call':RESULT}.get(name, 0), False


def machine(case):
    memory = memory_for(case)
    uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    pages = {a & ~0xfff for a in memory} | {a & ~0xfff for a in [ENTRY, END-1, RETURN, STACK, *HELPERS]}
    for page in pages: uc.mem_map(page, 0x1000)
    for a, b in memory.items(): uc.mem_write(a, bytes([b]))
    uc.mem_write(ENTRY, CODE)
    uc.reg_write(UC_ARM64_REG_X0, THIS)
    uc.reg_write(UC_ARM64_REG_X0+1, INCOMING if case['incoming'] else 0)
    uc.reg_write(UC_ARM64_REG_X30, RETURN)
    uc.reg_write(UC_ARM64_REG_SP, STACK+0x800)
    trace, casts, returned = [], 0, None
    def hook(engine, address, size, user):
        nonlocal casts, returned
        if address == RETURN:
            returned = engine.reg_read(UC_ARM64_REG_X0)
            engine.emu_stop()
            return
        if address not in HELPERS: return
        name = HELPERS[address]
        args = [engine.reg_read(UC_ARM64_REG_X0+i) for i in range(8)]
        counts = {'metadata':1,'combine':2,'isinst':2,'invalid-cast':1,'barrier':1,'box':2,'format':3,'allocate':1,'ctor':3,'call':7}
        args = args[:counts[name]]
        if name == 'box': args[1] = int.from_bytes(engine.mem_read(args[1], 8), 'little')
        if name == 'isinst': casts += 1
        value, stop = effect(case, name, args, trace, casts)
        if stop: engine.emu_stop(); return
        link = engine.reg_read(UC_ARM64_REG_X30)
        for i in range(19): engine.reg_write(UC_ARM64_REG_X0+i, 0xde000000+i)
        engine.reg_write(UC_ARM64_REG_X0, value)
        engine.reg_write(UC_ARM64_REG_PC, link)
    uc.hook_add(UC_HOOK_CODE, hook)
    uc.emu_start(ENTRY, RETURN+4, count=300)
    return trace, int.from_bytes(uc.mem_read(THIS+0x10, 8), 'little'), uc.mem_read(FLAG, 1)[0], returned


def semantic(case, function):
    memory = memory_for(case)
    variables = {'this':THIS, 'onCallBackResponse':INCOMING if case['incoming'] else 0,
        'null':0,'true':1,'false':0,'Sekai.APICoreParam.Method.DELETE':4}
    trace, casts, returned = [], 0, None
    def address(node):
        if node['kind'] == 'global': return node['Address']
        if node['kind'] == 'member': return expr(node['receiver']) + node['Offset']
        raise AssertionError(node)
    def expr(node, size=8):
        kind = node['kind']
        if kind in ('name','capture'): return variables[node['Name']]
        if kind == 'constant': return node['Value']
        if kind == 'metadata': return node['Slot'] if node['IsSlot'] else META[node['Slot']]
        if kind in ('global','member'): return read(memory, address(node), node.get('Size',size))
        if kind == 'address-of': return address(node['target'])
        if kind == 'slice':
            return (expr(node['value']) >> node['BitOffset']) & ((1 << node['BitWidth']) - 1)
        if kind == 'binary':
            a,b = expr(node['left']),expr(node['right'])
            return {'==':lambda:a==b,'!=':lambda:a!=b,'is':lambda:a==b,'is not':lambda:a!=b,'&':lambda:a&b}[node['Operator']]()
        raise AssertionError(node)
    def finish(): return trace,read(memory,THIS+0x10),read(memory,FLAG,1),returned
    blocks = {b['Address']:b for b in function['blocks']}
    pc = function['entry']
    for step in range(100):
        block = blocks[pc]
        for statement in block['statements']:
            kind = statement['kind']
            if kind == 'assign': variables[statement['Name']] = expr(statement['value'], 1 if statement['Type']=='uint8_t' else 8)
            elif kind == 'store':
                target = statement['target']
                put(memory,address(target),expr(statement['value']),target.get('Size',1))
            elif kind == 'ensure-metadata':
                if read(memory,statement['Flag'],1)&1 == 0:
                    trace.extend(['metadata',slot] for slot in statement['slots'])
                    put(memory,statement['Flag'],1,1)
            elif kind == 'return':
                returned = expr(statement['value']); return finish()
            elif kind == 'call':
                name = statement['Name']
                args = [expr(a) for a in statement['arguments']]
                if name == 'Runtime.InitializeMetadata': name='metadata'
                elif name == 'System.Delegate.Combine': name='combine'
                elif name.startswith('Runtime.IsInstance<'): name='isinst'; args.append(DELEGATE_TYPE); casts+=1
                elif name == 'Runtime.ThrowInvalidCast': name='invalid-cast'
                elif name == 'Runtime.GCWriteBarrier': name='barrier'
                elif name.startswith('Runtime.Box<'): name='box'; args.insert(0,BOX_TYPE)
                elif name == 'System.String.Format': name='format'
                elif name.startswith('Runtime.Allocate<'): name='allocate'; args=[DELEGATE_TYPE]
                elif name == '.ctor': name='ctor'; args.insert(0,expr(statement['receiver']))
                elif name == 'Call': name='call'; args.insert(0,expr(statement['receiver']))
                else: raise AssertionError(name)
                value,stop = effect(case,name,args,trace,casts)
                if stop: return finish()
                if statement['Result']: variables[statement['Result']] = value
            else: raise AssertionError(statement)
        if not block['Successors']: return finish()
        condition = block['condition'] is None or expr(block['condition'])
        pc = block['Successors'][0 if condition else 1]
    raise AssertionError('nonterminating IR')


raw = json.loads((ROOT/'artifacts/recovered/0x51f7dc4.semantics.json').read_text())
view = json.loads((ROOT/'artifacts/recovered/0x51f7dc4.view.semantics.json').read_text())
cases = [dict(zip(['flag','incoming','old','combine','user','cast_fail','throw'], values)) for values in
    itertools.product([0,1,2],[False,True],[False,True],[False,True],[0,-1,0x123456789abcdef],[0,1,2],['','combine','box','format','allocate','ctor','call','barrier'])]
for case in cases:
    actual = machine(case)
    assert actual == semantic(case,raw), ('raw',case,actual,semantic(case,raw))
    assert actual == semantic(case,view), ('view',case,actual,semantic(case,view))
report = {'method':'0x51f7dc4','cases':len(cases),'raw_matched':len(cases),'view_matched':len(cases),
    'scope':'actual ARM64 under Unicorn; deterministic runtime stubs; return, stores, flag, call arguments/order and exception exits; not game execution'}
(ROOT/'artifacts/execute-oracle.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report))
