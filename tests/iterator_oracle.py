"""一个真实 IEnumerator.MoveNext 的分支合流、状态写入与异常次序对照。"""
import itertools
import json
from pathlib import Path
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_CODE
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_X30, UC_ARM64_REG_SP, UC_ARM64_REG_PC

ROOT = Path(__file__).resolve().parents[1]
config = json.loads((ROOT/'native.local.json').read_text())
ENTRY, END, FLAG, GOT = 0x57088d0, 0x5708964, 0xbddab37, 0xb6fe260
THIS, NEW, TYPE, OLD, RETURN, STACK = 0x1000000, 0x1001000, 0x1002000, 0x1003000, 0x2000000, 0x3000000
HELPERS = {0x49c85a8:'metadata',0x49c8830:'allocate',0xad5c900:'ctor',0x49c8554:'barrier'}
with open(config['Binary'],'rb') as binary:
    elf = ELFFile(binary)
    segment = next(s for s in elf.iter_segments() if s['p_vaddr'] <= ENTRY < s['p_vaddr']+s['p_filesz'])
    binary.seek(segment['p_offset']+ENTRY-segment['p_vaddr'])
    CODE = binary.read(END-ENTRY)
    SLOT = next(r['r_addend'] for r in elf.get_section_by_name('.rela.dyn').iter_relocations() if r['r_offset']==GOT)


def initial(case):
    memory = {}
    for a,v,size in [(FLAG,case['flag'],1),(GOT,SLOT,8),(SLOT,TYPE,8),(THIS+16,case['state'],4),(THIS+24,case['current'],8)]: put(memory,a,v,size)
    return memory


def put(memory,a,value,size):
    for i,b in enumerate((value & ((1<<(size*8))-1)).to_bytes(size,'little')): memory[a+i]=b


def read(memory,a,size): return int.from_bytes(bytes(memory.get(a+i,0) for i in range(size)),'little')


def machine(case):
    memory=initial(case)
    uc=Uc(UC_ARCH_ARM64,UC_MODE_ARM)
    for page in {a&~0xfff for a in [*memory,ENTRY,END-1,*HELPERS,RETURN,STACK]}: uc.mem_map(page,0x1000)
    for a,b in memory.items(): uc.mem_write(a,bytes([b]))
    uc.mem_write(ENTRY,CODE)
    uc.reg_write(UC_ARM64_REG_X0,THIS); uc.reg_write(UC_ARM64_REG_X30,RETURN); uc.reg_write(UC_ARM64_REG_SP,STACK+0x800)
    trace=[]
    returned=None
    def hook(engine,pc,size,user):
        nonlocal returned
        if pc==RETURN:
            returned=engine.reg_read(UC_ARM64_REG_X0)&0xffffffff
            engine.emu_stop(); return
        if pc not in HELPERS: return
        name=HELPERS[pc]
        trace.append([name,engine.reg_read(UC_ARM64_REG_X0)])
        if name==case['throw']:
            trace.append(['exception',name]); engine.emu_stop(); return
        link=engine.reg_read(UC_ARM64_REG_X30)
        for i in range(19): engine.reg_write(UC_ARM64_REG_X0+i,0xde000000+i)
        engine.reg_write(UC_ARM64_REG_X0,NEW if name=='allocate' else 0)
        engine.reg_write(UC_ARM64_REG_PC,link)
    uc.hook_add(UC_HOOK_CODE,hook)
    uc.emu_start(ENTRY,RETURN+4,count=150)
    return trace,returned,int.from_bytes(uc.mem_read(THIS+16,4),'little'),int.from_bytes(uc.mem_read(THIS+24,8),'little'),uc.mem_read(FLAG,1)[0]


def semantic(case,function):
    memory=initial(case)
    variables={'this':THIS,'null':0,'true':1,'false':0}
    trace=[]
    returned=None
    def address(e): return e['Address'] if e['kind']=='global' else expr(e['receiver'])+e['Offset']
    def expr(e,size=8):
        k=e['kind']
        if k in ['name','capture']: return variables[e['Name']]
        if k=='constant': return e['Value']
        if k=='metadata': return e['Slot'] if e['IsSlot'] else TYPE
        if k in ['member','global']: return read(memory,address(e),e.get('Size',size))
        if k=='address-of': return address(e['target'])
        if k=='slice': return (expr(e['value']) >> e['BitOffset']) & ((1 << e['BitWidth']) - 1)
        if k=='binary':
            a,b=expr(e['left']),expr(e['right'])
            return {'==':lambda:a==b,'!=':lambda:a!=b,'&':lambda:a&b}[e['Operator']]()
        raise AssertionError(e)
    def finish(): return trace,returned,read(memory,THIS+16,4),read(memory,THIS+24,8),read(memory,FLAG,1)
    blocks={b['Address']:b for b in function['blocks']}
    pc=function['entry']
    for step in range(60):
        b=blocks[pc]
        for s in b['statements']:
            k=s['kind']
            if k=='declare': continue
            if k in ['assign','set-local']: variables[s['Name']]=expr(s['value'],1 if s.get('Type')=='uint8_t' else 8)
            elif k=='store': put(memory,address(s['target']),expr(s['value']),s['target'].get('Size',1))
            elif k=='return': returned=int(expr(s['value'])); return finish()
            elif k=='ensure-metadata':
                if read(memory,s['Flag'],1)&1==0:
                    trace.extend(['metadata',slot] for slot in s['slots']); put(memory,s['Flag'],1,1)
            elif k=='call':
                name=s['Name']; args=[expr(a) for a in s['arguments']]
                if name=='Runtime.InitializeMetadata': name='metadata'
                elif name.startswith('Runtime.Allocate<'): name='allocate'; args=[TYPE]
                elif name=='.ctor': name='ctor'; args=[expr(s['receiver'])]
                elif name=='Runtime.GCWriteBarrier': name='barrier'
                else: raise AssertionError(name)
                trace.append([name,*args])
                if name==case['throw']: trace.append(['exception',name]); return finish()
                if s['Result']: variables[s['Result']]=NEW
            else: raise AssertionError(s)
        if not b['Successors']: return finish()
        pc=b['Successors'][0 if b['condition'] is None or expr(b['condition']) else 1]
    raise AssertionError('nonterminating')


functions=[json.loads((ROOT/f'artifacts/recovered/0x57088d0{suffix}.semantics.json').read_text()) for suffix in ['', '.view']]
cases=[dict(zip(['flag','state','current','throw'],v)) for v in itertools.product([0,1,2],[-2,-1,0,1,2],[0,OLD],['','allocate','ctor','barrier'])]
for case in cases:
    actual=machine(case)
    for function in functions: assert actual==semantic(case,function),(case,actual,semantic(case,function))
report={'method':'0x57088d0','cases':len(cases),'raw_matched':len(cases),'view_matched':len(cases),'scope':'Unicorn real MoveNext; runtime stubs; state/current writes, returns and exceptions; not high-level yield recovery'}
(ROOT/'artifacts/iterator-oracle.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report))
