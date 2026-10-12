"""SSA 与真实 ARM64 逐指令对照。运行时调用使用外部桩的返回值。"""
from collections import defaultdict
from unicorn.arm64_const import *

class SsaLockstep:
    def __init__(self, program, uc, load_page=None):
        self.uc = uc
        self.load_page = load_page
        self.values = {v['Id']: v for v in program['Values']}
        self.instructions = {i['Address']: i for i in program['Instructions']}
        self.flow = {n['Instruction']['Address']: n for n in program['Flow']['Nodes']}
        self.definitions = defaultdict(list)
        for value in program['Values']:
            if value['Address']: self.definitions[value['Address']].append(value['Id'])
        self.cache, self.memory = {}, {}
        for start,end,_ in uc.mem_regions():
            self.memory.update(enumerate(uc.mem_read(start,end-start+1),start))
        self.initial = {f'x{i}': self.register(f'x{i}') for i in range(31)}
        self.initial.update({f'v{i}': self.register(f'v{i}') for i in range(32)})
        self.initial['nzcv'] = self.register('nzcv')
        self.initial['sp'] = self.register('sp')
        self.last = None
        self.expected = []
        self.writes = []
        self.checks = 0
        self.pc = None
    def register(self, name):
        if name == 'sp': return self.uc.reg_read(UC_ARM64_REG_SP)
        if name == 'nzcv': return self.uc.reg_read(UC_ARM64_REG_NZCV) >> 28
        if name.startswith('v'): return self.uc.reg_read(UC_ARM64_REG_Q0 + int(name[1:]))
        n = int(name[1:])
        return self.uc.reg_read(UC_ARM64_REG_X0+n if n<29 else UC_ARM64_REG_X29 if n==29 else UC_ARM64_REG_X30)
    def value(self, key):
        if key in self.cache: return self.cache[key]
        n = self.values[key]; op=n['Operation']; width=n['Width']; ids=n['Inputs']
        def val(i): return self.value(ids[i])
        if op == 'alias': result=val(0)
        elif op == 'constant': result=n['Immediate']
        elif op == 'stack-address': result=self.initial['sp']
        elif op == 'parameter': result=self.initial[f"x{n['Immediate']}"]
        elif op == 'unknown' and key.startswith('entry_'): result=self.initial[key[6:]]
        elif op == 'slice': result=val(0)>>n['Immediate']
        elif op in ['zero-extend','abi-extend']: result=val(0)
        elif op == 'sign-extend':
            bits=self.values[ids[0]]['Width']; value=val(0)
            result=value-(1<<bits) if value>>(bits-1) else value
        elif op == 'add': result=val(0)+val(1)
        elif op == 'sub': result=val(0)-val(1)
        elif op == 'orr': result=val(0)|val(1)
        elif op == 'and': result=val(0)&val(1)
        elif op == 'shift-left': result=val(0)<<n['Immediate']
        elif op == 'load':
            address=val(1)
            for at in range(address,address+width//8):
                if at not in self.memory and self.load_page is not None:
                    page=at & ~4095; self.load_page(page)
                    self.memory.update(enumerate(self.uc.mem_read(page,4096),page))
            result=int.from_bytes(bytes(self.memory[address+i] for i in range(width//8)),'little')
        elif op == 'store':
            # 前一 store 只用于排序；指令以前的内存版本已执行。
            before=self.values[ids[0]]
            if before['Operation']=='store' and before['Address']==self.pc: self.value(ids[0])
            address=val(1); size=self.values[ids[2]]['Width']//8; data=val(2).to_bytes(size,'little')
            self.memory.update(enumerate(data,address)); self.writes.append((address,data)); result=0
        elif op in ['memory','call-memory','exception-memory','return']: result=0
        elif op == 'compare':
            a,b=val(0),val(1); bits=self.values[ids[0]]['Width']; mask=(1<<bits)-1; diff=(a-b)&mask
            result=((diff>>(bits-1))<<3)|(int(diff==0)<<2)|(int(a>=b)<<1)|(((a^b)&(a^diff))>>(bits-1)&1)
        elif op == 'compare-add':
            a,b=val(0),val(1); bits=self.values[ids[0]]['Width']; mask=(1<<bits)-1; total=a+b; answer=total&mask
            result=((answer>>(bits-1))<<3)|(int(answer==0)<<2)|(int(total>mask)<<1)|((~(a^b)&(a^answer))>>(bits-1)&1)
        elif op == 'condition-value':
            flags=val(0); negative,zero,carry,overflow=[bool(flags & bit) for bit in [8,4,2,1]]
            conditions=[zero,not zero,carry,not carry,negative,not negative,overflow,not overflow,carry and not zero,
                        not carry or zero,negative==overflow,negative!=overflow,not zero and negative==overflow,zero or negative!=overflow]
            result=int(conditions[n['Immediate']-1])
        elif op == 'zero': result=int(val(0)==0)
        elif op == 'nonzero': result=int(val(0)!=0)
        elif op == 'b.eq': result=int(bool(val(0)&4))
        elif op == 'b.ne': result=int(not(val(0)&4))
        elif op == 'partial-clobber': result=val(0)&((1<<n['Immediate'])-1)
        else: raise AssertionError(('unbound SSA value',hex(self.pc),key,op))
        if width: result &= (1<<width)-1
        if n['Address'] and op not in ['phi','call']: self.cache[key]=result
        return result
    def observe(self, pc, pending):
        for register,expected in self.expected:
            actual=self.register(register)
            assert actual==expected,(hex(self.last),register,hex(expected),hex(actual))
            self.checks+=1
        self.expected=[]
        for address,data in self.writes:
            assert bytes(self.uc.mem_read(address,len(data)))==data,(hex(self.last),hex(address),data.hex())
            self.checks+=1
        self.writes=[]
        if pc not in self.instructions:
            if hasattr(self,'target'):
                assert pc==self.target,(hex(self.last),'call target',hex(pc),hex(self.target))
                del self.target
            return
        instruction=self.instructions[pc]
        if pending and self.last is not None:
            previous=self.instructions[self.last]
            call=previous['Call']; node=self.values[call]
            if pending[1]=='normal-return':
                self.cache[call]=sum(self.register(f'x{i}')<<(64*i) for i in range(max(1,(node['Width']+63)//64)))
                for key in previous['Effects']:
                    n=self.values[key]
                    if n['Register'] and n['Register']!='memory': self.cache[key]=self.register(n['Register'])
            else:
                self.cache[f'exception_{self.last:x}']=self.register('x0')
                self.cache[f'selector_{self.last:x}']=self.register('x1')
                for key in self.definitions[self.last]:
                    n=self.values[key]
                    if key.startswith('exception_') and n['Register']:self.cache[key]=self.register(n['Register'])
        self.pc=pc
        for key in self.definitions[pc]: self.cache.pop(key,None)
        # Phi 输入同时取前驱的快照，不能先覆盖循环变量。
        phis=[]
        for key in self.definitions[pc]:
            n=self.values[key]
            if n['Operation']!='phi':continue
            incoming=[i for i in n['Incoming'] if i['Predecessor']==(self.last or 0)]
            assert len(incoming)==1,(hex(pc),key,self.last,incoming)
            phis.append((key,0 if n['Width']==0 else self.value(incoming[0]['Value'])))
        self.cache.update(phis)
        if instruction['Call']:
            call=self.values[instruction['Call']]
            target=self.value(call['Inputs'][0])
            self.target=target
            for i in range(9):
                expected=self.value(call['Inputs'][i+2]); actual=self.register(f'x{i}')
                assert expected==actual,(hex(pc),'call argument',i,hex(expected),hex(actual))
                self.checks+=1
            for i in range(min(8,len(call['Inputs'])-11)):
                expected=self.value(call['Inputs'][i+11]); actual=self.register(f'v{i}')
                assert expected==actual,(hex(pc),'vector argument',i,hex(expected),hex(actual))
                self.checks+=1
        else:
            for key in instruction['Effects']:
                n=self.values[key]; value=self.value(key)
                if n['Register'] and n['Register']!='memory':self.expected.append((n['Register'],value))
            if instruction['Condition']:
                taken=self.value(instruction['Condition'])
                # 真值在下一条实际指令的前驱边上验证。
                self.branch=(pc,taken)
        if hasattr(self,'branch') and self.branch[0]!=pc:
            before,taken=self.branch
            edge=next(e for e in self.flow[before]['Edges'] if e['Kind']==('taken' if taken else 'not-taken'))
            assert edge['Target']==pc,(hex(before),'branch',hex(pc),edge)
            self.checks+=1
            del self.branch
        self.last=pc
