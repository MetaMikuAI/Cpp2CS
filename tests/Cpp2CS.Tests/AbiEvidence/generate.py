#!/usr/bin/env python3
"""重新生成：按本机约定加锁后执行 python3 tests/Cpp2CS.Tests/AbiEvidence/generate.py
只使用 gcc 与汇编观测，不调用产品分类器。四轮字节标记用于排除偶然相同值。
位置可能有多个：编译器可在未使用的实参槽保留临时副本，证据保留所有观测候选。
依据：https://gitlab.com/x86-psABIs/x86-64-ABI ，§3.2.3。
"""
import base64
import collections
import json
import pathlib
import random
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent
rng = random.Random(194271)
types = []
decls = []

def scalar(name, kind, size):
    types.append(dict(name=name, kind=kind, size=size, alignment=size, fields=[]))
    return len(types)-1

u8 = scalar('uint8_t', 'integer', 1)
u16 = scalar('uint16_t', 'integer', 2)
u32 = scalar('uint32_t', 'integer', 4)
u64 = scalar('uint64_t', 'integer', 8)
u128 = scalar('__uint128_t', 'integer', 16)
f32 = scalar('float', 'float', 4)
f64 = scalar('double', 'float', 8)
ptr = scalar('void*', 'pointer', 8)

def aggregate(shape, members, packed=False, alignment=0):
    name = 'T' + str(len(types))
    fields, code, offset, align = [], [], 0, 1
    for index, (tid, count) in enumerate(members):
        t = types[tid]
        a = 1 if packed else t['alignment']
        offset = (offset+a-1)//a*a
        fields.append(dict(offset=offset, type=tid, count=count))
        code.append(f"{t['name']} f{index}" + (f'[{count}]' if count > 1 else '') + ';')
        offset += t['size'] * count
        align = max(align, a)
    align = max(align, alignment)
    size = (offset+align-1)//align*align
    attrs = ('packed,' if packed else '') + f'aligned({align})'
    decls.append(f"typedef struct __attribute__(({attrs})) {{ {''.join(code)} }} {name};")
    types.append(dict(name=name, kind='aggregate', size=size, alignment=align, fields=fields, shape=shape))
    return len(types)-1

pair = aggregate('integer-pair', [(u64,1),(u64,1)])
aggregate('mixed', [(u64,1),(f64,1)])
aggregate('mixed', [(f64,1),(u64,1)])
aggregate('merged-eightbyte', [(f32,1),(u32,1)])
aggregate('float-pair', [(f32,2)])
aggregate('float-pair', [(f64,2)])
aggregate('large', [(u64,3)])
aggregate('large-float', [(f64,4)])
aggregate('padding', [(u8,1),(u64,1)])
aggregate('packed', [(u8,1),(f64,1)], packed=True)
aggregate('aligned', [(u64,2)], alignment=16)
aggregate('nested', [(pair,1)])
aggregate('array', [(u16,7)])
aggregate('empty', [])
aggregate('array', [(f32,3)])
aggregate('nested', [(pair,2),(f32,1)])
for i in range(24):
    aggregate('random', [(rng.choice([u8,u16,u32,u64,f32,f64,pair]), rng.randint(1,3))
                         for _ in range(rng.randint(1,4))], packed=i % 8 == 0)

cases = []
for i in range(360):
    # 每个返回形状都出现；高参数数目强制覆盖槽池耗尽与退回。
    args = [rng.randrange(len(types)) for _ in range(rng.randint(0,15))]
    if i % 6 == 0: args = [u64]*5 + [pair, u64, f64]
    if i % 6 == 1: args = [f64]*7 + [13, f64, u64]
    if i % 6 == 2: args = [u64]*7 + [u8,u128,u16]
    cases.append(dict(parameters=args, result=i % len(types)))

# 保留耗尽边界的重复试验，另补随机签名，去重后仍超过验收数量。
for i in range(160):
    cases.append(dict(parameters=[rng.randrange(len(types)) for _ in range(rng.randint(1,15))],
                      result=rng.randrange(len(types))))
assert len({(tuple(c['parameters']),c['result']) for c in cases}) >= 300

def leaves(tid, at=0):
    t = types[tid]
    if t['kind'] != 'aggregate': return list(range(at, at+t['size']))
    return [b for f in t['fields'] for k in range(f['count'])
            for b in leaves(f['type'], at+f['offset']+k*types[f['type']]['size'])]

# 每个字节的四轮标记是一个唯一的 32 位数；每个浮点值只经内存搬运。
def marker(token, trial):
    x = ((token+1)*2654435761) & 0xffffffff
    return (x >> (trial*8)) & 255

header = '#include <stdint.h>\n#include <stdio.h>\n#include <string.h>\n#include <stddef.h>\n'
code = [header, *decls]
for t in types:
    code.append(f'_Static_assert(sizeof({t["name"]})=={t["size"]},"size");')
    code.append(f'_Static_assert(_Alignof({t["name"]})=={t["alignment"]},"align");')
    for j,f in enumerate(t['fields']):
        code.append(f'_Static_assert(offsetof({t["name"]},f{j})=={f["offset"]},"offset");')
code.append('unsigned char captured[2224], returned[48], retbuf[256], retdata[256]; void (*retfn)(void);')
code.append('extern void probe(void); extern void result_probe(void); void (*volatile argfn)(void)=probe;')
code.append('static void fill(void* p,int n,unsigned base,int trial) { for(int j=0;j<n;j++) ((unsigned char*)p)[j]=((uint32_t)(base+j+1)*2654435761u)>>(trial*8); }')
for i,c in enumerate(cases):
    rt = types[c['result']]['name']
    code.append(f'__attribute__((noinline)) {rt} r{i}(void) {{ {rt} v; memcpy(&v,retdata,sizeof(v)); return v; }}')
    for j,tid in enumerate(c['parameters']): code.append(f'static {types[tid]["name"]} a{i}_{j};')
    argtypes = ','.join(types[t]['name'] for t in c['parameters']) or 'void'
    code.append(f'__attribute__((noinline)) static void call{i}(int trial) {{')
    for j,tid in enumerate(c['parameters']): code.append(f'fill(&a{i}_{j},sizeof(a{i}_{j}),{j*1024},trial);')
    code.append(f'(({rt}(*)({argtypes}))argfn)('+','.join(f'a{i}_{j}' for j in range(len(c['parameters'])))+');')
    code.append('fwrite(captured,1,sizeof(captured),stdout);')
    code.append(f'fill(retdata,{types[c["result"]]["size"]},32768,trial); memset(retbuf,0,256); retfn=(void(*)(void))r{i}; result_probe();')
    code.append('fwrite(returned,1,48,stdout); fwrite(retbuf,1,256,stdout);')
    code.append('unsigned char echo=0; uintptr_t p; memcpy(&p,returned,8); echo=p==(uintptr_t)retbuf; fwrite(&echo,1,1,stdout); }')
code.append('int main(void) { volatile unsigned char guard[4096]={0}; __asm__ volatile(""::"m"(guard):"memory");')
for i in range(len(cases)): code.append(f'for(int trial=0;trial<4;trial++) call{i}(trial);')
code.append('return 0;}')
asm = ['.text','.globl probe','probe:']
for i,r in enumerate(['rdi','rsi','rdx','rcx','r8','r9']): asm.append(f'movq %{r}, captured+{i*8}(%rip)')
for i in range(8): asm.append(f'movdqu %xmm{i}, captured+{48+i*16}(%rip)')
asm += ['leaq 8(%rsp), %r10','leaq captured+176(%rip), %r11']
for i in range(256): asm += [f'movq {i*8}(%r10), %rax',f'movq %rax, {i*8}(%r11)']
asm += ['movq %rdi,%rax','ret','.globl result_probe','result_probe:', 'subq $8,%rsp','leaq retbuf(%rip),%rdi','call *retfn(%rip)',
        'movq %rax,returned(%rip)','movq %rdx,returned+8(%rip)', 'movdqu %xmm0,returned+16(%rip)',
        'movdqu %xmm1,returned+32(%rip)','addq $8,%rsp','ret','.section .note.GNU-stack,"",@progbits']
with tempfile.TemporaryDirectory(prefix='abi-evidence.local.') as tmp:
    p = pathlib.Path(tmp)
    (p/'cases.c').write_text('\n'.join(code))
    (p/'probe.S').write_text('\n'.join(asm)+'\n')
    subprocess.run(['gcc','-std=gnu11','-O2','-fno-lto','-Wno-incompatible-pointer-types',str(p/'cases.c'),str(p/'probe.S'),'-o',str(p/'probe')],check=True)
    raw = subprocess.check_output([str(p/'probe')])
compiler = subprocess.check_output(['gcc','-dumpfullversion'],text=True).strip()
stride=2224+48+256+1
assert len(raw)==len(cases)*4*stride

def locations(trials):
    result=collections.defaultdict(list)
    for b,values in enumerate(zip(*trials)): result[bytes(values)].append(b)
    return result

def observed(positions, token):
    return positions.get(bytes(marker(token,k) for k in range(4)),[])

for i,c in enumerate(cases):
    trials=[raw[(i*4+k)*stride:(i*4+k+1)*stride] for k in range(4)]
    arg_positions=locations([t[:2224] for t in trials])
    ret_positions=locations([t[2224:2528] for t in trials])
    c['arguments']=[[[b,observed(arg_positions,j*1024+b)] for b in leaves(tid)]
                    for j,tid in enumerate(c['parameters'])]
    c['returns']=[[b,observed(ret_positions,32768+b)] for b in leaves(c['result'])]
    c['echo']=all(t[-1]==1 for t in trials)
    # 原始快照随证据保存；位置推导可独立复核。
    c['snapshots']=base64.b64encode(b''.join(trials)).decode()
    assert all(loc for arg in c['arguments'] for _,loc in arg), ('missing argument',i)
    assert all(loc for _,loc in c['returns']), ('missing return',i)
coverage=collections.Counter(types[t].get('shape',types[t]['kind']) for c in cases for t in c['parameters'])
return_coverage=collections.Counter(types[c['result']].get('shape',types[c['result']]['kind']) for c in cases)
data=dict(format=1,compiler='gcc '+compiler,seed=194271,coverage=dict(coverage),returnCoverage=dict(return_coverage),types=types,cases=cases)
(ROOT/'sysv.json').write_text(json.dumps({k:v for k,v in data.items() if k!='cases'},indent=2)[:-1]+',\n\"cases\":[\n'+',\n'.join(json.dumps(c,separators=(",",":")) for c in cases)+'\n]}\n')
print(json.dumps(dict(signatures=len(cases),arguments=coverage,returns=return_coverage),indent=2))
