"""ARM64 单指令差分测试的参照端：用 Unicorn 执行真实指令字，输出执行后的机器状态。

输入：每行 "pc word seed"（十六进制 pc/word，十进制 seed）。
输出：每行 JSON：{"pc","word","seed","status","x":[...31],"sp","q":[...32],"nzcv","next","writes":[[addr,size,value],...]}
初始状态完全由 seed 决定（splitmix64），与 C# 端 Evaluator 的约定一致：
  x[i] = mix(seed*64 + i)，q[i] = mix(seed*64 + 32 + i) | mix(seed*64 + 64 + i) << 64 （低/高 64 位），
  sp = mix(seed*64 + 31) & ~0xF，nzcv = (mix(seed*64 + 63) & 0xF) << 28。
  seed 为奇数时通用寄存器取值收窄到 48 位地址空间以内（访存指令可执行）。
未写过的内存字节 = Evaluator.MemoryByte(address)。
"""
import json, sys
import numpy as np
from unicorn import Uc, UcError, UC_ARCH_ARM64, UC_MODE_ARM, UC_HOOK_MEM_UNMAPPED, UC_HOOK_MEM_WRITE, UC_PROT_ALL
from unicorn.arm64_const import *
import capstone

CS = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM)

M64 = (1 << 64) - 1


def mix(x):
    z = (x + 0x9E3779B97F4A7C15) & M64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M64
    return z ^ (z >> 31)


def page_bytes(page):
    a = np.arange(page, page + 0x1000, dtype=np.uint64)
    with np.errstate(over='ignore'):
        z = a + np.uint64(0x9E3779B97F4A7C15)
        z = (z ^ (z >> np.uint64(30))) * np.uint64(0xBF58476D1CE4E5B9)
        z = (z ^ (z >> np.uint64(27))) * np.uint64(0x94D049BB133111EB)
        z = z ^ (z >> np.uint64(31))
    return (z & np.uint64(0xFF)).astype(np.uint8).tobytes()


def state(seed):
    base = seed * 64
    narrow = seed & 1
    x = []
    for i in range(31):
        v = mix(base + i)
        if narrow:
            v &= (1 << 47) - 1
        x.append(v)
    sp = mix(base + 31) & ~0xF
    if narrow:
        sp &= (1 << 47) - 1
    q = [mix(base + 32 + i) | (mix(base + 64 + i) << 64) for i in range(32)]
    nzcv = (mix(base + 63) & 0xF) << 28
    return x, sp, q, nzcv


X = [UC_ARM64_REG_X0 + i for i in range(29)] + [UC_ARM64_REG_X29, UC_ARM64_REG_X30]
Q = [UC_ARM64_REG_Q0 + i for i in range(32)]


def run(pc, word, seed):
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mapped = set()
    writes = []

    def ensure(addr, size):
        for page in {addr & ~0xFFF, (addr + size - 1) & ~0xFFF}:
            if page in mapped:
                continue
            if page >= (1 << 48):
                return False
            mu.mem_map(page, 0x1000, UC_PROT_ALL)
            mu.mem_write(page, page_bytes(page))
            mapped.add(page)
        return True

    def on_unmapped(uc, access, addr, size, value, data):
        return ensure(addr, size)

    def on_write(uc, access, addr, size, value, data):
        writes.append([addr, size, value & ((1 << (size * 8)) - 1)])

    ensure(pc, 4)
    mu.mem_write(pc, word.to_bytes(4, 'little'))
    x, sp, q, nzcv = state(seed)
    for r, v in zip(X, x):
        mu.reg_write(r, v)
    mu.reg_write(UC_ARM64_REG_SP, sp)
    for r, v in zip(Q, q):
        mu.reg_write(r, v)
    mu.reg_write(UC_ARM64_REG_NZCV, nzcv)
    mu.hook_add(UC_HOOK_MEM_UNMAPPED, on_unmapped)
    mu.hook_add(UC_HOOK_MEM_WRITE, on_write)
    status = 'ok'
    try:  # 外部模拟器的执行异常：如实记录为状态，不当作正常结果
        mu.emu_start(pc, pc + 4, count=1)
    except UcError as e:
        status = 'fault:' + str(e)
    asm = next((f'{i.mnemonic} {i.op_str}' for i in CS.disasm(word.to_bytes(4, 'little'), pc)), '?')
    return {
        'pc': pc, 'word': word, 'seed': seed, 'status': status, 'asm': asm,
        'x': [mu.reg_read(r) for r in X],
        'sp': mu.reg_read(UC_ARM64_REG_SP),
        'q': [mu.reg_read(r) for r in Q],
        'nzcv': mu.reg_read(UC_ARM64_REG_NZCV) >> 28,
        'next': mu.reg_read(UC_ARM64_REG_PC),
        'writes': writes,
    }


def main():
    out = open(sys.argv[2], 'w')
    for line in open(sys.argv[1]):
        pc, word, seed = line.split()
        r = run(int(pc, 16), int(word, 16), int(seed))
        r['x'] = [str(v) for v in r['x']]
        r['q'] = [str(v) for v in r['q']]
        r['sp'] = str(r['sp'])
        r['writes'] = [[str(a), s, str(v)] for a, s, v in r['writes']]
        out.write(json.dumps(r) + '\n')


main()
