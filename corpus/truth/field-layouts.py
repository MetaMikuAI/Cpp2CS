#!/usr/bin/env python3
"""从生成结构抽取独立的 LP64 C++ sizeof/offsetof 证据；在重任务锁内运行。
仅接受无继承、无联合体的直接字段结构，未知语法拒绝。引用替换为 void*，
值字段保留原结构；类型表的数组次序对应 ProgramModel.RuntimeTypes。
输出写到调用方指定的本地文件，不修改语料。
"""
import argparse
import json
import pathlib
import re
import subprocess
import tempfile

p = argparse.ArgumentParser()
p.add_argument('corpus', type=pathlib.Path)
p.add_argument('output', type=pathlib.Path)
a = p.parse_args()
cpp = a.corpus / 'artifacts/il2cppOutput/cpp'
records = {}
packs = {}
field = re.compile(r'\s*([\w:]+)(\*)?\s+(___\w+)(\[\d+\])?;\s*')
for path in sorted(cpp.glob('*.cpp')):
    text = path.read_text(encoding='utf-8-sig')
    for m in re.finditer(r'^struct (\w+)\s*\n\{\n([^{}]*?)^\};', text, re.M | re.S):
        # 只保留外层已知 pack 状态；内部联合体在结构语法筛选时拒绝。
        stack = [0]
        for directive in re.findall(r'^\s*#pragma pack\(([^)]*)\)', text[:m.start()], re.M):
            parts = [part.strip() for part in directive.split(',')]
            if parts[0] == 'push':
                stack.append(int(parts[-1]) if parts[-1].isdigit() else stack[-1])
            elif parts[0] == 'pop' and len(stack) > 1:
                stack.pop()
            elif len(parts) == 1 and parts[0].isdigit():
                stack[-1] = int(parts[0])
            else:
                raise ValueError('未知 pack 指令：' + directive)
        fields = []
        for line in m[2].splitlines():
            if not line.strip():
                continue
            f = field.fullmatch(line)
            if not f:
                break
            fields.append((f[1], bool(f[2]), f[3], f[4] or ''))
        else:
            records[m[1]] = fields
            packs[m[1]] = stack[-1]
primitives = {'bool', 'char', 'int8_t', 'uint8_t', 'int16_t', 'uint16_t', 'int32_t', 'uint32_t', 'int64_t', 'uint64_t', 'intptr_t', 'uintptr_t', 'float', 'double', 'Il2CppChar'}
accepted = {}
def accept(name, active):
    if name in accepted:
        return True
    if name not in records or name in active:
        return False
    fs = records[name]
    if not fs or any(not ptr and t not in primitives and not accept(t, active | {name}) for t, ptr, _, _ in fs):
        return False
    accepted[name] = fs
    return True
text = (cpp / 'Il2CppTypeDefinitions.c').read_text(encoding='utf-8-sig')
body = re.search(r'g_Il2CppTypeTable\[\d+\]\s*=\s*\{(.*?)\};', text, re.S)[1]
names = re.findall(r'&(\w+)', body)
selected = []
for index, name in enumerate(names):
    name = re.sub(r'_\d+_\d+_\d+$', '', name)
    if accept(name, set()):
        selected.append((index, name))
source = ['#include <cstdint>', '#include <cstddef>', '#include <cstdio>', 'using Il2CppChar = char16_t;']
for name, fields in accepted.items():
    source.append('#pragma pack(push, ' + str(packs[name]) + ')')
    source.append('struct ' + name + ' {')
    source.extend(('void*' if ptr else t) + ' ' + n + ar + ';' for t, ptr, n, ar in fields)
    source.append('};')
    source.append('#pragma pack(pop)')
source.append('int main() { static_assert(sizeof(void*) == 8);')
for index, name in selected:
    fs = accepted[name]
    fmt = '%zu ' * (2 + len(fs)) + '\\n'
    values = [f'sizeof({name})', f'alignof({name})'] + [f'offsetof({name}, {n})' for _, _, n, _ in fs]
    source.append(f'printf("{fmt}", ' + ', '.join(values) + ');')
source.append('}')
with tempfile.TemporaryDirectory(suffix='.local.layout') as temp:
    root = pathlib.Path(temp)
    (root / 'probe.cpp').write_text('\n'.join(source))
    subprocess.run(['c++', '-std=c++17', str(root / 'probe.cpp'), '-o', str(root / 'probe')], check=True)
    lines = subprocess.check_output([str(root / 'probe')], text=True).splitlines()
results = []
for (index, name), line in zip(selected, lines, strict=True):
    size, alignment, *offsets = map(int, line.split())
    results.append(dict(index=index, structure=name, size=size, alignment=alignment, offsets=offsets,
                        fields=[n for _, _, n, _ in accepted[name]]))
a.output.write_text(json.dumps(results, indent=2) + '\n')
print(f'C++ 结构证据：{len(results)} 个类型表项，{len(accepted)} 个结构定义；不支持的语法未纳入。')
