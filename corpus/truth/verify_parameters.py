#!/usr/bin/env python3
"""核对可复现性与用例关联，导出指定函数的机器码供人工抽查。"""
import argparse
import json
from pathlib import Path
import capstone
from elftools.elf.elffile import ELFFile
from extract import digest, require, write


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('input', 'truth', 'repeat', 'report'):
        parser.add_argument('--'+name, type=Path, required=True)
    parser.add_argument('--function', action='append', default=[], help='生成函数的完整名字，可重复')
    args = parser.parse_args()
    require(args.truth.resolve() != args.repeat.resolve(), '重复输出必须来自另一个目录')
    files = sorted(p.name for p in args.truth.glob('*.json'))
    require(files == sorted(p.name for p in args.repeat.glob('*.json')), '文件集合不同')
    require(all(digest(args.truth/f) == digest(args.repeat/f) for f in files), '重复输出不同')
    require(not args.report.exists(), '报告不得覆盖已有文件')
    require(not any(args.report.resolve().is_relative_to(p.resolve()) for p in (args.input, args.truth, args.repeat)), '报告不得写入输入目录')
    report = dict(reproducible_files=files, targets={})
    for target in ('arm64-v8a', 'x86_64'):
        rows = json.loads((args.truth/('parameters.'+target+'.json')).read_text())
        cases = json.loads((args.truth/('parameter-cases.'+target+'.json')).read_text())
        by_name = {r['cpp_name']:r for r in rows}
        require(len(by_name) == len(rows), '函数名重复')
        for c in cases:
            require(c['records'] == by_name[c['cpp_name']]['records'], '用例关联不一致')
            require(c['records'], '用例缺少 DWARF 记录')
        chosen = [by_name[n] for n in args.function]
        decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM) if target == 'arm64-v8a' else capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
        samples = []
        with (args.input/'artifacts/il2cppOutput/build'/target/'libil2cpp.so').open('rb') as stream:
            elf = ELFFile(stream)
            for row in chosen:
                start, size = int(row['address'], 16), row['size']
                segment = next(s for s in elf.iter_segments() if s['p_type'] == 'PT_LOAD' and s['p_vaddr'] <= start and start+size <= s['p_vaddr']+s['p_filesz'])
                stream.seek(segment['p_offset']+start-segment['p_vaddr'])
                code = stream.read(size)
                instructions = list(decoder.disasm_lite(code, start))
                require(sum(i[1] for i in instructions) == size, '机器码解码不完整')
                samples.append(dict(row, instructions=[dict(address=hex(a), size=n, mnemonic=m, operands=o) for a,n,m,o in instructions]))
        report['targets'][target] = dict(functions=len(rows), cases=len(cases), samples=samples)
    write(args.report, report)


if __name__ == '__main__':
    main()
