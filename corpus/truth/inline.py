#!/usr/bin/env python3
"""抽取 DWARF 内联树，比较源码调用、直接机器调用和内联记录。"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import capstone
from elftools.elf.elffile import ELFFile
from elftools.dwarf.descriptions import describe_form_class
from extract import digest, require, write


def inherited(die, key):
    if key in die.attributes:
        return die.attributes[key].value
    for ref in ('DW_AT_abstract_origin', 'DW_AT_specification'):
        if ref in die.attributes:
            value = inherited(die.get_DIE_from_attribute(ref), key)
            if value is not None:
                return value
    return None


def decoded(value):
    return value.decode('utf-8') if isinstance(value, bytes) else value


def ranges(die, dwarf, cu):
    attrs = die.attributes
    if 'DW_AT_ranges' in attrs:
        base = cu.get_top_DIE().attributes.get('DW_AT_low_pc')
        base = base.value if base else 0
        result = []
        for entry in dwarf.range_lists().get_range_list_at_offset(attrs['DW_AT_ranges'].value, cu):
            if hasattr(entry, 'base_address'):
                base = entry.base_address
            else:
                offset = 0 if entry.is_absolute else base
                result.append([offset + entry.begin_offset, offset + entry.end_offset])
        return result
    if 'DW_AT_low_pc' in attrs and 'DW_AT_high_pc' in attrs:
        low, high = attrs['DW_AT_low_pc'].value, attrs['DW_AT_high_pc']
        return [[low, high.value + (0 if describe_form_class(high.form) == 'address' else low)]]
    return []


def extract_debug(path, wanted, generated, methods):
    result = defaultdict(list)
    with path.open('rb') as stream:
        dwarf = ELFFile(stream).get_dwarf_info()
        for cu in dwarf.iter_CUs():
            line = dwarf.line_program_for_CU(cu)
            def file_at(index):
                if index is None or line is None:
                    return None
                entry = line['file_entry'][index - (0 if cu['version'] >= 5 else 1)]
                # 编译机目录不进入输出；文件表索引保留以区分同名文件。
                return decoded(entry.name).replace('\\', '/').split('/')[-1]
            def walk(die, owners, parent):
                if die.tag == 'DW_TAG_subprogram':
                    rs = ranges(die, dwarf, cu)
                    owners = sorted({name for lo, hi in rs for name in wanted.get(lo, [])})
                    for owner in owners:
                        result.setdefault(owner, [])
                    parent = None
                elif die.tag == 'DW_TAG_inlined_subroutine' and owners:
                    name = decoded(inherited(die, 'DW_AT_name'))
                    linkage = decoded(inherited(die, 'DW_AT_linkage_name'))
                    match = name if name in generated else linkage if linkage in generated else None
                    rs = ranges(die, dwarf, cu)
                    record = dict(id=hex(die.offset), parent=parent, name=name, linkage_name=linkage,
                                  generated_name=match, method_ids=sorted(methods.get(match, [])),
                                  origin='generated' if match and generated[match]['sources'] else 'runtime_or_library',
                                  declaration_file=file_at(inherited(die, 'DW_AT_decl_file')),
                                  declaration_line=inherited(die, 'DW_AT_decl_line'),
                                  ranges=[[hex(lo), hex(hi)] for lo, hi in rs],
                                  call_file=file_at(inherited(die, 'DW_AT_call_file')),
                                  call_file_index=inherited(die, 'DW_AT_call_file'),
                                  call_line=inherited(die, 'DW_AT_call_line'),
                                  cu_offset=hex(cu.cu_offset))
                    for owner in owners:
                        result[owner].append(record)
                    parent = record['id']
                for child in die.iter_children():
                    walk(child, owners, parent)
            walk(cu.get_top_DIE(), [], None)
            # pyelftools 默认驻留整个 CU；逐单元释放 DIE 与行表缓存。
            cu._dielist.clear()
            cu._diemap.clear()
            dwarf._linetable_cache.clear()
    return result


LEX = re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'', re.S)
CALL = re.compile(r'\b([A-Za-z_]\w*)\s*(?:<[^;{}\n]*>)?\s*\)?\s*\(')
KEYWORDS = {'if', 'while', 'for', 'switch', 'sizeof', 'return', 'alignof', 'decltype', 'static_cast', 'reinterpret_cast', 'const_cast'}


def source_calls(root, generated):
    files = {}
    result = {}
    for name, row in generated.items():
        calls = []
        for source in row['sources']:
            filename = source['file']
            if filename not in files:
                text = (root / filename).read_text(encoding='utf-8-sig')
                files[filename] = LEX.sub(lambda m: re.sub(r'[^\n]', ' ', m[0]), text).splitlines()
            for number in range(source['start_line'] + 1, source['end_line'] + 1):
                for match in CALL.finditer(files[filename][number - 1]):
                    callee = match[1]
                    if callee not in KEYWORDS:
                        calls.append(dict(name=callee, file=filename, line=number,
                                          known=callee in generated))
        result[name] = calls
    return result


def plt_names(elf, target):
    """由跳板实际读取的 GOT 槽关联重定位，不按符号顺序猜地址。"""
    relocations = elf.get_section_by_name('.rela.plt')
    section = elf.get_section_by_name('.plt')
    if relocations is None or section is None:
        return {}
    symbols = elf.get_section(relocations['sh_link'])
    slots = {r['r_offset']: symbols.get_symbol(r['r_info_sym']).name for r in relocations.iter_relocations()}
    decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM) if target == 'arm64-v8a' else capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    decoder.detail = True
    pages, result = {}, {}
    for ins in decoder.disasm(section.data(), section['sh_addr']):
        ops = ins.operands
        if target == 'arm64-v8a':
            if ins.mnemonic == 'adrp':
                pages[ops[0].reg] = (ops[1].imm, ins.address)
            elif ins.mnemonic == 'ldr' and len(ops) == 2 and ops[1].type == capstone.arm64.ARM64_OP_MEM:
                memory = ops[1].mem
                if memory.base in pages:
                    base, start = pages[memory.base]
                    slot = base + memory.disp
                    if slot in slots:
                        result[start] = slots[slot]
        elif ins.mnemonic == 'jmp' and ops[0].type == capstone.x86.X86_OP_MEM and ops[0].mem.base == capstone.x86.X86_REG_RIP:
            slot = ins.address + ins.size + ops[0].mem.disp
            if slot in slots:
                result[ins.address] = slots[slot]
    return result


def analyze(root, target, functions, selected, records, sources, generated):
    address_names = defaultdict(set)
    for function in functions:
        if function['defined']:
            address_names[int(function['address'], 16)].add(function['cpp_name'] or function['name'])
    decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM) if target == 'arm64-v8a' else capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    result = []
    with (root / 'artifacts/il2cppOutput/build' / target / 'libil2cpp.so').open('rb') as stream:
        elf = ELFFile(stream)
        plt = plt_names(elf, target)
        for address, name in plt.items():
            address_names[address].add(name)
        segments = [(s['p_vaddr'], s.data()) for s in elf.iter_segments() if s['p_type'] == 'PT_LOAD']
        for name, function in sorted(selected.items()):
            start, size = int(function['address'], 16), function['size']
            data = next(data[start-base:start-base+size] for base, data in segments if base <= start and start+size <= base+len(data))
            direct = []
            consumed = 0
            for address, length, mnemonic, operands in decoder.disasm_lite(data, start):
                consumed += length
                if mnemonic in ('bl', 'b', 'call', 'jmp') and re.fullmatch(r'#?0x[0-9a-f]+', operands):
                    destination = int(operands.lstrip('#'), 16)
                    if mnemonic in ('b', 'jmp') and start <= destination < start+size:
                        continue
                    direct.append(dict(address=hex(address), target=hex(destination), names=sorted(address_names[destination]), via_plt=destination in plt, tail=mnemonic in ('b', 'jmp')))
            require(consumed == size, f'反汇编不完整：{target} {name} {consumed}/{size}')
            called = {n for call in direct for n in call['names']}
            inline = {n for r in records.get(name, []) for n in (r['generated_name'], r['name'], r['name'].split('<', 1)[0] if r['name'] else None) if n}
            calls = []
            for call in sources.get(name, []):
                callee = call['name']
                status = ('direct' if callee in called else 'inline' if callee in inline else 'missing_candidate') if call['known'] else ('runtime_inline' if callee in inline else 'unknown')
                matches = [r for r in records.get(name, []) if callee in (r['generated_name'], r['name'], (r['name'] or '').split('<', 1)[0])]
                calls.append(dict(call, status=status, candidate_class=generated[callee]['kind'] if status == 'missing_candidate' else None, matching_inline_ids=[r['id'] for r in matches], callsite_inline_ids=[r['id'] for r in matches if r['call_file']==call['file'] and r['call_line']==call['line']]))
            source_names = {c['name'] for c in calls}
            extra = [dict(id=r['id'], name=r['name'], origin=r['origin'], parent=r['parent'], reason='nested_inline' if r['parent'] else 'header_template_or_macro_candidate' if r['origin']=='runtime_or_library' else 'unresolved') for r in records.get(name, []) if r['generated_name'] not in source_names and r['name'] not in source_names and (r['name'] or '').split('<', 1)[0] not in source_names]
            result.append(dict(cpp_name=name, address=function['address'], size=size, source_available=bool(generated.get(name, {}).get('sources')), calls=calls, direct_calls=direct, extra_inline=extra))
    return result


def summary(rows):
    counts = Counter(call['status'] for row in rows for call in row['calls'])
    known = sum(counts[s] for s in ('direct', 'inline', 'missing_candidate'))
    return dict(candidate_classes=dict(sorted(Counter(c['candidate_class'] for r in rows for c in r['calls'] if c['status']=='missing_candidate').items())), functions=len(rows), source_available=sum(r['source_available'] for r in rows), calls=dict(sorted(counts.items())), known_calls=known, candidate_fraction=counts['missing_candidate']/known if known else None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('input', 'truth', 'output', 'cache'):
        parser.add_argument('--'+name, type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists() or not any(args.output.iterdir()), '输出目录必须为空')
    require(not args.output.resolve().is_relative_to(args.truth.resolve()), '不在已有真值目录中写入')
    require(not args.output.resolve().is_relative_to(args.input.resolve()), '不在产物输入目录中写入')
    require(args.cache.resolve() != args.output.resolve(), '缓存与输出必须分开')
    require(not args.cache.resolve().is_relative_to(args.input.resolve()) and not args.cache.resolve().is_relative_to(args.truth.resolve()), '缓存不能写入输入目录')
    args.output.mkdir(parents=True, exist_ok=True)
    args.cache.mkdir(parents=True, exist_ok=True)
    load = lambda name: json.loads((args.truth/(name+'.json')).read_text())
    manifest = load('manifest')
    for filename, expected in manifest['outputs'].items():
        require(digest(args.truth/filename) == expected, f'真值校验失败：{filename}')
    for item in manifest['inputs']:
        path = (args.input/item['path']).resolve()
        require(path.is_relative_to(args.input.resolve()), '输入路径越界')
        require(path.stat().st_size == item['bytes'] and digest(path) == item['sha256'], f'产物校验失败：{item["path"]}')
    generated = {g['name']: g for g in load('generated')}
    mappings, cases = load('mappings'), load('cases')
    methods = defaultdict(set)
    for m in mappings:
        if m['method_id']:
            methods[m['cpp_name']].add(m['method_id'])
    sources = source_calls(args.input/'artifacts/il2cppOutput/cpp', generated)
    report = {}
    for target in ('arm64-v8a', 'x86_64'):
        functions = load('functions.'+target)
        selected = {f['cpp_name']: f for f in functions if f['defined'] and f['cpp_name'] in methods}
        wanted = defaultdict(list)
        for name, f in selected.items():
            wanted[int(f['address'], 16)].append(name)
        debug = args.input/'artifacts/il2cppOutput/build'/target/'libil2cpp.dbg.so'
        key = digest(debug)+digest(Path(__file__))+digest(args.truth/'mappings.json')+digest(args.truth/'generated.json')+digest(args.truth/('functions.'+target+'.json'))
        cached = args.cache/(target+'.local.json')
        previous = json.loads(cached.read_text()) if cached.exists() else None
        if previous and previous['key'] == key:
            records = previous['records']
        else:
            print('DWARF', target, flush=True)
            records = extract_debug(debug, wanted, generated, methods)
            write(cached, dict(key=key, records=records))
        rows = [dict(cpp_name=name, method_ids=sorted(methods[name]), address=f['address'], size=f['size'], debug_function_found=name in records, records=records.get(name, [])) for name, f in sorted(selected.items())]
        write(args.output/('inlines.'+target+'.json'), rows)
        analysis = analyze(args.input, target, functions, selected, records, sources, generated)
        write(args.output/('inline-audit.'+target+'.json'), analysis)
        by_name = {r['cpp_name']: r for r in rows}
        case_names = {c['mapping']['cpp_name'] for c in cases}
        require(case_names <= by_name.keys(), '用例入口缺失')
        write(args.output/('inline-cases.'+target+'.json'), [dict(case=c['case'], method_id=c['method']['id'], **by_name[c['mapping']['cpp_name']]) for c in cases])
        report[target] = dict(all=summary(analysis), cases=summary([r for r in analysis if r['cpp_name'] in case_names]), debug_functions=sum(r['debug_function_found'] for r in rows), records=sum(len(r['records']) for r in rows), case_records=sum(len(by_name[n]['records']) for n in case_names), debug_sha256=digest(debug))
        print(target, report[target], flush=True)
    write(args.output/'inline-summary.json', report)
    write(args.output/'inline-manifest.json', dict(version=1, tool_sha256=digest(Path(__file__)), dependencies=dict(pyelftools='0.32', capstone=capstone.__version__), inputs={p.name:digest(p) for p in sorted(args.truth.glob('*.json'))}, outputs={p.name:digest(p) for p in sorted(args.output.glob('*.json'))}))


if __name__ == '__main__':
    main()
