#!/usr/bin/env python3
"""读取裁剪程序集、v31 元数据、生成注册表和 ELF64 符号，输出确定性真值。"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess

VERSION = 1


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + '\n', encoding='utf-8')


def array(text, name):
    m = re.search(r'\b' + re.escape(name) + r'\s*\[\s*(\d*)\s*\]\s*=\s*\{(.*?)\n\};', text, re.S)
    require(m is not None, f'缺少注册数组 {name}')
    body = re.sub(r'//[^\n]*|/\*.*?\*/', '', m[2], flags=re.S)
    items = [x.strip() for x in body.split(',') if x.strip()]
    if m[1]:
        require(len(items) == int(m[1]), f'{name} 长度不一致')
    return [re.sub(r'^\(Il2CppMethodPointer\)\s*&?', '', x) for x in items]


def elf_functions(path):
    data = path.read_bytes()
    require(data[:6] == b'\x7fELF\x02\x01', '仅支持小端 ELF64')
    shoff = struct.unpack_from('<Q', data, 40)[0]
    entsize, count, names_index = struct.unpack_from('<HHH', data, 58)
    require(entsize == 64 and count > 0 and names_index < count, '不支持扩展节表')
    sections = [struct.unpack_from('<IIQQQQIIQQ', data, shoff + i * entsize) for i in range(count)]
    def string(table, offset):
        return table[offset:table.index(b'\0', offset)].decode('utf-8')
    ns = sections[names_index]
    names = data[ns[4]:ns[4] + ns[5]]
    tables = [s for s in sections if s[1] == 2]
    require(len(tables) == 1, '需要恰好一个完整 .symtab')
    s = tables[0]
    require(s[9] == 24 and s[5] % 24 == 0, '符号表布局错误')
    st = sections[s[6]]
    strings = data[st[4]:st[4] + st[5]]
    rows = []
    for offset in range(s[4], s[4] + s[5], 24):
        name, info, other, section, address, size = struct.unpack_from('<IBBHQQ', data, offset)
        if info & 15 not in (2, 10):
            continue
        rows.append(dict(symbol_index=(offset-s[4])//24, name=string(strings, name),
                         address=f'0x{address:x}', size=size, section_index=section,
                         section=string(names, sections[section][0]) if 0 < section < count else None,
                         defined=section != 0, binding=info >> 4, visibility=other & 3,
                         symbol_type='IFUNC' if info & 15 == 10 else 'FUNC'))
    groups = defaultdict(list)
    for row in rows:
        if row['defined']:
            groups[(row['section_index'], row['address'])].append(row['symbol_index'])
    for row in rows:
        row['same_address_symbols'] = groups[(row['section_index'], row['address'])] if row['defined'] else []
        row['duplicate_address'] = len(row['same_address_symbols']) > 1
    return sorted(rows, key=lambda r: (int(r['address'], 16), r['name'], r['symbol_index']))


def metadata_methods(path, methods):
    data = path.read_bytes()
    require(struct.unpack_from('<II', data) == (0xFAB11BAF, 31), '仅支持元数据 v31')
    def table(index, size):
        offset, length = struct.unpack_from('<II', data, 8 + index*8)
        require(length % size == 0 and offset + length <= len(data), '元数据表边界错误')
        return range(offset, offset+length, size)
    string_offset, string_size = struct.unpack_from('<II', data, 24)
    strings = data[string_offset:string_offset+string_size]
    def string(index):
        return strings[index:strings.index(b'\0', index)].decode('utf-8')
    type_images = {}
    for offset in table(20, 40):
        name, _, start, count = struct.unpack_from('<IiiI', data, offset)
        for i in range(start, start+count):
            type_images[i] = string(name)
    types = list(table(19, 88))
    by_id = {m['id']: m for m in methods}
    result, missing = [], []
    for offset in table(5, 36):
        name, declaring = struct.unpack_from('<Ii', data, offset)
        token = struct.unpack_from('<I', data, offset+24)[0]
        key = f'{type_images[declaring]}:0x{token:08x}'
        if key not in by_id:
            require(type_images[declaring] not in {m['assembly'] for m in methods}, f'已知程序集缺少标记：{key}')
            missing.append(dict(metadata_method_id=key, metadata_index=len(result), name=string(name), reason='metadata_image_without_managed_input'))
            result.append(key)
            continue
        m = by_id[key]
        require(m['name'] == string(name), f'元数据方法名不一致：{key}')
        type_token = struct.unpack_from('<I', data, types[declaring]+84)[0]
        m['metadata_index'] = len(result)
        m['declaring_type_token'] = f'0x{type_token:08x}'
        result.append(key)
    return result, missing


def cpp_definitions(root):
    rows = []
    # 先屏蔽注释和字符串，保留换行与列位置，再配对花括号。
    lex = re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'', re.S)
    for path in sorted(root.glob('*.cpp')):
        text = path.read_text(encoding='utf-8-sig')
        original_lines = text.splitlines()
        clean = lex.sub(lambda m: re.sub(r'[^\n]', ' ', m[0]), text)
        lines = clean.splitlines(keepends=True)
        for i, line in enumerate(lines[:-1]):
            if not line or line[0].isspace() or line.startswith(('#', '//')):
                continue
            m = re.search(r'\b([A-Za-z_]\w*)\s*\([^;]*\)\s*$', line)
            if not m or lines[i+1].strip() != '{':
                continue
            depth, end = 0, None
            for j in range(i+1, len(lines)):
                depth += lines[j].count('{') - lines[j].count('}')
                if depth == 0:
                    end = j+1
                    break
            require(end is not None, f'C++ 函数体不完整：{path.name}:{i+1}')
            previous = i-1
            while previous >= 0 and not original_lines[previous].strip():
                previous -= 1
            comment = original_lines[previous][2:].strip() if previous >= 0 and original_lines[previous].startswith('//') else None
            rows.append(dict(name=m[1], file=path.name, start_line=i+1, end_line=end,
                             managed_comment=comment, declaration=line.strip()))
    return rows


def kind(name):
    if re.search(r'_marshal_(?:pinvoke|com)(?:_back|_cleanup)?$', name):
        return 'marshal_helper'
    if name.startswith('DelegatePInvokeWrapper_'):
        return 'delegate_pinvoke_wrapper'
    if re.search(r'_m[0-9A-F]{40}_(?:Multicast|(?:Open|Closed)(?:Inst|Static|GenericInterface|GenericVirtual|Interface|Virtual)(?:Invoker)?)$', name):
        return 'delegate_helper'
    if name.startswith('RuntimeInvoker_'):
        return 'invoker'
    if name.endswith('_AdjustorThunk'):
        return 'adjustor_thunk'
    if name.endswith('_inline'):
        return 'inline_copy'
    if '_gshared' in name:
        return 'shared_generic'
    if re.search(r'_m[0-9A-F]{40}$', name):
        return 'method'
    return 'generated_other'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--dotnet', required=True)
    parser.add_argument('--cxxfilt', default='c++filt')
    parser.add_argument('--managed-reader', type=Path, required=True)
    parser.add_argument('--cases', type=Path, default=Path(__file__).resolve().parents[1]/'cases/methods.json')
    args = parser.parse_args()
    root, output = args.input.resolve(), args.output.resolve()
    require(not output.is_relative_to(root), '输出必须在输入产物目录之外')
    require(not output.exists() or not any(output.iterdir()), '输出目录必须为空，避免残留真值')
    cpp = root/'artifacts/il2cppOutput/cpp'
    managed = root/'artifacts/ManagedStripped'
    methods = json.loads(subprocess.check_output([args.dotnet, str(args.managed_reader), str(managed)], text=True))
    methods.sort(key=lambda m: m['id'])
    independent = []
    for m in methods:
        encoded = m.pop('cecil_il_hex')
        if encoded is not None:
            require(encoded == m['il_hex'], f'Cecil 与原始 IL 不一致：{m["id"]}')
            independent.append(m['id'])
        m['assembly_path'] = f'artifacts/ManagedStripped/{m["assembly"]}'
    meta_ids, missing_metadata = metadata_methods(root/'artifacts/il2cppOutput/data/Metadata/global-metadata.dat', methods)
    by_id = {m['id']: m for m in methods}
    sources = cpp_definitions(cpp)
    source_by_name = defaultdict(list)
    for row in sources:
        source_by_name[row['name']].append(row)
    functions, native = {}, {}
    for lib in sorted((root/'artifacts/il2cppOutput/build').glob('*/libil2cpp.sym.so')):
        target = lib.parent.name
        functions[target] = elf_functions(lib)
        native[target] = defaultdict(list)
        demangled = subprocess.check_output([args.cxxfilt], input='\n'.join(f['name'] for f in functions[target])+'\n', text=True).splitlines()
        require(len(demangled) == len(functions[target]), 'c++filt 输出数量错误')
        for f, readable in zip(functions[target], demangled):
            f['demangled_name'] = readable
            base = readable.split('(', 1)[0]
            f['cpp_name'] = base if base in source_by_name else None
            if f['defined']:
                native[target][f['name']].append(f)
                if f['cpp_name'] and f['cpp_name'] != f['name']:
                    native[target][f['cpp_name']].append(f)
    require(len(functions) == 2, '验收要求两个目标')
    def addresses(name):
        return {t: [dict(symbol_index=f['symbol_index'], symbol_name=f['name'], address=f['address'], size=f['size'], section=f['section'])
                    for f in native[t].get(name, [])] for t in functions}
    edges = []
    def edge(method_id, name, role, evidence, **extra):
        if name in ('NULL', '0'):
            return
        require(re.fullmatch(r'[A-Za-z_]\w*', name), f'不支持的函数指针表达式：{name}')
        edges.append(dict(method_id=method_id if method_id in by_id else None, metadata_method_id=method_id, cpp_name=name, role=role, evidence=evidence,
                          targets=addresses(name), sources=source_by_name.get(name, []), **extra))
    invokers = array((cpp/'Il2CppInvokerTable.cpp').read_text(encoding='utf-8-sig'), 'g_Il2CppInvokerPointers')
    for file in sorted(cpp.glob('*_CodeGen.c')):
        text = file.read_text(encoding='utf-8-sig')
        assembly = re.search(r'"([^"\n]+)"\s*,', text)
        require(assembly is not None, f'缺少模块名：{file.name}')
        if not re.search(r's_methodPointers\s*\[', text):
            continue
        pointers, indices = array(text, 's_methodPointers'), array(text, 's_InvokerIndices')
        require(len(pointers) == len(indices), f'注册表长度不一致：{file.name}')
        for i, name in enumerate(pointers):
            key = f'{assembly[1]}:0x{0x06000001+i:08x}'
            require(key in meta_ids, f'注册槽位不存在：{key}')
            evidence = f'{file.name}:s_methodPointers[{i}]'
            edge(key, name, 'ordinary', evidence)
            if name not in ('NULL', '0'):
                for suffix, role in [('_inline', 'inline_copy'), ('_AdjustorThunk', 'adjustor_thunk')]:
                    if name+suffix in source_by_name or any(name+suffix in n for n in native.values()):
                        edge(key, name+suffix, role, evidence+' + exact suffix')
                index = int(indices[i])
                if index >= 0:
                    edge(key, invokers[index], 'invoker', f'{file.name}:s_InvokerIndices[{i}]={index}')
    def tuples(file, width):
        text = (cpp/file).read_text(encoding='utf-8-sig')
        pattern = r'\{\s*' + r'\s*,\s*'.join([r'(-?\d+)']*width) + r'\s*\}'
        return [tuple(map(int, m)) for m in re.findall(pattern, text)]
    specs = tuples('Il2CppGenericMethodDefinitions.c', 3)
    generic_ptrs = array((cpp/'Il2CppGenericMethodPointerTable.c').read_text(encoding='utf-8-sig'), 'g_Il2CppGenericMethodPointers')
    adjustors = array((cpp/'Il2CppGenericAdjustorThunkTable.c').read_text(encoding='utf-8-sig'), 'g_Il2CppGenericAdjustorThunks')
    for spec, pointer, invoker, adjustor in tuples('Il2CppGenericMethodTable.c', 4):
        method, class_inst, method_inst = specs[spec]
        key = meta_ids[method]
        extra = dict(method_spec_index=spec, class_inst_index=class_inst, method_inst_index=method_inst)
        evidence = f'Il2CppGenericMethodTable.c:spec[{spec}] -> metadata method[{method}]'
        if pointer >= 0:
            name = generic_ptrs[pointer]
            edge(key, name, 'shared_generic' if '_gshared' in name else 'generic_instance', evidence, **extra)
            if name+'_inline' in source_by_name:
                edge(key, name+'_inline', 'inline_copy', evidence+' + exact suffix', **extra)
        if invoker >= 0:
            edge(key, invokers[invoker], 'invoker', evidence, **extra)
        if adjustor >= 0:
            edge(key, adjustors[adjustor], 'adjustor_thunk', evidence, **extra)
    # 无注释的泛型包装函数只按函数体中唯一的已注册调用目标关联。
    registered = defaultdict(list)
    for e in edges:
        if e['role'] in ('shared_generic', 'generic_instance'):
            registered[e['cpp_name']].append(e)
    body_files = {}
    for source in sources:
        if not source['declaration'].startswith('inline '):
            continue
        if source['file'] not in body_files:
            body_files[source['file']] = (cpp/source['file']).read_text(encoding='utf-8-sig').splitlines()
        body = body_files[source['file']][source['start_line']:source['end_line']]
        statements = [line.strip() for line in body if line.strip()]
        if len(statements) != 3 or statements[0] != '{' or statements[-1] != '}' or not statements[1].startswith('return '):
            continue
        referenced = set(re.findall(r'\b[A-Za-z_]\w*_m[0-9A-F]{40}(?:_gshared\w*)?\b', '\n'.join(body))) & registered.keys()
        if len(referenced) != 1:
            continue
        forwarded = next(iter(referenced))
        ids = {e['metadata_method_id'] for e in registered[forwarded]}
        if len(ids) == 1:
            edge(next(iter(ids)), source['name'], 'generic_wrapper',
                 f"{source['file']}:{source['start_line']}-{source['end_line']}: unique registered callee",
                 forwarded_to=forwarded, forwarded_targets=addresses(forwarded))
    spec_names = defaultdict(set)
    for e in edges:
        if 'method_spec_index' in e and e['role'] in ('shared_generic', 'generic_instance'):
            spec_names[e['method_spec_index']].add(e['cpp_name'])
    instances = [dict(method_spec_index=i, metadata_method_id=meta_ids[m],
                      method_id=meta_ids[m] if meta_ids[m] in by_id else None,
                      class_inst_index=c, method_inst_index=g,
                      cpp_names=sorted(spec_names[i]))
                 for i, (m, c, g) in enumerate(specs)]
    edges.sort(key=lambda e: (e['metadata_method_id'], e['role'], e['cpp_name'], e.get('method_spec_index', -1)))
    method_edges = defaultdict(list)
    for e in edges:
        method_edges[e['method_id']].append(e)
    cases = json.loads(args.cases.read_text())
    snapshot_cases = root/'source/cases/methods.json'
    require(cases == json.loads(snapshot_cases.read_text(encoding='utf-8-sig')), '用例清单与产物快照不一致')
    views = []
    for case in cases:
        matches = [m for m in methods if m['declaring_type'] == case['type'] and m['name'] == case['method']]
        require(len(matches) == 1, f'用例方法不唯一：{case}')
        m = matches[0]
        linked = [e for e in method_edges[m['id']] if e['role'] == 'ordinary']
        require(len(linked) == 1, f'用例普通函数不唯一：{m["id"]}')
        e = linked[0]
        require(re.fullmatch(re.escape(case['symbolPrefix']) + '[0-9A-F]{40}', e['cpp_name']), '用例前缀与注册表不一致')
        require(all(len(v) == 1 for v in e['targets'].values()), f'用例目标符号不唯一：{m["id"]}')
        require(len(e['sources']) == 1, f'用例 C++ 函数体不唯一：{m["id"]}')
        views.append(dict(case=case, method=m, mapping=e))
    case_assemblies = {v['method']['assembly'] for v in views}
    coverage = []
    for m in methods:
        body_edges = [e for e in method_edges[m['id']] if e['role'] in ('ordinary', 'generic_instance', 'shared_generic')]
        if not m['has_body']:
            status = 'no_managed_body'
        elif any(all(e['targets'].values()) for e in body_edges):
            status = 'mapped_both_targets'
        elif body_edges:
            status = 'registered_but_native_symbol_missing'
        elif m['generic_arity'] or m['generic_type']:
            status = 'no_registered_generic_instance'
        else:
            status = 'no_registered_pointer_unresolved'
        coverage.append(dict(method_id=m['id'], signature=m['signature'], status=status,
                             case_assembly=m['assembly'] in case_assemblies, has_body=m['has_body']))
    linked_names = {e['cpp_name'] for e in edges}
    linked_names.update(f['symbol_name'] for e in edges for fs in e['targets'].values() for f in fs)
    generated = []
    wrappers = {e['cpp_name'] for e in edges if e['role'] == 'generic_wrapper'}
    all_names = set(source_by_name) | {n for ns in native.values() for n in ns}
    for name in sorted(all_names):
        generated.append(dict(name=name, kind='generic_wrapper' if name in wrappers else kind(name), linked=name in linked_names,
                              sources=source_by_name.get(name, []), targets=addresses(name)))
    targets = list(functions)
    raw_native = {t: {f['name']: f for f in fs if f['defined']} for t, fs in functions.items()}
    differences = []
    for t, other in [(targets[0], targets[1]), (targets[1], targets[0])]:
        for name in sorted(set(raw_native[t])-set(raw_native[other])):
            f = raw_native[t][name]
            readable = f['demangled_name']
            if f['cpp_name']:
                reason = 'generated_cpp_emission_difference'
            elif 'libunwind' in readable or name.startswith('__CortexA53'):
                reason = 'platform_unwind_or_linker_stub'
            elif 'std::__va_list' in readable or '__va_list_tag' in readable or 'long double' in readable or '__float128' in readable:
                reason = 'platform_abi_type'
            elif 'std::__ndk1::' in readable or 'google::' in readable or 'itanium_demangle::' in readable:
                reason = 'native_template_emission_difference'
            else:
                reason = 'native_runtime_difference_unresolved'
            differences.append(dict(target=t, name=name, demangled_name=readable, reason=reason,
                                    cpp_name=f['cpp_name'], cause_proven=False))
    checks = dict(cases=len(views), cases_unique=True, independent_il_methods=len(independent),
                  independent_il_case_ids=[v['method']['id'] for v in views if v['method']['id'] in independent],
                  case_assembly_coverage=dict(Counter(r['status'] for r in coverage if r['case_assembly'])),
                  all_method_coverage=dict(Counter(r['status'] for r in coverage)),
                  duplicate_addresses={t: dict(symbols=sum(f['duplicate_address'] for f in fs), groups=len({(f['section_index'], f['address']) for f in fs if f['duplicate_address']})) for t, fs in functions.items()},
                  generated_kinds=dict(Counter(r['kind'] for r in generated if r['sources'])),
                  target_difference_counts=dict(Counter(r['target'] for r in differences)),
                  target_difference_categories={t: dict(Counter(r['reason'] for r in differences if r['target'] == t)) for t in targets},
                  inline_debug_records='not_extracted')
    # 校验整份输入清单，路径必须留在输入目录内。
    inputs = []
    for item in json.loads((root/'manifest.json').read_text(encoding='utf-8-sig')):
        path = (root/item['path']).resolve()
        require(path.is_relative_to(root), '输入清单路径越界')
        require(path.stat().st_size == item['bytes'] and digest(path) == item['sha256'], f'产物校验失败：{item["path"]}')
        inputs.append(item)
    required_inputs = list(managed.glob('*.dll')) + list(cpp.glob('*.cpp')) + list(cpp.glob('*_CodeGen.c')) + list(cpp.glob('Il2CppGeneric*.c'))
    required_inputs += [root/'artifacts/il2cppOutput/data/Metadata/global-metadata.dat']
    required_inputs += list((root/'artifacts/il2cppOutput/build').glob('*/libil2cpp.sym.so'))
    recorded = {r['path'] for r in inputs}
    require(all(str(p.relative_to(root)) in recorded for p in required_inputs), '抽取输入未完整包含在产物清单中')
    output.mkdir(parents=True, exist_ok=True)
    tables = {'generic-instances.json': instances, 'unmatched-metadata.json': missing_metadata, 'methods.json': methods, 'mappings.json': edges, 'cases.json': views,
              'generated.json': generated, 'coverage.json': coverage, 'target-differences.json': differences}
    tables.update({f'functions.{t}.json': rows for t, rows in functions.items()})
    for name, rows in tables.items():
        write(output/name, rows)
    write(output/'checks.json', checks)
    source_files = [Path(__file__), Path(__file__).parent/'Managed/Program.cs', Path(__file__).parent/'Managed/Managed.csproj', Path(__file__).parent/'verify.py']
    write(output/'manifest.json', dict(format_version=VERSION, tool_version=VERSION,
          tool_sources={p.name: digest(p) for p in source_files},
          managed_reader_sha256=digest(args.managed_reader), cecil_sha256=digest(args.managed_reader.parent/'Mono.Cecil.dll'),
          dotnet_version=subprocess.check_output([args.dotnet, '--version'], text=True).strip(),
          cxxfilt_version=subprocess.check_output([args.cxxfilt, '--version'], text=True).splitlines()[0], input_manifest_sha256=digest(root/'manifest.json'),
          cases_sha256=digest(args.cases), source_cases_sha256=digest(snapshot_cases), inputs=sorted(inputs, key=lambda r: r['path']),
          counts={k: len(v) for k, v in tables.items()},
          outputs={p.name: digest(p) for p in sorted(output.glob('*.json'))}))
    print(json.dumps(checks, ensure_ascii=False, sort_keys=True))


if __name__ == '__main__':
    main()
