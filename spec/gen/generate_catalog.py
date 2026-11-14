#!/usr/bin/env python3
"""从头文件选取声明，交给 libclang 计算原型及 Itanium 修饰名。"""
import argparse
import importlib.metadata
import json
import re
import tempfile
from pathlib import Path
from clang import cindex as ci
from generate import PRELUDE, TARGETS, sha, dump


def declaration(root, entry):
    path = root / entry['header']
    text = path.read_text()
    # 当前输入限于单行、非模板的自由函数和静态成员；不解析函数体。
    pattern = r'^([ \t]*(?:[A-Za-z_][A-Za-z_0-9:]*[ \t*&]+)+' + re.escape(entry['name'].split('::')[-1]) + r'\s*\([^\n;{}]*\))\s*(?:;|\{|$)'
    candidates = [m for m in re.finditer(pattern, text, re.M)
                  if m[1].split(entry['name'].split('::')[-1], 1)[0].strip() not in ('', 'return')]
    if 'parameters' in entry:
        candidates = [m for m in candidates if re.sub(r'\s+', ' ', m[1].split('(', 1)[1][:-1]).strip() == entry['parameters']]
    # 条件编译中有声明和空的 inline 实现时，两者的类型必须相同。
    normalized = {re.sub(r'\b(inline|IL2CPP_FORCE_INLINE|IL2CPP_NO_INLINE)\b', '', m[1]).strip() for m in candidates}
    if len(normalized) != 1:
        raise ValueError(f"{entry['name']}：声明匹配 {len(normalized)} 项，要求明确选择重载")
    match = candidates[0]
    return match[1].strip(), {'file': entry['header'], 'line': text.count('\n', 0, match.start()) + 1}


def shape(t):
    c = t.get_canonical()
    if c.kind == ci.TypeKind.VOID:
        return {'kind': 'void'}
    if c.kind in (ci.TypeKind.POINTER, ci.TypeKind.LVALUEREFERENCE, ci.TypeKind.RVALUEREFERENCE):
        return {'kind': 'pointer', 'bits': 64}
    if c.kind in (ci.TypeKind.BOOL, ci.TypeKind.CHAR_S, ci.TypeKind.CHAR_U, ci.TypeKind.SCHAR, ci.TypeKind.UCHAR,
                  ci.TypeKind.SHORT, ci.TypeKind.USHORT, ci.TypeKind.INT, ci.TypeKind.UINT, ci.TypeKind.LONG,
                  ci.TypeKind.ULONG, ci.TypeKind.LONGLONG, ci.TypeKind.ULONGLONG):
        return {'kind': 'integer', 'bits': c.get_size() * 8}
    if c.kind in (ci.TypeKind.FLOAT, ci.TypeKind.DOUBLE):
        return {'kind': 'float', 'bits': c.get_size() * 8}
    return {'kind': 'unsupported', 'reason': '尚未支持的 C 类型：' + t.spelling}


def generate(root, unity, target, mapping):
    if importlib.metadata.version('libclang') != '18.1.1':
        raise ValueError('需要 libclang==18.1.1')
    entries = json.loads(mapping.read_text())
    if unity != entries['unity_version']:
        raise ValueError('手写映射的 Unity 版本不匹配')
    selected = [(e, *declaration(root, e)) for e in entries['functions']]
    with tempfile.TemporaryDirectory(suffix='.local.catalog') as tmp:
        p = Path(tmp)
        (p / 'primitives.h').write_text(PRELUDE.replace('typedef __WCHAR_TYPE__ wchar_t;', '').replace('#define NULL ((void*)0)', '#define NULL 0'))
        for name in ('stdint.h', 'stddef.h', 'string.h'):
            (p / name).write_text('#include "primitives.h"\n')
        metadata = (root / 'codegen/il2cpp-codegen-metadata.h').read_text()
        aliases = re.findall(r'^typedef (?:struct )?\w+ \w+;', metadata, re.M)
        names = sorted({line.split()[-2] for line in aliases})
        slot = re.findall(r'^typedef \w+ Il2CppMethodSlot;', (root / 'il2cpp-config.h').read_text(), re.M)
        if len(slot) != 1:
            raise ValueError('Il2CppMethodSlot 必须有唯一的真实定义')
        body = '#include "primitives.h"\n' + '\n'.join('struct ' + n + ';' for n in names)
        body += '\nstruct Exception_t; struct Type_t; struct VirtualInvokeData;\n' + '\n'.join(aliases + slot)
        body += '\n#define IL2CPP_FORCE_INLINE inline\n#define IL2CPP_NO_INLINE\n'
        array_size = re.findall(r'^typedef \w+ il2cpp_array_size_t;', (root / 'il2cpp-api-types.h').read_text(), re.M)
        if len(array_size) != 1:
            raise ValueError('il2cpp_array_size_t 必须有唯一的真实定义')
        body += array_size[0] + '\n'
        # 保留声明中的宏标志；不编译不完整头文件依赖中的函数体。
        body += '\n#undef NORETURN\n#define NORETURN __attribute__((noreturn))\n#undef REAL_NORETURN\n#define REAL_NORETURN __attribute__((noreturn))\n'
        for e, decl, _ in selected:
            parts = e['name'].split('::')
            if len(parts) == 1:
                body += decl + ';\n'
            else:
                # 同一类在独立 probe 中解析，避免重定义；只有明确的 static 成员可进入。
                if not re.search(r'\bstatic\b', decl):
                    raise ValueError('非静态成员不能忽略 this：' + e['name'])
                continue
        probe = p / 'probe.cpp'
        probe.write_text(body)
        args = ['-x', 'c++', '-std=c++17', '-target', TARGETS[target], '-nostdinc', '-I' + tmp, '-I' + str(root)]
        def parse(source):
            tu = ci.Index.create().parse(str(probe), args=args, unsaved_files=[(str(probe), source)])
            errors = [str(d) for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
            if errors:
                raise ValueError('\n'.join(errors))
            return tu
        tu = parse(body)
        functions = []
        for e, decl, location in selected:
            parts = e['name'].split('::')
            current = tu
            if len(parts) > 1:
                member = ''.join('namespace ' + n + ' {' for n in parts[:-2]) + 'class ' + parts[-2] + ' { public: ' + decl + '; };' + '}' * (len(parts) - 2)
                current = parse(body + member)
            matches = [c for c in current.cursor.walk_preorder() if c.kind in (ci.CursorKind.FUNCTION_DECL, ci.CursorKind.CXX_METHOD)
                       and c.spelling == parts[-1] and c.location.file and c.location.file.name == str(probe)]
            # 映射中的原始声明确定重载，clang 的规范类型与形参数由声明生成。
            if len(matches) > 1:
                single = parse(body[:body.index('\n#undef NORETURN')] + '\n#define NORETURN __attribute__((noreturn))\n#define REAL_NORETURN __attribute__((noreturn))\n' + decl + ';')
                matches = [c for c in single.cursor.get_children() if c.kind == ci.CursorKind.FUNCTION_DECL and c.spelling == parts[-1]]
            if len(matches) != 1:
                raise ValueError('无法唯一解析：' + e['name'])
            c = matches[0]
            parameters = list(c.get_arguments())
            types = [shape(a.type) for a in parameters]
            ret = shape(c.result_type)
            problems = [t['reason'] for t in [*types, ret] if t['kind'] == 'unsupported']
            functions.append(dict(name=e['name'], mangled_name=c.mangled_name, declaration=decl, declaration_source=location,
                declared_noreturn=bool(re.search(r'\b(?:NORETURN|REAL_NORETURN)\b', decl)),
                prototype=dict(parameters=types, result=ret, variadic=c.type.is_function_variadic()),
                parameter_names=[a.spelling for a in parameters], parameter_types=[a.type.spelling for a in parameters],
                result_type=c.result_type.spelling, unsupported=problems,
                operation=e['operation'], arguments=e['arguments'], result=e['result'], basis=e['basis'],
                recognition=dict(symbol=True, export=None, call_graph=None, reference_shape=None, **e.get('recognition', {}))))
        sources = sorted({e['header'] for e in entries['functions']} | {'codegen/il2cpp-codegen-metadata.h', 'il2cpp-object-internals.h', 'il2cpp-class-internals.h', 'il2cpp-config.h', 'il2cpp-api-types.h'})
        return dict(schema_version=1, unity_version=unity, target=dict(triple=TARGETS[target], data_model='LP64'),
                    generator_sha256=sha(Path(__file__)), shared_generator_sha256=sha(Path(__file__).with_name('generate.py')), mapping_sha256=sha(mapping), compiler='libclang 18.1.1',
                    source={name: sha(root / name) for name in sources},
                    adaptations=['仅解析选定单行声明，保留真实类型别名；静态成员保留命名空间与类作用域',
                                 '只接受指针、引用与标量；类前置声明，别名来自 codegen-metadata，槽类型来自 config；不编译函数体；NORETURN 按 Android 展开'],
                    functions=sorted(functions, key=lambda f: f['mangled_name']))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--runtime-headers', required=True, type=Path)
    parser.add_argument('--unity', required=True)
    parser.add_argument('--target', choices=['android-arm64', 'android-x64'], required=True)
    parser.add_argument('--mapping', type=Path, default=Path(__file__).with_name('runtime-functions.json'))
    parser.add_argument('--output', required=True, type=Path)
    a = parser.parse_args()
    dump(a.output, generate(a.runtime_headers.resolve(), a.unity, a.target, a.mapping))
