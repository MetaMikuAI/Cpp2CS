#!/usr/bin/env python3
"""通过 libclang 的目标布局 API 提取运行时数据。"""
import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path
import re
import tempfile
from clang import cindex as ci

VERSION = '1'
TARGETS = {'android-arm64': 'aarch64-linux-android', 'android-x64': 'x86_64-linux-android', 'windows-x64': 'x86_64-pc-windows-msvc'}
PRELUDE = '''
#pragma once
typedef __INT8_TYPE__ int8_t;
typedef __UINT8_TYPE__ uint8_t;
typedef __INT16_TYPE__ int16_t;
typedef __UINT16_TYPE__ uint16_t;
typedef __INT32_TYPE__ int32_t;
typedef __UINT32_TYPE__ uint32_t;
typedef __INT64_TYPE__ int64_t;
typedef __UINT64_TYPE__ uint64_t;
typedef __INTPTR_TYPE__ intptr_t;
typedef __UINTPTR_TYPE__ uintptr_t;
typedef __SIZE_TYPE__ size_t;
typedef __PTRDIFF_TYPE__ ptrdiff_t;
typedef __WCHAR_TYPE__ wchar_t;
#define offsetof(T, f) __builtin_offsetof(T, f)
#define INT32_MIN (-__INT32_MAX__ - 1)
#define INT64_MIN (-__INT64_MAX__ - 1)
#define INT32_MAX __INT32_MAX__
#define UINT32_MAX __UINT32_MAX__
#define INT64_MAX __INT64_MAX__
#define UINT64_MAX __UINT64_MAX__
#define INTPTR_MAX __INTPTR_MAX__
#define UINTPTR_MAX __UINTPTR_MAX__
#define NULL ((void*)0)
'''
PLATFORM = '''
#pragma once
#define IL2CPP_TARGET_ANDROID 1
#define IL2CPP_TARGET_POSIX 1
#define IL2CPP_SIZEOF_VOID_P __SIZEOF_POINTER__
#define IL2CPP_TARGET_ARM64 __aarch64__
#define IL2CPP_TARGET_X64 __x86_64__
#define IL2CPP_COMPILER_MSVC 0
#define STDCALL
#define CDECL
#define DEFAULT_CALL
#define IL2CPP_EXPORT
#define IL2CPP_IMPORT
#define IL2CPP_API
#define IL2CPP_TARGET_LINUX 0
#define IL2CPP_DEBUG 0
typedef uint16_t Il2CppChar;
typedef char Il2CppNativeChar;
typedef uintptr_t il2cpp_array_size_t;
'''
SINGLE = '''
#define bool uint8_t
typedef uint16_t Il2CppChar;
typedef char Il2CppNativeChar;
typedef uintptr_t il2cpp_array_size_t;
'''

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def dump(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + '\n')

def generate(source, unity, target, real=False, restore_arrays=True):
    if importlib.metadata.version("libclang") != "18.1.1":
        raise ValueError("需要 libclang==18.1.1")
    source = source.resolve()
    with tempfile.TemporaryDirectory(suffix='.local.layout') as tmp:
        root = Path(tmp)
        (root / 'primitives.h').write_text(PRELUDE)
        for name in ('stdint.h', 'stddef.h', 'string.h'):
            (root / name).write_text('#include "primitives.h"\n')
        if real:
            if target == 'windows-x64':
                raise ValueError('真实头文件的补充平台配置目前只支持 Android')
            platform = root / 'os/c-api'
            platform.mkdir(parents=True)
            (platform / 'il2cpp-config-platforms.h').write_text(PLATFORM)
            (platform / 'il2cpp-config-api-platforms.h').write_text('#pragma once\n')
            body = '#include "il2cpp-object-internals.h"\n#include "il2cpp-tabledefs.h"\n'
            includes = ['-I' + str(source)]
        else:
            body = SINGLE + '\n#include "' + source.as_posix() + '"\n'
            includes = []
        probe = root / 'probe.c'
        probe.write_text('#include "primitives.h"\n' + body + '\nstruct LayoutTargetProbe { char c; short s; int i; long l; long long ll; void *p; float f; double d; long double ld; };\n')
        transformations = []
        unsaved = []
        if not real and restore_arrays:
            original = source.read_text()
            pattern = r'(VirtualInvokeData\s+vtable|void\*\s+vector|Il2CppChar\s+chars)\[32\]'
            transformed, count = re.subn(pattern, r'\1[0]', original)
            transformations = [{'operation': 'restore_zero_length_arrays', 'fields': ['vtable', 'vector', 'chars'], 'occurrences': count, 'basis': 'Il2CppVersions headers/extract.py replaces [0] with [32] for IDA'}]
            unsaved = [(str(source), transformed)]
        args = ['-x', 'c', '-std=gnu11', '-target', TARGETS[target], '-nostdinc', '-I' + tmp] + includes
        tu = ci.Index.create().parse(str(probe), args=args, unsaved_files=unsaved, options=ci.TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD)
        errors = [str(d) for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
        if errors:
            raise RuntimeError('\n'.join(errors))
        def owned(c):
            if not c.location.file:
                return False
            p = Path(c.location.file.name)
            return p.is_relative_to(source) if real else p == source
        records, constants = {}, {}
        def fields(c, prefix='', base=0):
            result = []
            children = list(c.get_children())
            named_types = {f.type.get_declaration().get_usr() for f in children if f.kind == ci.CursorKind.FIELD_DECL}
            for f in children:
                if f.kind == ci.CursorKind.FIELD_DECL:
                    off = f.get_field_offsetof()
                    if off < 0 or f.type.get_size() < 0:
                        raise ValueError(f'不可计算字段: {c.spelling}.{f.spelling}')
                    item = {'name': prefix + f.spelling, 'offset_bits': base + off, 'size': f.type.get_size(), 'type': re.sub(r'\(unnamed (?:union|struct) at .*?\)', '(anonymous)', f.type.spelling)}
                    decl = f.type.get_declaration()
                    if decl.kind in (ci.CursorKind.STRUCT_DECL, ci.CursorKind.UNION_DECL) and decl.is_anonymous():
                        item['members'] = fields(decl)
                    if f.is_bitfield():
                        item['bit_width'] = f.get_bitfield_width()
                    result.append(item)
                elif f.kind in (ci.CursorKind.STRUCT_DECL, ci.CursorKind.UNION_DECL) and f.is_anonymous() and f.get_usr() not in named_types:
                    nested = fields(f)
                    # 匿名成员通过父类型查询，偏移由编译器返回。
                    for item in nested:
                        off = c.type.get_offset(item['name'])
                        if off < 0:
                            raise ValueError('匿名字段不可定位: ' + item['name'])
                        item['offset_bits'] = base + off
                    result.extend(nested)
            return result
        for c in tu.cursor.walk_preorder():
            if not owned(c):
                continue
            if c.kind in (ci.CursorKind.STRUCT_DECL, ci.CursorKind.UNION_DECL) and c.is_definition() and c.spelling and not c.is_anonymous():
                if c.type.get_size() < 0:
                    raise ValueError('不可计算结构: ' + c.spelling)
                records[c.spelling] = {'type': c.type.spelling, 'kind': 'union' if c.kind == ci.CursorKind.UNION_DECL else 'struct', 'size': c.type.get_size(), 'alignment': c.type.get_align(), 'fields': fields(c)}
            elif c.kind == ci.CursorKind.ENUM_CONSTANT_DECL:
                constants[c.spelling] = c.enum_value
        # 整数宏也交给编译器求值；排除函数宏和字符串宏。
        macros = []
        values = []
        for c in tu.cursor.get_children():
            if owned(c) and c.kind == ci.CursorKind.VAR_DECL and c.type.is_const_qualified() and c.type.get_canonical().kind in (ci.TypeKind.INT, ci.TypeKind.UINT, ci.TypeKind.LONG, ci.TypeKind.ULONG, ci.TypeKind.LONGLONG, ci.TypeKind.ULONGLONG):
                values.append(c.spelling)
            if owned(c) and c.kind == ci.CursorKind.MACRO_DEFINITION:
                tokens = list(c.get_tokens())
                if len(tokens) > 1 and re.match(r'^(?:TYPE|METHOD|METHOD_IMPL|FIELD|PARAM|PROPERTY|EVENT)_ATTRIBUTE_|^IL2CPP_(?:GENERIC_PARAMETER_ATTRIBUTE_|TYPE_|TOKEN_)|^THREAD_LOCAL_STATIC_MASK$', c.spelling):
                    macros.append(c.spelling)
        if macros or values:
            probe.write_text(probe.read_text() + '\nenum LayoutConstants {\n' + ',\n'.join('LayoutConstant_' + n + ' = ' + n for n in sorted(set(macros + values))) + '\n};\n')
            mt = ci.Index.create().parse(str(probe), args=args, unsaved_files=unsaved)
            errors = [str(d) for d in mt.diagnostics if d.severity >= ci.Diagnostic.Error]
            if errors:
                raise RuntimeError('\n'.join(errors))
            for c in mt.cursor.walk_preorder():
                if c.kind == ci.CursorKind.ENUM_CONSTANT_DECL and c.spelling.startswith('LayoutConstant_'):
                    constants[c.spelling.removeprefix('LayoutConstant_')] = c.enum_value
        primitive = next(c for c in tu.cursor.get_children() if c.spelling == 'LayoutTargetProbe')
        model = {f.type.spelling: {'size': f.type.get_size(), 'alignment': f.type.get_align()} for f in primitive.get_children()}
        inputs = {Path(i.include.name) for i in tu.get_includes() if Path(i.include.name).is_relative_to(source)} if real else {source}
        sources = {p.relative_to(source).as_posix() if real else p.name: sha(p) for p in sorted(inputs)}
        return {'schema_version': 1, 'generator_version': VERSION, 'generator_sha256': sha(Path(__file__)), 'compiler': 'libclang 18.1.1', 'unity_version': unity, 'target': {'triple': TARGETS[target], 'data_model': 'LLP64' if target == 'windows-x64' else 'LP64', 'alignment': 'clang target default', 'language': 'gnu11', 'primitives': model}, 'source': {'kind': 'runtime-headers' if real else 'Il2CppVersions', 'sha256': sources, 'transformations': transformations, 'platform_adapter': 'Android C declarations; absent os/c-api configuration supplied by generator' if real else 'compiler primitive types and IL2CPP character/array typedefs'}, 'records': records, 'constants': constants}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', required=True, type=Path)
    p.add_argument('--unity', required=True)
    p.add_argument('--target', choices=TARGETS, required=True)
    p.add_argument('--runtime-headers', action='store_true')
    p.add_argument('--output', required=True, type=Path)
    a = p.parse_args()
    dump(a.output, generate(a.source, a.unity, a.target, a.runtime_headers))

if __name__ == '__main__':
    main()
