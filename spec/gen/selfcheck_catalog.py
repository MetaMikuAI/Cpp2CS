#!/usr/bin/env python3
"""检查声明选择、C 类型映射与不支持类型的显式失败。"""
import tempfile
from pathlib import Path
from clang import cindex as ci
from generate_catalog import declaration, shape

with tempfile.TemporaryDirectory(suffix='.local.catalog-check') as tmp:
    root = Path(tmp)
    header = root / 'test.h'
    header.write_text('void F(int x);\nvoid F(void* p);\ninline void G(int x) { F(x); }\n')
    entry = dict(header='test.h', name='F')
    try:
        declaration(root, entry)
        raise AssertionError('重载必须明确选择')
    except ValueError as e:
        assert '要求明确选择重载' in str(e)
    selected, source = declaration(root, dict(entry, parameters='int x'))
    assert selected == 'void F(int x)' and source == dict(file='test.h', line=1)
    selected, _ = declaration(root, dict(header='test.h', name='G'))
    assert selected == 'inline void G(int x)'
    probe = root / 'probe.cpp'
    probe.write_text('struct S; namespace n { class C { public: static bool F(const S& s, int x); }; }\nstruct S { int x; }; S G(S x);')
    tu = ci.Index.create().parse(str(probe), args=['-x', 'c++', '-target', 'aarch64-linux-android', '-nostdinc'])
    assert not [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
    method = next(c for c in tu.cursor.walk_preorder() if c.kind == ci.CursorKind.CXX_METHOD)
    assert method.mangled_name == '_ZN1n1C1FERK1Si'
    assert shape(method.result_type) == dict(kind='integer', bits=8)
    assert [shape(a.type) for a in method.get_arguments()] == [dict(kind='pointer', bits=64), dict(kind='integer', bits=32)]
    function = next(c for c in tu.cursor.get_children() if c.spelling == 'G')
    assert shape(function.result_type)['kind'] == 'unsupported'
print('运行时目录生成器：声明重载、作用域、引用、布尔与不支持聚合检查通过')
