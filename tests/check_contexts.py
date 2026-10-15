"""使用真实 ctree 验证跨泛型上下文绑定；这些检查不替代被调用方法的执行验收。"""
import copy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from runtime_context import Runtime, ContextReader
from ctree_flow import Flow


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


runtime = Runtime(read(sys.argv[1]))
exports, layouts_dir = Path(sys.argv[2]), Path(sys.argv[3])
layouts = read(layouts_dir / 'runtime-layouts.json')
method_layouts = read(layouts_dir / 'method-layouts.json')
layout = method_layouts['MethodInfo_88E2650']
setup = read(exports / '585e200.json')['structured']
reader = ContextReader(runtime, setup, layouts, layout)
call, = [n for n in reader.nodes.values() if n['op'] == 'call' and
         reader.nodes[n['x']].get('object') == '0x88e2650']
context = reader.method(call['arguments'][-1])
assert context and runtime.owns(0x88e2650, context)
assert runtime.data['typeDefinitions'][context['typeArguments'][0]['definition']]['name'] == 'Sekai.Mysekai.GridAreaCell'
assert not runtime.owns(0x88e1e1c, context)
wrong_type = copy.deepcopy(context)
wrong_type['typeArguments'][0] = runtime.shape(next(x['shape'] for x in runtime.data['runtimeTypes'] if x['kind'] == 8 and not x['byRef']))
assert not runtime.owns(0x88e2650, wrong_type)
wrong_arity = dict(context, typeArguments=[])
assert not runtime.owns(0x88e2650, wrong_arity)
truncated = copy.deepcopy(setup)
next(n for n in truncated['nodes'] if n['id'] == call['arguments'][-1])['nativeType']['bytes'] = 4
assert ContextReader(runtime, truncated, layouts, layout).method(call['arguments'][-1]) is None

# 保留实际地址和类型，改掉槽位偏移后必须拒绝原目标。
wrong = copy.deepcopy(setup)
offset = next(n for n in wrong['nodes'] if n['op'] == 'num' and n.get('ea') == '0x585e464' and n.get('number') == '112')
offset['number'] = '120'
other = ContextReader(runtime, wrong, layouts, layout).method(call['arguments'][-1])
assert other and not runtime.owns(0x88e2650, other)

source, = [s for s in runtime.data['slots'] if s['displayName'].endswith('APICaller<EmptyRequest, SuiteUser>.Call()')]
caller = read(exports / '9fa8a80.json')['structured']
reader = ContextReader(runtime, caller, layouts, layout, runtime.slot(source['address']))
call, = [n for n in reader.nodes.values() if n['op'] == 'call' and
         reader.nodes[n['x']].get('object') == '0x6eb36e4']
context = reader.method(call['arguments'][-1])
assert context and runtime.owns(0x6eb36e4, context)
assert context['typeArguments'] == []
assert [runtime.data['typeDefinitions'][a['definition']]['name'] for a in context['methodArguments']] == ['Sekai.EmptyRequest', 'Sekai.SuiteUser']
assert ContextReader(runtime, caller, layouts, layout).method(call['arguments'][-1]) is None

# 显示名称不参与解析。
renamed = copy.deepcopy(caller)
for node in renamed['nodes']:
    if 'symbol' in node:
        node['symbol'] = 'unrelated'
assert ContextReader(runtime, renamed, layouts, layout, runtime.slot(source['address'])).method(call['arguments'][-1]) == context

# 单次赋值也可能被跳转绕开；支配分析必须检查整张图。
nodes = [
    {'id': 0, 'op': 'block', 'items': [1, 2, 5]},
    {'id': 1, 'op': 'goto', 'target': 9},
    {'id': 2, 'op': 'expr', 'expression': 3},
    {'id': 3, 'op': 'asg', 'x': 4, 'y': 8},
    {'id': 4, 'op': 'var', 'variable': 0},
    {'id': 5, 'op': 'return', 'expression': 6, 'label': 9},
    {'id': 6, 'op': 'var', 'variable': 0},
    {'id': 8, 'op': 'num', 'number': '1'}]
tree = {'root': 0, 'nodes': nodes}
assert not Flow(tree).dominates(3, 6)
nodes[0]['items'] = [2, 5]
assert Flow(tree).dominates(3, 6)
nodes[0]['items'] = [5, 2]
assert not Flow(tree).dominates(3, 6)
print('PASS: 15 context/ownership/control-flow checks; native ABI and method bodies still require recovery validation')
