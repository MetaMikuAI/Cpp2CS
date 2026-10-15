"""从 case 根方法展开带泛型实例的调用证据，保留未导出和未绑定边。"""
import argparse
from collections import defaultdict, deque
import json
from pathlib import Path
from runtime_context import Runtime, ContextReader


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def key(address, context):
    return json.dumps([address, context], sort_keys=True, separators=(',', ':'))


def plan(data, roots, exports, layouts, method_layout):
    runtime = Runtime(data)
    definitions = defaultdict(list)
    for definition in data['definitions']:
        if definition['address']:
            definitions[definition['address']].append(definition['index'])
    trees = {}
    for directory in exports:
        for path in Path(directory).glob('*.json'):
            result = read(path)
            if not isinstance(result, dict) or 'structured' not in result:
                continue
            if result['input_sha256'].lower() != data['binarySha256'].lower():
                raise ValueError('ctree 与登记表输入版本不符: ' + str(path))
            address = int(result['address'], 0)
            if address in trees:
                raise ValueError('同一地址有多个 ctree 导出，需明确选择: ' + hex(address))
            trees[address] = result
    pending = deque()
    for root in roots:
        address = root['Address']
        if len(definitions[address]) != 1:
            raise ValueError('根方法身份不唯一: ' + hex(address))
        pending.append((address, {'definition': definitions[address][0], 'typeArguments': [], 'methodArguments': []}))
    visited = set()
    methods = []
    while pending:
        address, context = pending.popleft()
        identity = key(address, context)
        if identity in visited:
            continue
        visited.add(identity)
        definition = data['definitions'][context['definition']]
        method = {'address': hex(address), 'assembly': definition['assembly'], 'token': definition['token'],
                  'name': definition['owner'] + '.' + definition['name'], 'context': context,
                  'body': 'exported' if address in trees else 'missing', 'abi': 'unchecked', 'calls': []}
        methods.append(method)
        if address not in trees:
            continue
        tree = trees[address]
        method['warnings'] = tree['warnings']
        reader = ContextReader(runtime, tree['structured'], layouts, method_layout, context)
        for node in reader.nodes.values():
            if node['op'] != 'call':
                continue
            target = reader.nodes[node['x']]
            while target['op'] == 'cast':
                target = reader.nodes[target['x']]
            target_address = int(target['object'], 0) if target['op'] == 'obj' else None
            edge = {'node': node['id'], 'ea': node['ea'], 'target': hex(target_address) if target_address else None,
                    'status': 'unresolved', 'reason': 'indirect-call' if target_address is None else 'method-info-unresolved'}
            method['calls'].append(edge)
            if target_address is None or not node['arguments']:
                continue
            info_node = reader.nodes[node['arguments'][-1]]
            bound = reader.method(info_node['id'])
            while info_node['op'] == 'cast':
                info_node = reader.nodes[info_node['x']]
            if bound is None and info_node['op'] == 'num' and info_node['number'] == '0' and len(definitions[target_address]) == 1:
                bound = {'definition': definitions[target_address][0], 'typeArguments': [], 'methodArguments': []}
            if bound is not None and runtime.owns(target_address, bound):
                edge.update(status='identity-bound', context=bound)
                del edge['reason']
                pending.append((target_address, bound))
            elif bound:
                edge['reason'] = 'target-or-sharing-mismatch'
            elif not definitions[target_address] and target_address not in runtime.targets:
                edge['reason'] = 'native-runtime-or-external'
    return {'binarySha256': data['binarySha256'], 'metadataSha256': data['metadataSha256'],
            'stage': 'dependency-evidence', 'complete': False,
            'coverage': {'directCalls': True, 'delegateTargets': False, 'virtualDispatch': False,
                         'coroutineDispatch': False, 'staticInitialization': False, 'exceptionCleanup': False},
            'methods': methods}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('runtime')
    parser.add_argument('roots')
    parser.add_argument('layouts')
    parser.add_argument('method_layouts')
    parser.add_argument('output')
    parser.add_argument('--exports', nargs='+', required=True)
    args = parser.parse_args()
    method_layouts = read(args.method_layouts)
    candidates = [layout for layout in method_layouts.values() if any(f['name'] == 'rgctx_data' for f in layout['fields'])]
    offsets = {next(f['offset_bits'] for f in layout['fields'] if f['name'] == 'rgctx_data') for layout in candidates}
    if len(offsets) != 1:
        raise ValueError('MethodInfo 泛型上下文布局不一致')
    result = plan(read(args.runtime), read(args.roots), args.exports, read(args.layouts), candidates[0])
    Path(args.output).write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    methods = result['methods']
    calls = [c for m in methods for c in m['calls']]
    print(f'{len(methods)} method instances, {sum(m["body"] == "missing" for m in methods)} missing bodies, '
          f'{sum(c["status"] == "identity-bound" for c in calls)}/{len(calls)} calls identity-bound; ABI/recovery not complete')


if __name__ == '__main__':
    main()
