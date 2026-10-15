"""按真实地址和 MethodInfo 建立调用证据；无法解析的间接调用保留为未解决。"""
import argparse
import json
from collections import defaultdict
from pathlib import Path


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def write(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2), encoding='utf-8')


def index(script):
    methods = defaultdict(list)
    for item in script['ScriptMethod']:
        methods[item['Address']].append(item)
    globals_ = {x['Address']: dict(x, kind=kind) for kind in
                ('ScriptMetadataMethod', 'ScriptMetadata', 'ScriptString') for x in script[kind]}
    return methods, globals_


def references(node, nodes):
    if node['op'] == 'obj':
        yield int(node['object'], 0)
    for role in ('x', 'y', 'z'):
        if role in node:
            yield from references(nodes[node[role]], nodes)
    for child in node.get('arguments', []):
        yield from references(nodes[child], nodes)


def runtime_bindings(runtime):
    owners = defaultdict(set)
    for d in runtime['definitions']:
        if d['address']:
            owners[d['address']].add(d['index'])
    for s in runtime['specs']:
        if s['address']:
            owners[s['address']].add(s['definition'])
    return owners, {s['address']: s for s in runtime['slots']}


def bind_call(address, infos, runtime, owners, slots):
    if len(infos) != 1:
        return {'status': 'unresolved', 'reason': 'no-unique-method-info'}
    slot = slots.get(infos[0]['Address'])
    if not slot or not slot['valid']:
        return {'status': 'unresolved', 'reason': 'invalid-metadata-slot'}
    if slot['definition'] not in owners.get(address, set()):
        return {'status': 'unresolved', 'reason': 'definition-does-not-own-target'}
    definition = runtime['definitions'][slot['definition']]
    spec = runtime['specs'][slot['index']] if slot['kind'] == 6 else None
    return {'status': 'identity-bound', 'assembly': definition['assembly'], 'token': definition['token'],
            'definition': definition['index'], 'slot': slot['address'], 'rawToken': slot['raw'],
            'typeArguments': spec['typeArguments'] if spec else [],
            'methodArguments': spec['methodArguments'] if spec else [], 'abi': 'unchecked'}


def call_graph(exports, methods, globals_, expected_hash, runtime=None):
    owners, slots = runtime_bindings(runtime) if runtime else ({}, {})
    result = []
    for path in sorted(Path(exports).glob('*.json')):
        data = read(path)
        if 'structured' not in data:
            continue
        if data['input_sha256'].lower() != expected_hash.lower():
            raise ValueError(f'输入版本不符: {path}')
        nodes = {n['id']: n for n in data['structured']['nodes']}
        calls = []
        for n in nodes.values():
            if n['op'] != 'call':
                continue
            target = nodes[n['x']]
            while target['op'] == 'cast':
                target = nodes[target['x']]
            address = int(target['object'], 0) if target['op'] == 'obj' else None
            refs = sorted(set(references(n, nodes)))
            contexts = [globals_[a] for a in refs if a in globals_ and
                        globals_[a]['kind'] == 'ScriptMetadataMethod']
            # 委托构造等实参还可包含其他方法，只有末尾 MethodInfo 才是本次调用上下文。
            last_refs = set(references(nodes[n['arguments'][-1]], nodes)) if n['arguments'] else set()
            info = [globals_[a] for a in sorted(last_refs) if methods.get(address) and a in globals_ and
                    globals_[a]['kind'] == 'ScriptMetadataMethod']
            bindings = [m for m in info if m['MethodAddress'] != 0 and m['MethodAddress'] == address]
            calls.append({'node': n['id'], 'ea': n['ea'], 'target': hex(address) if address else None,
                'nativeSymbol': target.get('symbol'), 'nativeHelper': target.get('helper'),
                'kind': 'direct' if address is not None else 'indirect',
                'candidates': methods.get(address, []), 'methodInfo': info,
                'binding': bind_call(address, info, runtime, owners, slots) if runtime else
                    {'status': 'verified-address' if len(bindings) == 1 else 'unresolved'},
                'referencedMethods': contexts, 'argumentNodes': n['arguments']})
        globals_used = sorted({int(n['object'], 0) for n in nodes.values() if n['op'] == 'obj'} & globals_.keys())
        result.append({'address': data['address'], 'names': [m['Name'] for m in methods[int(data['address'], 0)]],
            'warnings': data['warnings'], 'calls': calls,
            'globals': [globals_[a] for a in globals_used]})
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=('plan', 'report'))
    parser.add_argument('script')
    parser.add_argument('case')
    parser.add_argument('output')
    parser.add_argument('--exports')
    parser.add_argument('--runtime-index')
    args = parser.parse_args()
    spec, script = read(args.case), read(args.script)
    methods, globals_ = index(script)
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    roots = [m for m in script['ScriptMethod'] if any(m['Name'].split('$$')[0] == name or
             m['Name'].split('$$')[0].startswith(name + '.') for name in spec['types'])]
    write(output/'roots.json', roots)
    if args.action == 'plan':
        requests = [{'action': 'decompile', 'address': hex(a), 'binary_sha256': spec['binarySha256']}
                    for a in sorted({m['Address'] for m in roots})]
        (output/'requests.jsonl').write_text('\n'.join(json.dumps(x) for x in requests) + '\n', encoding='utf-8')
        print(f'roots: {len(roots)} methods, {len(requests)} native bodies')
        return
    runtime = read(args.runtime_index) if args.runtime_index else None
    if runtime and runtime['binarySha256'] != spec['binarySha256']:
        raise ValueError('登记表的输入哈希不匹配')
    graph = call_graph(args.exports, methods, globals_, spec['binarySha256'], runtime)
    write(output/'dependencies.json', graph)
    known = {int(x['address'], 0) for x in graph}
    missing = sorted({int(c['target'], 0) for m in graph for c in m['calls'] if c['target']} - known)
    write(output/'missing.json', [{'address': hex(a), 'candidates': methods.get(a, [])} for a in missing])
    print(f'bodies: {len(graph)}, calls: {sum(len(m["calls"]) for m in graph)}, unexported targets: {len(missing)}')


if __name__ == '__main__':
    main()
