"""按登记表实例化泛型身份，并解析 ctree 中的 MethodInfo/rgctx 读取。"""
from collections import defaultdict
from ctree_flow import Flow


class Runtime:
    def __init__(self, data):
        if data.get('schema') != 2:
            raise ValueError('登记表 schema 不匹配，需重新导出')
        self.data = data
        self.slots = {s['address']: s for s in data['slots']}
        self.contexts = {(c['assembly'], c['token']): c['entries'] for c in data['contexts']}
        self.targets = defaultdict(list)
        for spec in data['specs']:
            if spec['address']:
                self.targets[spec['address']].append(spec['index'])

    def shape(self, index, context=None):
        source = self.data['shapes'][index]
        kind = source['kind']
        if kind in (19, 30) and context:
            arguments = context['typeArguments' if kind == 19 else 'methodArguments']
            if source['position'] >= len(arguments):
                raise ValueError('泛型参数位置越界')
            result = dict(arguments[source['position']])
            result['byRef'] = bool(result['byRef'] or source['byRef'])
            return result
        return {'kind': kind, 'byRef': bool(source['byRef']), 'definition': source['definition'],
                'position': source['position'], 'rank': source['rank'],
                'element': self.shape(source['element'], context) if source['element'] >= 0 else None,
                'arguments': [self.shape(x, context) for x in source['arguments']]}

    def spec(self, index, context=None):
        spec = self.data['specs'][index]
        return {'definition': spec['definition'],
                'typeArguments': [self.shape(x['shape'], context) for x in spec['typeArguments']],
                'methodArguments': [self.shape(x['shape'], context) for x in spec['methodArguments']]}

    def slot(self, address):
        slot = self.slots.get(address)
        if not slot or not slot['valid']:
            return None
        return self.spec(slot['index']) if slot['kind'] == 6 else {
            'definition': slot['definition'], 'typeArguments': [], 'methodArguments': []}

    def reference(self, shape):
        return shape['kind'] in (14, 18, 20, 28, 29) or (
            shape['kind'] == 21 and not self.data['typeDefinitions'][shape['definition']]['valueType'])

    def sharing(self, left, right):
        if left == right:
            return True
        if left['byRef'] != right['byRef']:
            return False
        return self.reference(left) and self.reference(right)

    def owns(self, address, context):
        if not all(self.closed(shape) for key in ('typeArguments', 'methodArguments') for shape in context[key]):
            return False
        definition = self.data['definitions'][context['definition']]
        owner = self.data['typeDefinitions'][definition['declaringType']]
        if len(context['typeArguments']) != owner['genericArity'] or len(context['methodArguments']) != definition['genericArity']:
            return False
        if not context['typeArguments'] and not context['methodArguments']:
            return definition['address'] == address
        return any(self.spec(i)['definition'] == context['definition'] and
                   all(len(context[key]) == len(self.spec(i)[key]) and
                       all(self.sharing(a, b) for a, b in zip(context[key], self.spec(i)[key]))
                       for key in ('typeArguments', 'methodArguments'))
                   for i in self.targets.get(address, []))

    def closed(self, shape):
        return shape['kind'] not in (19, 30) and all(self.closed(a) for a in shape['arguments']) and \
            (shape['element'] is None or self.closed(shape['element']))

    def entry(self, context, owner_kind, index):
        definition = self.data['definitions'][context['definition']]
        owner = definition if owner_kind == 'method' else self.data['typeDefinitions'][definition['declaringType']]
        entries = self.contexts.get((owner['assembly'], owner['token']), [])
        if not 0 <= index < len(entries):
            return None
        entry = entries[index]
        if entry['kind'] == 3:
            return ('method', self.spec(entry['data'], context))
        if entry['kind'] in (1, 2):
            shape = self.shape(self.data['runtimeTypes'][entry['data']]['shape'], context)
            return ('type' if entry['kind'] == 1 else 'class-type', shape)
        return None


def member(layout, name):
    field, = [f for f in layout['fields'] if f['name'] == name]
    if field['offset_bits'] % 8 or field['size_bits'] != 64:
        raise ValueError('运行时字段不是完整的 64 位指针')
    return field['offset_bits'] // 8


class ContextReader:
    """只接受已证明来源的指针路径；多次写入、地址逃逸和无支配关系的别名保留未知。"""
    def __init__(self, runtime, structured, layouts, method_layout, context=None):
        self.runtime = runtime
        self.nodes = {n['id']: n for n in structured['nodes']}
        self.method_argument = structured['arguments'][-1] if structured['arguments'] else None
        self.context = context
        self.klass = member(layouts['MethodInfo'], 'klass')
        self.method_rgctx = member(method_layout, 'rgctx_data')
        self.class_rgctx = member(layouts['Il2CppClass'], 'rgctx_data')
        self.stride = layouts['Il2CppRGCTXData']['bytes']
        if self.stride != 8:
            raise ValueError('尚未支持的泛型上下文槽位宽度')
        writes = defaultdict(list)
        escaped = set()
        for n in self.nodes.values():
            x = self.nodes.get(n.get('x'))
            if x and x['op'] == 'var':
                if n['op'].startswith('asg') or n['op'] in ('preinc', 'postinc', 'predec', 'postdec'):
                    writes[x['variable']].append(n)
                if n['op'] == 'ref':
                    escaped.add(x['variable'])
        self.aliases = {v: ns[0] for v, ns in writes.items() if len(ns) == 1 and
                        ns[0]['op'] == 'asg' and v not in escaped}
        self.flow = Flow(structured)

    def read(self, base, offset):
        if base is None:
            return None
        kind, payload = base
        if kind == 'offset':
            return self.read(payload[0], payload[1] + offset)
        if kind == 'method':
            if offset == self.klass:
                return ('class', payload)
            if offset == self.method_rgctx:
                return ('context', (payload, 'method'))
        if kind == 'class' and offset == self.class_rgctx:
            return ('context', (payload, 'class'))
        if kind == 'context' and offset >= 0 and offset % self.stride == 0:
            return self.runtime.entry(payload[0], payload[1], offset // self.stride)
        return None

    def value(self, index, seen=frozenset()):
        if index in seen:
            return None
        seen = seen | {index}
        n = self.nodes[index]
        if n['op'] in ('obj', 'ptr', 'memptr', 'idx') and n['nativeType']['bytes'] != 8:
            return None
        if n['op'] == 'obj':
            context = self.runtime.slot(int(n['object'], 0))
            return ('method', context) if context else None
        if n['op'] == 'var':
            if n['variable'] == self.method_argument and self.context:
                return ('method', self.context)
            assignment = self.aliases.get(n['variable'])
            if assignment and self.flow.dominates(assignment['id'], index):
                return self.value(assignment['y'], seen)
            return None
        if n['op'] == 'cast' and n['nativeType']['bytes'] == 8:
            return self.value(n['x'], seen)
        if n['op'] == 'ptr':
            return self.read(self.value(n['x'], seen), 0)
        if n['op'] == 'memptr':
            return self.read(self.value(n['x'], seen), n['offset'])
        if n['op'] in ('add', 'idx'):
            offset = self.nodes[n['y']]
            base = self.value(n['x'], seen)
            if offset['op'] != 'num' or base is None:
                return None
            scale = n['nativeType']['bytes'] if n['op'] == 'idx' else 1
            # 指针加法具有元素缩放；缺少元素布局时不猜测。
            if n['op'] == 'add' and self.nodes[n['x']]['nativeType']['kind'] == 'pointer':
                return None
            displacement = int(offset['number']) * scale
            return self.read(base, displacement) if n['op'] == 'idx' else ('offset', (base, displacement))
        return None

    def method(self, index):
        value = self.value(index)
        return value[1] if value and value[0] == 'method' else None
