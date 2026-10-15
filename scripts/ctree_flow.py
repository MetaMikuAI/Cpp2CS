"""ctree 语句图及支配关系，仅供调用证据中的局部别名判断。"""
class Flow:
    def __init__(self, tree):
        self.nodes = {n['id']: n for n in tree['nodes']}
        self.edges = {-1: set()}
        self.anchors = {}
        self.labels = {}
        self.jumps = []
        self.assignments = set()
        self.entry = self.statement(tree['root'], -1, None, None)
        for source, label in self.jumps:
            self.edges[source] = {self.labels[label]}
        reachable = set()
        pending = [self.entry]
        while pending:
            node = pending.pop()
            if node is not None and node not in reachable:
                reachable.add(node)
                pending.extend(self.edges[node])
        predecessors = {n: set() for n in reachable}
        for node in reachable:
            for successor in self.edges[node] & reachable:
                predecessors[successor].add(node)
        self.dominators = {n: {n} if n == self.entry else set(reachable) for n in reachable}
        changed = True
        while changed:
            changed = False
            for node in reachable - {self.entry}:
                before = set.intersection(*(self.dominators[p] for p in predecessors[node])) | {node}
                if before != self.dominators[node]:
                    self.dominators[node] = before
                    changed = True

    def expression(self, index, anchor):
        n = self.nodes[index]
        self.anchors[index] = anchor
        for role in ('x', 'y', 'z'):
            if role in n:
                self.expression(n[role], anchor)
        for child in n.get('arguments', []):
            self.expression(child, anchor)

    def statement(self, index, next_, break_, continue_):
        n = self.nodes[index]
        op = n['op']
        successors = {next_} if next_ is not None else set()
        entry = index
        if op == 'block':
            for child in reversed(n['items']):
                next_ = self.statement(child, next_, break_, continue_)
            successors = {next_} if next_ is not None else set()
        elif op == 'if':
            successors = {self.statement(n['then'], next_, break_, continue_),
                          self.statement(n['else'], next_, break_, continue_) if n.get('else') is not None else next_}
            self.expression(n['condition'], index)
        elif op in ('while', 'do', 'for'):
            step = index
            if op == 'for':
                step = n['step']
                self.edges[step] = {index}
                self.expression(step, step)
            body = self.statement(n['body'], step, next_, step)
            successors = {body, next_}
            self.expression(n['condition'], index)
            if op == 'do':
                entry = body
            elif op == 'for':
                entry = n['init']
                self.edges[entry] = {index}
                self.expression(entry, entry)
        elif op == 'switch':
            case_next = next_
            successors = {next_}
            for case in reversed(n['cases']):
                case_next = self.statement(case['body'], case_next, next_, continue_)
                successors.add(case_next)
            self.expression(n['expression'], index)
        elif op == 'goto':
            self.jumps.append((index, n['target']))
            successors = set()
        elif op in ('break', 'continue'):
            target = break_ if op == 'break' else continue_
            if target is None:
                raise ValueError('break/continue 缺少目标')
            successors = {target}
        elif op in ('expr', 'return'):
            self.expression(n['expression'], index)
            if op == 'return':
                successors = set()
            elif self.nodes[n['expression']]['op'] == 'asg':
                self.assignments.add(n['expression'])
        elif op != 'empty':
            raise ValueError('调用证据的控制流尚未支持: ' + op)
        self.edges[index] = successors - {None}
        if n.get('label', -1) >= 0:
            self.labels[n['label']] = entry
        return entry

    def dominates(self, assignment, use):
        source, target = self.anchors.get(assignment), self.anchors.get(use)
        return assignment in self.assignments and source != target and source in self.dominators.get(target, set())
