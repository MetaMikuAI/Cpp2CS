#!/usr/bin/env python3
"""从 DWARF 抽取函数入口形参，保留未知项及栈位置换算证据。"""
import argparse
from bisect import bisect_right
from collections import Counter, defaultdict
import json
from pathlib import Path
import elftools
from elftools.elf.elffile import ELFFile
from elftools.dwarf.callframe import FDE
from elftools.dwarf.descriptions import describe_reg_name
from elftools.dwarf.dwarf_expr import DWARFExprParser
from elftools.dwarf.locationlists import LocationParser, LocationExpr
from extract import digest, require, write
from inline import decoded, inherited, ranges


def owner(die, key):
    if key in die.attributes:
        return die
    for ref in ('DW_AT_abstract_origin', 'DW_AT_specification'):
        if ref in die.attributes:
            found = owner(die.get_DIE_from_attribute(ref), key)
            if found is not None:
                return found
    return None


def type_of(die):
    source = owner(die, 'DW_AT_type')
    return source.get_DIE_from_attribute('DW_AT_type') if source else None


def shape(die, active=()):
    if die is None:
        return dict(kind='void', size=0)
    if die.offset in active:
        return dict(kind='unknown', reason='recursive_value_type')
    active = (*active, die.offset)
    tag = die.tag
    size = inherited(die, 'DW_AT_byte_size')
    if tag in ('DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type', 'DW_TAG_restrict_type'):
        return shape(type_of(die), active)
    if tag in ('DW_TAG_pointer_type', 'DW_TAG_reference_type', 'DW_TAG_rvalue_reference_type'):
        return dict(kind='pointer', size=size if size is not None else die.cu['address_size'])
    if tag == 'DW_TAG_base_type':
        encoding = inherited(die, 'DW_AT_encoding')
        kind = 'float' if encoding == 4 else 'integer' if encoding in (2, 5, 6, 7, 8, 16) else 'unknown'
        return dict(kind=kind, size=size, encoding=encoding)
    if tag == 'DW_TAG_enumeration_type':
        return dict(kind='integer', size=size, enum=True)
    if tag in ('DW_TAG_structure_type', 'DW_TAG_class_type', 'DW_TAG_union_type'):
        members = []
        for child in die.iter_children():
            if child.tag not in ('DW_TAG_member', 'DW_TAG_inheritance'):
                continue
            if inherited(child, 'DW_AT_external'):
                continue
            offset = inherited(child, 'DW_AT_data_member_location')
            if tag == 'DW_TAG_union_type' and offset is None:
                offset = 0
            members.append(dict(name=decoded(inherited(child, 'DW_AT_name')), offset=offset if isinstance(offset, int) else None,
                                shape=shape(type_of(child), active), bit_size=inherited(child, 'DW_AT_bit_size'),
                                bit_offset=inherited(child, 'DW_AT_bit_offset'), data_bit_offset=inherited(child, 'DW_AT_data_bit_offset')))
        return dict(kind='aggregate', size=size, layout=tag.removeprefix('DW_TAG_'), members=members)
    if tag == 'DW_TAG_array_type':
        element = shape(type_of(die), active)
        dimensions = []
        for child in die.iter_children():
            if child.tag == 'DW_TAG_subrange_type':
                count = inherited(child, 'DW_AT_count')
                high = inherited(child, 'DW_AT_upper_bound')
                low = inherited(child, 'DW_AT_lower_bound') or 0
                dimensions.append(count if count is not None else high-low+1 if isinstance(high, int) else None)
        if size is None and element.get('size') is not None and dimensions and all(n is not None for n in dimensions):
            size = element['size']
            for n in dimensions:
                size *= n
        return dict(kind='aggregate', layout='array', size=size, element=element, dimensions=dimensions)
    return dict(kind='unknown', size=size, reason=tag)


class Locations:
    def __init__(self, dwarf, arch, cfi):
        self.dwarf, self.arch, self.cfi = dwarf, arch, cfi
        self.parser = LocationParser(dwarf.location_lists())
        self.expr = DWARFExprParser(dwarf.structs)
        self.sp = 31 if arch == 'AArch64' else 7

    def reg(self, number):
        return dict(register=describe_reg_name(number, machine_arch=self.arch), dwarf_register=number)

    def select(self, die, key, pc):
        source = owner(die, key)
        if source is None:
            return None, 'no_location_attribute'
        value = self.parser.parse_from_attribute(source.attributes[key], source.cu['version'], die=source)
        if isinstance(value, LocationExpr):
            return value.loc_expr, 'expression'
        base = source.cu.get_top_DIE().attributes.get('DW_AT_low_pc')
        base = base.value if base else 0
        matches = []
        for entry in value:
            if hasattr(entry, 'base_address'):
                base = entry.base_address
            else:
                start = entry.begin_offset + (0 if entry.is_absolute else base)
                end = entry.end_offset + (0 if entry.is_absolute else base)
                if start <= pc < end:
                    matches.append(entry.loc_expr)
        require(len(matches) <= 1, '入口位置列表重叠')
        return (matches[0], 'location_list') if matches else (None, 'no_range_at_entry')

    def operations(self, expression):
        def serialize(op):
            return dict(op=op.op_name, args=[[serialize(x) for x in a] if isinstance(a, list) and a and hasattr(a[0], 'op_name') else a for a in op.args])
        return [serialize(op) for op in self.expr.parse_expr(expression)]

    def cfa(self, pc):
        index = bisect_right(self.cfi[0], pc)-1
        if index < 0:
            return None
        start, end, rule = self.cfi[1][index]
        if not start <= pc < end or rule.expr is not None:
            return None
        return dict(**self.reg(rule.reg), offset=rule.offset, entry_sp_offset=rule.offset if rule.reg == self.sp else None)

    def decode(self, ops, cfa, frame):
        pieces, segment, bit = [], [], 0
        def one(code):
            if not code:
                return dict(kind='unknown', reason='unavailable_piece')
            name, args = code[0]['op'], code[0]['args']
            if name in ('DW_OP_entry_value', 'DW_OP_GNU_entry_value'):
                if len(code) == 1 or (len(code) == 2 and code[1]['op'] == 'DW_OP_stack_value'):
                    return dict(kind='unknown', reason='entry_value_only', entry_value_pieces=self.decode(args[0], cfa, frame))
            if name.startswith('DW_OP_breg') and code[-1]['op'] == 'DW_OP_stack_value':
                n, delta = (args[0], args[1]) if name == 'DW_OP_bregx' else (int(name[10:]), args[0])
                middle = code[1:-1]
                shift = 0
                if len(middle) == 2 and middle[0]['op'] == 'DW_OP_constu' and middle[1]['op'] == 'DW_OP_shr':
                    shift = middle[0]['args'][0]
                    middle = []
                if delta == 0 and not middle:
                    return dict(kind='register', **self.reg(n), location_bit_offset=shift, derivation='register_value_expression')
            if len(code) != 1:
                return dict(kind='unknown', reason='unsupported_expression')
            if name.startswith('DW_OP_reg'):
                n = args[0] if name == 'DW_OP_regx' else int(name[9:])
                return dict(kind='register', **self.reg(n))
            if name.startswith('DW_OP_breg'):
                n, offset = (args[0], args[1]) if name == 'DW_OP_bregx' else (int(name[10:]), args[0])
                return dict(kind='stack', offset=offset) if n == self.sp else dict(kind='indirect', **self.reg(n), offset=offset)
            if name in ('DW_OP_fbreg', 'DW_OP_call_frame_cfa'):
                base = frame if name == 'DW_OP_fbreg' else cfa
                delta = args[0] if args else 0
                return dict(kind='stack', offset=base['entry_sp_offset']+delta) if base and base.get('entry_sp_offset') is not None else dict(kind='unknown', reason='unresolved_frame_base')
            return dict(kind='unknown', reason='unsupported_expression')
        for op in ops:
            if op['op'] in ('DW_OP_piece', 'DW_OP_bit_piece'):
                count = op['args'][0] * 8 if op['op'] == 'DW_OP_piece' else op['args'][0]
                piece = one(segment)
                piece.update(value_bit_offset=bit, size_bits=count, location_bit_offset=piece.get('location_bit_offset', 0)+(0 if op['op'] == 'DW_OP_piece' else op['args'][1]))
                pieces.append(piece)
                segment = []
                bit += count
            else:
                segment.append(op)
        if segment:
            piece = one(segment)
            piece.update(value_bit_offset=bit, size_bits=None, location_bit_offset=piece.get('location_bit_offset', 0))
            pieces.append(piece)
        return pieces or [dict(kind='unknown', reason='empty_expression')]

    def frame(self, die, pc, cfa, rs):
        raw, source = self.select(die, 'DW_AT_frame_base', pc)
        ops = self.operations(raw) if raw is not None else []
        offset = None
        if len(ops) == 1:
            op = ops[0]
            if op['op'] == 'DW_OP_call_frame_cfa' and cfa:
                offset = cfa['entry_sp_offset']
            elif op['op'] == 'DW_OP_reg'+str(self.sp) or (op['op'] == 'DW_OP_regx' and op['args'] == [self.sp]):
                offset = 0
        # clang 的固定 fbreg 可能以序言后的 SP 为基址，即使其范围覆盖入口。
        # 只有 CFI 证明整个函数的 SP 基址不变，才将这种帧基址当作入口 SP。
        stable = True
        if offset == 0 and ops and ops[0]['op'] != 'DW_OP_call_frame_cfa':
            stable = cfa is not None and cfa['entry_sp_offset'] is not None
            for lo, hi in rs:
                index = max(0, bisect_right(self.cfi[0], lo)-1)
                covered = lo
                for row_index in range(index, len(self.cfi[1])):
                    start, end, rule = self.cfi[1][row_index]
                    if start >= hi:
                        break
                    if end <= lo:
                        continue
                    if start > covered or rule.expr is not None or rule.reg != self.sp or not cfa or rule.offset != cfa['offset']:
                        stable = False
                    covered = max(covered, end)
                stable = stable and covered >= hi
            if not stable:
                offset = None
        return dict(source=source, expression=ops, entry_sp_offset=offset, sp_stable=stable,
                    reason=None if offset is not None else 'frame_base_not_proven_at_entry')


def cfi_index(elf):
    dwarf = elf.get_dwarf_info()
    entries = dwarf.EH_CFI_entries() if dwarf.has_EH_CFI() else dwarf.CFI_entries() if dwarf.has_CFI() else []
    rows = []
    for fde in entries:
        if isinstance(fde, FDE):
            table = fde.get_decoded().table
            for i, row in enumerate(table):
                end = table[i+1]['pc'] if i+1 < len(table) else fde['initial_location']+fde['address_range']
                if row['pc'] < end:
                    rows.append((row['pc'], end, row['cfa']))
    rows.sort(key=lambda r: r[:2])
    return [r[0] for r in rows], rows


def extract(debug, binary, wanted):
    with binary.open('rb') as stream:
        cfi = cfi_index(ELFFile(stream))
    result = defaultdict(list)
    with debug.open('rb') as stream:
        elf = ELFFile(stream)
        require(elf.get_machine_arch() in ('AArch64', 'x64'), '仅支持两个已验证的寄存器命名表')
        dwarf = elf.get_dwarf_info()
        loc = Locations(dwarf, elf.get_machine_arch(), cfi)
        for cu in dwarf.iter_CUs():
            for die in cu.iter_DIEs():
                if die.tag != 'DW_TAG_subprogram':
                    continue
                rs = ranges(die, dwarf, cu)
                if not rs:
                    continue
                pc = min(lo for lo, hi in rs)
                if pc not in wanted:
                    continue
                cfa = loc.cfa(pc)
                frame = loc.frame(die, pc, cfa, rs)
                params = []
                children = list(die.iter_children())
                # 具体 DIE 的形参通过 abstract_origin 继承类型与名字，位置仍来自具体实例。
                for child in children:
                    if child.tag != 'DW_TAG_formal_parameter':
                        continue
                    raw, source = loc.select(child, 'DW_AT_location', pc)
                    ops = loc.operations(raw) if raw is not None else []
                    pieces = loc.decode(ops, cfa, frame) if raw is not None else []
                    parameter_shape = shape(type_of(child))
                    size = parameter_shape.get('size')
                    if pieces and size is not None:
                        end = pieces[-1].get('value_bit_offset', 0)
                        if pieces[-1].get('size_bits') is None and pieces[-1]['kind'] != 'unknown':
                            pieces[-1]['size_bits'] = max(0, size*8-end)
                        elif pieces[-1].get('size_bits') is not None and end+pieces[-1]['size_bits'] < size*8:
                            end += pieces[-1]['size_bits']
                            pieces.append(dict(kind='unknown', reason='unreported_tail', value_bit_offset=end, size_bits=size*8-end))
                    known = bool(pieces) and all(p['kind'] != 'unknown' for p in pieces)
                    params.append(dict(index=len(params), name=decoded(inherited(child, 'DW_AT_name')), shape=parameter_shape,
                                       die=hex(child.offset), artificial=bool(inherited(child, 'DW_AT_artificial')),
                                       location=dict(known=known, source=source, expression=ops, pieces=pieces,
                                                     reason=None if known else source if raw is None else ','.join(sorted({p['reason'] for p in pieces if p['kind'] == 'unknown'})))))
                record = dict(die=hex(die.offset), dwarf_name=decoded(inherited(die, 'DW_AT_name')), parameters=params,
                              return_shape=shape(type_of(die)), frame_base=frame, entry_cfa=cfa,
                              variadic=any(c.tag == 'DW_TAG_unspecified_parameters' for c in children))
                for name in wanted[pc]:
                    result[name].append(record)
            cu._dielist.clear()
            cu._diemap.clear()
    return result


def has_float(s):
    return s['kind'] == 'float' or any(has_float(m['shape']) for m in s.get('members', [])) or ('element' in s and has_float(s['element']))


def summary(rows):
    groups = {g: dict(count=0, known=0) for g in ('integer_pointer', 'float', 'aggregate_le16', 'aggregate_gt16', 'aggregate_float', 'observed_stack')}
    params = [p for r in rows for d in r['records'] for p in d['parameters']]
    reasons = Counter()
    for p in params:
        s, loc = p['shape'], p['location']
        tags = []
        if s['kind'] in ('integer', 'pointer'):
            tags.append('integer_pointer')
        if s['kind'] == 'float':
            tags.append('float')
        if s['kind'] == 'aggregate':
            if s.get('size') is not None:
                tags.append('aggregate_le16' if s['size'] <= 16 else 'aggregate_gt16')
            if has_float(s):
                tags.append('aggregate_float')
        if any(x['kind'] == 'stack' for x in loc['pieces']):
            tags.append('observed_stack')
        for tag in tags:
            groups[tag]['count'] += 1
            groups[tag]['known'] += loc['known']
        if not loc['known']:
            reasons[loc['reason']] += 1
    known = sum(p['location']['known'] for p in params)
    return dict(functions=len(rows), debug_functions=sum(bool(r['records']) for r in rows), parameters=len(params), known=known,
                known_fraction=known/len(params) if params else None, groups=groups, unknown_reasons=dict(sorted(reasons.items())),
                unknown_shapes=sum(p['shape']['kind'] == 'unknown' or p['shape'].get('size') is None for p in params))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('input', 'truth', 'output', 'cache'):
        parser.add_argument('--'+name, type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists() or not any(args.output.iterdir()), '输出目录必须为空')
    for destination in (args.output, args.cache):
        require(not any(destination.resolve().is_relative_to(p.resolve()) for p in (args.input, args.truth)), '不得写入输入目录')
    require(args.cache.resolve() != args.output.resolve(), '缓存与输出必须分开')
    load = lambda name: json.loads((args.truth/(name+'.json')).read_text())
    manifest = load('manifest')
    for filename, expected in manifest['outputs'].items():
        require(digest(args.truth/filename) == expected, '真值校验失败：'+filename)
    for item in manifest['inputs']:
        path = (args.input/item['path']).resolve()
        require(path.is_relative_to(args.input.resolve()), '输入路径越界')
        require(path.stat().st_size == item['bytes'] and digest(path) == item['sha256'], '产物校验失败：'+item['path'])
    args.output.mkdir(parents=True, exist_ok=True)
    args.cache.mkdir(parents=True, exist_ok=True)
    methods = defaultdict(set)
    for m in load('mappings'):
        if m['method_id']:
            methods[m['cpp_name']].add(m['method_id'])
    hashes = {}
    for target in ('arm64-v8a', 'x86_64'):
        selected = {f['cpp_name']: f for f in load('functions.'+target) if f['defined'] and f['cpp_name'] in methods}
        wanted = defaultdict(list)
        for name, f in selected.items():
            wanted[int(f['address'], 16)].append(name)
        root = args.input/'artifacts/il2cppOutput/build'/target
        debug, binary = root/'libil2cpp.dbg.so', root/'libil2cpp.so'
        hashes[target] = dict(debug=digest(debug), binary=digest(binary))
        key = hashes[target]['debug']+hashes[target]['binary']+digest(Path(__file__))+digest(Path(__file__).with_name('inline.py'))+digest(args.truth/'mappings.json')+digest(args.truth/('functions.'+target+'.json'))
        cached = args.cache/(target+'.local.json')
        previous = json.loads(cached.read_text()) if cached.exists() else None
        if previous and previous['key'] == key:
            records = previous['records']
        else:
            print('DWARF', target, flush=True)
            records = extract(debug, binary, wanted)
            write(cached, dict(key=key, records=records))
        rows = [dict(cpp_name=n, method_ids=sorted(methods[n]), address=f['address'], size=f['size'], records=records.get(n, [])) for n, f in sorted(selected.items())]
        by_name = {r['cpp_name']: r for r in rows}
        cases = [dict(case=c['case'], method_id=c['method']['id'], **by_name[c['mapping']['cpp_name']]) for c in load('cases')]
        require(all(c['records'] for c in cases), '用例缺少调试函数')
        write(args.output/('parameters.'+target+'.json'), rows)
        write(args.output/('parameter-cases.'+target+'.json'), cases)
        report = dict(all=summary(rows), cases=summary(cases))
        report['gaps'] = [dict(group=g, count=v['count'], known=v['known'], reason='absent' if v['count'] == 0 else 'fewer_than_five' if v['count'] < 5 else 'incomplete_locations')
                          for g,v in report['cases']['groups'].items() if v['count'] < 5 or v['known'] < v['count']]
        write(args.output/('parameter-summary.'+target+'.json'), report)
        print(target, report, flush=True)
    write(args.output/'parameter-manifest.json', dict(version=1, tool_sha256=digest(Path(__file__)), dependencies=dict(pyelftools=elftools.__version__), helper_sha256={n:digest(Path(__file__).with_name(n)) for n in ('inline.py', 'extract.py')}, binaries=hashes,
          inputs={p.name:digest(p) for p in sorted(args.truth.glob('*.json'))}, outputs={p.name:digest(p) for p in sorted(args.output.glob('*.json'))}))


if __name__ == '__main__':
    main()
