"""导出带操作数角色的 ctree；不从伪代码文本推断结构。"""
import ida_hexrays as hx
import ida_name


def type_info(t):
    kind = ("pointer" if t.is_ptr() else "bool" if t.is_bool() else
            "integer" if t.is_integral() or t.is_enum() else "float" if t.is_floating() else
            "void" if t.is_void() else "aggregate" if t.is_udt() else "other")
    result = {"name": str(t), "bytes": t.get_size(), "kind": kind,
              "signed": t.is_signed()}
    if t.is_ptr():
        result["pointee"] = str(t.get_pointed_object())
    return result


class Export(hx.ctree_visitor_t):
    def __init__(self):
        super().__init__(hx.CV_PARENTS)
        self.nodes = []

    def visit_expr(self, item):
        node = self.common(item)
        node["nativeType"] = type_info(item.type)
        for key, used in (("x", hx.op_uses_x), ("y", hx.op_uses_y), ("z", hx.op_uses_z)):
            if used(item.op):
                node[key] = getattr(item, key).index
        if item.op == hx.cot_var:
            node["variable"] = item.v.idx
        elif item.op == hx.cot_obj:
            node["object"] = hex(item.obj_ea)
            node["symbol"] = ida_name.get_name(item.obj_ea)
        elif item.op == hx.cot_num:
            node["number"] = str(item.numval())
        elif item.op in (hx.cot_memptr, hx.cot_memref):
            node["offset"] = item.m
        elif item.op == hx.cot_call:
            node["arguments"] = [a.index for a in item.a]
        elif item.op == hx.cot_helper:
            node["helper"] = item.helper
        self.nodes.append(node)
        return 0

    def common(self, item):
        return {"id": item.index, "op": hx.get_ctype_name(item.op), "ea": hex(item.ea),
                "label": item.label_num}

    def visit_insn(self, item):
        node = self.common(item)
        if item.op == hx.cit_block:
            node["items"] = [i.index for i in item.cblock]
        elif item.op == hx.cit_expr:
            node["expression"] = item.cexpr.index
        elif item.op == hx.cit_return:
            node["expression"] = item.creturn.expr.index
        elif item.op == hx.cit_if:
            node["condition"] = item.cif.expr.index
            node["then"] = item.cif.ithen.index
            node["else"] = item.cif.ielse.index if item.cif.ielse else None
        elif item.op == hx.cit_goto:
            node["target"] = item.cgoto.label_num
        elif item.op == hx.cit_while:
            node["condition"] = item.cwhile.expr.index
            node["body"] = item.cwhile.body.index
        self.nodes.append(node)
        return 0


def export(cfunc):
    # IDA 在生成显示文本时建立 treeitems 索引；不解析文本。
    cfunc.get_pseudocode()
    visitor = Export()
    visitor.apply_to(cfunc.body, None)
    ids = {n["id"] for n in visitor.nodes}
    if len(ids) != len(visitor.nodes) or min(ids) < 0:
        raise ValueError("ctree 节点索引无效")
    variables = [{"id": i, "name": v.name, "nativeType": type_info(v.type()),
                  "argument": v.is_arg_var} for i, v in enumerate(cfunc.get_lvars())]
    return {"schema": 1, "root": cfunc.body.index, "nodes": visitor.nodes,
            "arguments": list(cfunc.argidx), "variables": variables}
