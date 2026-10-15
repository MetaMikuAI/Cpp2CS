"""在数据库副本中顺序查询 IDA；JSON 请求从 stdin 读取，结果写入指定目录。"""
import os
import json
from pathlib import Path
import sys
import time

database = Path(sys.argv[1]).resolve()
output = Path(sys.argv[2]).resolve()
experiment = Path("D:/Cpp2CS/attempt-10/ida-session").resolve()
if "artifacts" not in database.parts and not database.is_relative_to(experiment):
    raise ValueError("只允许打开实验目录下的数据库副本")
output.mkdir(parents=True, exist_ok=True)
os.environ.setdefault("IDADIR", "C:/Program Files/IDA Professional 9.3")
os.environ.setdefault("IDALOG", str(output / "ida.log"))
print("Initializing idalib", flush=True)
import idapro

import ida_funcs
import ida_hexrays as hx
import ida_kernwin
import ida_lines
import ida_nalt
import idautils


class Tree(hx.ctree_visitor_t):
    def __init__(self):
        super().__init__(hx.CV_PARENTS)
        self.nodes = []

    def record(self, item, expression):
        node = {"id": item.index, "op": hx.get_ctype_name(item.op),
                "ea": hex(item.ea), "parents": [p.index for p in self.parents if p is not None]}
        if expression:
            node["type"] = str(item.type)
            if item.op == hx.cot_var:
                node["variable"] = item.v.idx
            elif item.op == hx.cot_obj:
                node["object"] = hex(item.obj_ea)
            elif item.op == hx.cot_num:
                node["number"] = str(item.numval())
            elif item.op in (hx.cot_memptr, hx.cot_memref):
                node["member_offset"] = item.m
        self.nodes.append(node)
        return 0

    def visit_expr(self, item):
        return self.record(item, True)

    def visit_insn(self, item):
        return self.record(item, False)


started = time.monotonic()
status = idapro.open_database(str(database), False)
if status != 0:
    raise RuntimeError(f"open_database: {status}")
if not hx.init_hexrays_plugin():
    raise RuntimeError("Hex-Rays 初始化失败")
info = {"ida": ida_kernwin.get_kernel_version(), "hexrays": hx.get_hexrays_version(),
        "input_sha256": ida_nalt.retrieve_input_file_sha256().hex(),
        "functions": ida_funcs.get_func_qty(), "open_seconds": time.monotonic() - started}
(output / "session.json").write_text(json.dumps(info, indent=2), encoding="utf-8")
print(json.dumps({"ready": info}), flush=True)
for line in sys.stdin:
    if not line.strip():
        continue
    request = json.loads(line)
    if request["action"] == "close":
        break
    if request["action"] == "describe":
        print(json.dumps({name: getattr(hx, name).__doc__ for name in request["names"]}), flush=True)
        continue
    if request["action"] != "decompile":
        raise ValueError(f"未知请求: {request['action']}")
    address = int(request["address"], 0)
    started = time.monotonic()
    function = ida_funcs.get_func(address)
    failure = hx.hexrays_failure_t()
    cfunc = hx.decompile(address, failure)
    result = {"address": hex(address), "name": ida_funcs.get_func_name(address),
              "function_start": hex(function.start_ea) if function else None,
              "function_end": hex(function.end_ea) if function else None,
              "decompiled": cfunc is not None, "failure": str(failure),
              "xrefs_to": [{"from": hex(x.frm), "type": x.type} for x in idautils.XrefsTo(address)],
              "blocks": None}
    if cfunc is not None:
        result["pseudocode"] = "\n".join(ida_lines.tag_remove(x.line) for x in cfunc.get_pseudocode())
        tree = Tree()
        tree.apply_to(cfunc.body, None)
        result["ctree"] = tree.nodes
        result["variables"] = [{"id": i, "name": v.name, "type": str(v.type()),
                                "width": v.width, "argument": v.is_arg_var}
                               for i, v in enumerate(cfunc.get_lvars())]
        result["warnings"] = [{"ea": hex(w.ea), "text": w.text} for w in cfunc.get_warnings()]
        result["blocks"] = cfunc.mba.qty
        result["microcode"] = []
        for i in range(cfunc.mba.qty):
            block = cfunc.mba.get_mblock(i)
            instructions = []
            instruction = block.head
            while instruction is not None:
                instructions.append({"ea": hex(instruction.ea), "text": instruction.dstr()})
                instruction = instruction.next
            result["microcode"].append({"id": i, "successors": list(block.succset),
                                         "instructions": instructions})
    result["seconds"] = time.monotonic() - started
    destination = output / f"{address:x}.json"
    destination.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps({"result": str(destination), "decompiled": result["decompiled"],
                      "nodes": len(result.get("ctree", [])), "warnings": len(result.get("warnings", [])),
                      "seconds": result["seconds"]}), flush=True)
idapro.close_database(False)
print(json.dumps({"closed": True, "saved": False}), flush=True)
