"""核对 layouts 的 JSON 行。生成的登记表只提供模型坐标对应的 C++ 类型与成员名。"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import subprocess


def dwarf_index(path):
    # readelf 解释 DWARF，按 DIE 深度保留成员所属的结构；忽略位置表与代码。
    select = r'''
    function finish() { if (keep) print die, parent, tag, name, size, offset, ref }
    BEGIN { OFS="\t" }
    /^ <[0-9]+></ {
        finish()
        split($1, a, /[<>]/)
        depth=a[2]+0; die=a[4]; parent=stack[depth-1]; stack[depth]=die
        tag=$NF; gsub(/[()]/, "", tag)
        keep=(tag ~ /^DW_TAG_(structure_type|class_type|union_type|base_type|typedef|member|enumeration_type|pointer_type)$/)
        name=size=offset=ref=""; next
    }
    !keep { next }
    / DW_AT_name +:/ { name=$0; sub(/^.* DW_AT_name *: /,"",name); sub(/^\(indirect string[^)]*\): /,"",name) }
    / DW_AT_byte_size +:/ { size=$NF }
    / DW_AT_data_member_location *:/ { offset=$0; sub(/^.* DW_AT_data_member_location *: /,"",offset) }
    / DW_AT_type +:/ { ref=$NF; gsub(/^<0x|>$/,"",ref) }
    END { finish() }
    '''
    nodes = {}
    children = defaultdict(list)
    with subprocess.Popen(["readelf", "-wi", str(path)], stdout=subprocess.PIPE) as dump:
        with subprocess.Popen(["awk", select], stdin=dump.stdout, stdout=subprocess.PIPE,
                              text=True, encoding="utf-8", errors="replace") as filtered:
            dump.stdout.close()
            for line in filtered.stdout:
                die, parent, tag, name, size, offset, ref = line.rstrip("\n").split("\t", 6)
                if tag == "DW_TAG_member":
                    children[parent].append((name, offset, ref))
                else:
                    nodes[die] = (tag, name, size, ref)
            if filtered.wait():
                raise RuntimeError("DWARF 属性筛选失败")
        if dump.wait():
            raise RuntimeError("readelf 无法读取调试信息")

    sizes = defaultdict(set)
    members = defaultdict(lambda: defaultdict(set))

    def number(value):
        return int(value, 0) if re.fullmatch(r"(?:0x[\da-fA-F]+|\d+)", value) else None

    def add_members(name, die, origin):
        for member, offset, ref in children.get(die, ()):
            at = number(offset)
            if at is None and not offset and nodes[die][0] == "DW_TAG_union_type":
                at = 0
            if at is None:
                continue
            if member:
                members[name][member].add(origin + at)
            elif ref in nodes:
                add_members(name, ref, origin + at)

    for die, (_, name, _, _) in nodes.items():
        if not name:
            continue
        target = die
        while target in nodes and nodes[target][0] == "DW_TAG_typedef":
            target = nodes[target][3]
        if target not in nodes:
            continue
        size = number(nodes[target][2])
        if size is not None:
            sizes[name].add(size)
            add_members(name, target, 0)
    return sizes, members


def generated_tables(cpp):
    text = (cpp / "Il2CppCCalculateTypeValues.cpp").read_text("utf-8-sig")
    types = {int(i): name for i, name in re.findall(r"g_typeDefinitionSize(\d+)\s*=\s*\{\s*sizeof\((\w+)\)", text)}
    text = (cpp / "Il2CppCCalculateFieldValues.cpp").read_text("utf-8-sig")
    fields = {}
    for i, length, body in re.findall(r"g_FieldOffsetTable(\d+)\[(\d+)\]\s*=\s*\{([^}]+)\}", text):
        start = depth = 0
        entries = []
        for j, char in enumerate(body):
            if char == "," and depth == 0:
                entries.append(body[start:j].strip())
                start = j + 1
            depth += (char == "(") - (char == ")")
        if body[start:].strip():
            entries.append(body[start:].strip())
        if len(entries) != int(length):
            raise ValueError(f"字段登记项数不符 {i}")
        fields[int(i)] = entries
    text = (cpp / "Il2CppGenericClassTable.c").read_text("utf-8-sig")
    table = re.search(r"g_Il2CppGenericTypes\[(\d+)\]\s*=\s*\{([^}]+)\}", text)
    classes = [s.strip().removeprefix("&").removesuffix("_GenericClass") for s in table[2].split(",") if s.strip()]
    if len(classes) != int(table[1]):
        raise ValueError("泛型类型登记项数不符")
    return types, fields, classes


def compare(rows, cpp, sizes, members, details):
    types, fields, classes = generated_tables(cpp)
    headers = sizes.get("Il2CppObject", set())
    if len(headers) != 1:
        raise ValueError("DWARF 没有唯一的对象头大小")
    header = next(iter(headers))
    counts = defaultdict(Counter)
    seen = set()
    open_types = 0

    def check(kind, where, actual, truth, reason):
        result = "缺依据" if len(truth) != 1 or actual is None else "一致" if actual in truth else "不一致"
        counts[kind][result] += 1
        if result != "一致":
            print(json.dumps(dict(item=where, kind=kind, actual=actual, dwarf=sorted(truth), reason=reason
                                  if result == "缺依据" else "适配器数值与 DWARF 不同"), ensure_ascii=False), file=details)

    for row in rows:
        definition, generic = row["definition"], row["generic"]
        coordinate = ("类型", row["key"]) if row["key"] is not None else ("登记行", definition, generic)
        if coordinate in seen:
            continue
        seen.add(coordinate)
        if row["open"]:
            open_types += 1
            continue
        prefix = "定义" if generic is None else "实例"
        cpp_type = types.get(definition) if generic is None else classes[generic] if generic >= 0 else None
        where = f"{definition}/{generic}/{row['key']}"
        if row["value"]:
            check(prefix + "大小", where, row["size"], sizes.get(cpp_type, set()),
                  row["sizeReason"] or f"DWARF 无唯一类型大小 {cpp_type}")
        for field in row["fields"]:
            cpp_owner, member = cpp_type, None
            instance = field["storage"] == "Instance"
            add_header = header if row["value"] and instance else 0
            truth = set()
            if generic is None:
                expr = fields[definition][field["Ordinal"]]
                match = re.search(r"offsetof\((\w+),\s*(\w+)\)", expr)
                if match:
                    cpp_owner, member = match.groups()
                elif expr == "static_cast<int32_t>(sizeof(RuntimeObject))":
                    # 标量值类型仅有底层存储，装箱后的起点是 DWARF 的对象头末尾。
                    truth = {header}
            else:
                suffix = {"Instance": "", "Static": "_StaticFields", "ThreadStatic": "_ThreadStaticFields"}
                cpp_owner = cpp_type + suffix[field["storage"]] if cpp_type else None
                member = "___" + re.sub(r"[^A-Za-z0-9_]", lambda m: "U" + format(ord(m[0]), "X"), field["Name"])
            if member:
                truth = {v + add_header for v in members.get(cpp_owner, {}).get(member, ())}
            check(prefix + "字段", where + "/" + str(field["i"]), field["offset"], truth,
                  field["reason"] or f"DWARF 无唯一成员偏移 {cpp_owner}.{member}")
    print(f"类型 {len(seen)}，开放类型 {open_types}（无具体布局）")
    for kind, c in sorted(counts.items()):
        print(f"{kind} 一致 {c['一致']} / {c.total()}，不一致 {c['不一致']}，缺依据 {c['缺依据']}")
    return sum(c["不一致"] + c["缺依据"] for c in counts.values())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("layouts", type=Path)
    parser.add_argument("cpp", type=Path)
    parser.add_argument("elf", type=Path)
    parser.add_argument("details", type=Path)
    args = parser.parse_args()
    size_index, member_index = dwarf_index(args.elf)
    with args.layouts.open() as source, args.details.open("w") as output:
        holes = compare(map(json.loads, source), args.cpp, size_index, member_index, output)
    raise SystemExit(1 if holes else 0)
