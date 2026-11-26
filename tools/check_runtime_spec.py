"""用法：python check_runtime_spec.py 调试库 符号库 libil2cpp源码目录。需要 pyelftools。"""

import argparse
from dataclasses import dataclass
from pathlib import Path
import re

from elftools.elf.elffile import ELFFile


SPEC = Path(__file__).resolve().parents[1] / "src/Cpp2CS.Spec/Runtime"


@dataclass(frozen=True)
class Field:
    name: str
    expected: int
    header: str
    measure: str
    subject: str


def layout_fields():
    source = (SPEC / "RuntimeLayout.cs").read_text()
    declarations, initializer = source.split("public static RuntimeLayout Unity2022Lp64")
    names = re.findall(r"\b(?:int|long) (\w+)", declarations)
    fields = []
    for line in initializer.splitlines():
        if not re.match(r"\s*\w+\s*[:=]", line):
            continue
        row = re.fullmatch(
            r"\s*(\w+)\s*[:=]\s*(0x[0-9a-fA-F]+|[0-9]+)[,)]\s*// (\S+\.h)(?: [^|]+)? \| (\w+) (\S+)\s*", line)
        if row is None:
            raise ValueError(f"布局项缺少数字或量法：{line}")
        name, value, header, measure, subject = row.groups()
        fields.append(Field(name, int(value, 0), header, measure, subject))
    if sorted(f.name for f in fields) != sorted(names) or not fields:
        raise ValueError("布局声明、初值和量法未逐项对应")
    return fields


def registered_symbols():
    source = (SPEC / "RuntimeSpec.cs").read_text()
    entries = source.split("ImmutableArray<RuntimeOperation> entries =", 1)[1].split("];", 1)[0]
    # 构造器的第二个参数是符号表；Raise 的末尾是 params 符号。无法解析的条目报错。
    entries = entries.strip().removeprefix("[").strip()
    chunks = re.split(r",\s*\n\s*(?=(?:new|Raise)\()", entries)
    symbols = []
    literal = r'"([^"\\]+)"'
    for chunk in chunks:
        if chunk.startswith("Raise("):
            match = re.fullmatch(r'Raise\("[^"]+",\s*ExceptionKind\.\w+,\s*"[^"]+",\s*(.*?)\),?', chunk, re.S)
        else:
            match = re.match(r'new\("[^"]+",\s*\[([^\]]*)\],\s*RuntimeEffect\.\w+', chunk, re.S)
        if match is None or not re.fullmatch(rf'{literal}(?:,\s*{literal})*', match[1].strip()):
            raise ValueError(f"无法读取登记的符号：{chunk[:80]}")
        symbols.extend(re.findall(literal, match[1]))
    if len(set(symbols)) != len(symbols):
        raise ValueError("操作之间存在重复符号")
    return symbols


def dwarf_definitions(dwarf, fields):
    wanted = {(f.measure if f.measure in ("castbits", "constant") else "struct", f.subject.split(".")[0]): f.header
              for f in fields if f.measure != "macro"}
    definitions = {}
    # 先看包含结构定义的运行时翻译单元，避免逐个展开无关方法的调试信息。
    def priority(cu):
        lines = dwarf.line_program_for_CU(cu)
        names = {f.name.replace(b"\\", b"/").rsplit(b"/", 1)[-1] for f in lines["file_entry"]} if lines else set()
        return not bool(names & {b"Array.cpp", b"Object.cpp", b"PlatformInvoke.cpp"})
    for cu in sorted(dwarf.iter_CUs(), key=priority):
        for die in cu.iter_DIEs():
            attr = die.attributes
            if die.tag == "DW_TAG_structure_type" and "DW_AT_byte_size" in attr:
                kind = "struct"
            elif die.tag == "DW_TAG_variable" and "DW_AT_const_value" in attr:
                kind = "constant"
            elif die.tag == "DW_TAG_typedef":
                kind = "castbits"
            else:
                continue
            if "DW_AT_name" not in attr:
                continue
            key = kind, attr["DW_AT_name"].value.decode()
            if key in wanted:
                if kind != "castbits":
                    lines = dwarf.line_program_for_CU(cu)
                    decl = attr.get("DW_AT_decl_file")
                    if not decl or not lines:
                        continue
                    index = decl.value - int(lines.header.version < 5)
                    filename = lines["file_entry"][index].name.replace(b"\\", b"/").split(b"/")[-1].decode()
                    if filename != Path(wanted[key]).name:
                        continue
                definitions[key] = die
                del wanted[key]
                if not wanted:
                    return definitions
    return definitions


def members(die, base=0):
    for member in die.iter_children():
        if member.tag != "DW_TAG_member":
            continue
        a = member.attributes
        if "DW_AT_data_bit_offset" in a:
            offset = a["DW_AT_data_bit_offset"].value // 8
        elif "DW_AT_data_member_location" in a:
            offset = a["DW_AT_data_member_location"].value
            if "DW_AT_bit_offset" in a:
                start = a["DW_AT_bit_offset"].value
                if member.cu.structs.little_endian:
                    start = type_bits(member) - start - a["DW_AT_bit_size"].value
                offset += start // 8
        elif die.tag == "DW_TAG_union_type":
            offset = 0
        else:
            raise ValueError("成员没有常量偏移")
        if "DW_AT_name" in a:
            yield a["DW_AT_name"].value.decode(), (base + offset, member)
        else:
            yield from members(member.get_DIE_from_attribute("DW_AT_type"), base + offset)


def type_bits(die):
    while "DW_AT_byte_size" not in die.attributes:
        if die.tag == "DW_TAG_pointer_type":
            return die.cu["address_size"] * 8
        die = die.get_DIE_from_attribute("DW_AT_type")
    return die.attributes["DW_AT_byte_size"].value * 8


def measured(field, definitions, source):
    subject, _, member_names = field.subject.partition(".")
    if field.measure == "macro":
        header = (source / field.header).read_text()
        match = re.search(rf"^#define\s+{re.escape(subject)}\s+\(\(int32_t\)\s*(0x[0-9a-fA-F]+)\)\s*$", header, re.M)
        return int(match[1], 0) if match else None
    kind = field.measure if field.measure in ("constant", "castbits") else "struct"
    die = definitions.get((kind, subject))
    if die is None:
        return None
    if kind == "constant":
        return die.attributes["DW_AT_const_value"].value
    if kind == "castbits":
        header = (source / field.header).read_text()
        macro = re.search(r"^#define IL2CPP_ARRAY_BOUNDS_CHECK\(index, length\).*?while \(0\)", header, re.M | re.S)
        if macro and re.search(rf">=\s*\(\({re.escape(subject)}\)length\)", macro[0]):
            return type_bits(die)
        return None
    if field.measure == "size":
        return die.attributes["DW_AT_byte_size"].value
    offsets = dict(members(die))
    if any(name not in offsets for name in member_names.split(",")):
        return None
    if field.measure == "bitbyte":
        items = [offsets[name] for name in member_names.split(",")]
        if any("DW_AT_bit_size" not in m.attributes or m.attributes["DW_AT_bit_size"].value != 1 for _, m in items):
            return None
        locations = {offset for offset, _ in items}
        return locations.pop() if len(locations) == 1 else None
    offset, member = offsets[member_names]
    if field.measure == "offset":
        return offset
    if field.measure == "bits":
        return type_bits(member.get_DIE_from_attribute("DW_AT_type"))
    raise ValueError(f"未知量法：{field.measure}")


def build_id(elf):
    notes = elf.get_section_by_name(".note.gnu.build-id")
    return next((n["n_desc"] for n in notes.iter_notes() if n["n_type"] == "NT_GNU_BUILD_ID"), None) if notes else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("debug", "symbols", "source"):
        parser.add_argument(name, type=Path)
    args = parser.parse_args()
    fields = layout_fields()
    with args.debug.open("rb") as debug_file, args.symbols.open("rb") as symbol_file:
        debug, symbols = ELFFile(debug_file), ELFFile(symbol_file)
        if not build_id(debug) or build_id(debug) != build_id(symbols):
            parser.error("调试库与符号库的构建标识不匹配")
        definitions = dwarf_definitions(debug.get_dwarf_info(relocate_dwarf_sections=False), fields)
        ok = dwarf_ok = 0
        for field in fields:
            value = measured(field, definitions, args.source)
            if value == field.expected:
                ok += 1
                dwarf_ok += field.measure != "macro"
            else:
                print(f"{field.name}：登记 {field.expected}，实测 {value}")
        table = symbols.get_section_by_name(".symtab")
        if table is None:
            parser.error("缺少 .symtab")
        found = {s.name for s in table.iter_symbols()
                 if s["st_info"]["type"] == "STT_FUNC" and s["st_shndx"] != "SHN_UNDEF"}
    expected = registered_symbols()
    missing = sorted(set(expected) - found)
    for symbol in missing:
        print(f"缺少函数符号：{symbol}")
    dwarf_total = sum(f.measure != "macro" for f in fields)
    print(f"DWARF 一致 {dwarf_ok}/{dwarf_total}（含比较宏所用整数类型），源码宏一致 {ok-dwarf_ok}/{len(fields)-dwarf_total}")
    print(f"布局与语义数值一致 {ok}/{len(fields)}，登记符号存在 {len(expected)-len(missing)}/{len(expected)}")
    return int(ok != len(fields) or bool(missing))


if __name__ == "__main__":
    raise SystemExit(main())
