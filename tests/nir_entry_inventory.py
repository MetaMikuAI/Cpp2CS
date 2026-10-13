"""从二进制自身的函数入口记录挑选短函数，供 NIR 对照验证；不推断托管签名。"""
import argparse
import hashlib
import json
import struct
from pathlib import Path

import capstone
import pefile
from elftools.elf.elffile import ELFFile


def collect_arm(path):
    samples = []
    decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_LITTLE_ENDIAN)
    with path.open("rb") as stream:
        elf = ELFFile(stream)
        segments = [segment for segment in elf.iter_segments() if segment["p_type"] == "PT_LOAD"]
        table = elf.get_section_by_name(".dynsym")
        for symbol_index, symbol in enumerate(table.iter_symbols()):
            start, size = symbol["st_value"], symbol["st_size"]
            if symbol["st_info"]["type"] != "STT_FUNC" or not 4 <= size <= 80:
                continue
            segment = next((s for s in segments if s["p_vaddr"] <= start < s["p_vaddr"] + s["p_filesz"]), None)
            if segment is None or not segment["p_flags"] & 1:
                continue
            offset = segment["p_offset"] + start - segment["p_vaddr"]
            stream.seek(offset)
            raw = stream.read(size)
            decoded = list(decoder.disasm_lite(raw, start))
            if sum(item[1] for item in decoded) != size:
                continue
            samples.append({"entry": hex(start), "end": hex(start + size), "fileOffset": hex(offset),
                            "evidence": "ELF .dynsym STT_FUNC", "recordIndex": symbol_index,
                            "recordFileOffset": hex(table["sh_offset"] + symbol_index * table["sh_entsize"]),
                            "name": symbol.name, "bytes": raw.hex(),
                            "instructions": [{"address": hex(a), "mnemonic": m, "operands": o} for a, _, m, o in decoded]})
    return samples


def collect_x64(path):
    image = pefile.PE(str(path), fast_load=True)
    directory = image.OPTIONAL_HEADER.DATA_DIRECTORY[3]
    raw_records = image.get_data(directory.VirtualAddress, directory.Size)
    decoder = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    samples = []
    image.parse_data_directories(directories=[0])
    for symbol in image.DIRECTORY_ENTRY_EXPORT.symbols:
        if symbol.name is None or symbol.forwarder is not None:
            continue
        address = image.OPTIONAL_HEADER.ImageBase + symbol.address
        decoded = []
        for instruction in decoder.disasm_lite(image.get_data(symbol.address, 80), address):
            decoded.append(instruction)
            if instruction[2] in {"ret", "jmp", "int3"}:
                break
        if not decoded or decoded[-1][2] not in {"ret", "jmp"}:
            continue
        size = sum(item[1] for item in decoded)
        samples.append({"entry": hex(address), "end": hex(address + size),
                        "fileOffset": hex(image.get_offset_from_rva(symbol.address)), "evidence": "PE named export",
                        "name": symbol.name.decode("ascii"), "ordinal": symbol.ordinal,
                        "rangeLimit": "linear prefix to first ret/jmp; not a complete CFG claim",
                        "bytes": image.get_data(symbol.address, size).hex(),
                        "instructions": [{"address": hex(a), "mnemonic": m, "operands": o} for a, _, m, o in decoded]})
    for index, (start, end, unwind) in enumerate(struct.iter_unpack("<III", raw_records)):
        if not 1 <= end - start <= 48:
            continue
        raw = image.get_data(start, end - start)
        address = image.OPTIONAL_HEADER.ImageBase + start
        decoded = list(decoder.disasm_lite(raw, address))
        if sum(item[1] for item in decoded) != len(raw):
            continue
        mnemonics = {item[2] for item in decoded}
        if "ret" not in mnemonics:
            continue
        samples.append({"entry": hex(address), "end": hex(image.OPTIONAL_HEADER.ImageBase + end),
                        "fileOffset": hex(image.get_offset_from_rva(start)), "evidence": "PE .pdata BeginAddress/EndAddress",
                        "recordIndex": index, "unwindRva": hex(unwind), "bytes": raw.hex(),
                        "instructions": [{"address": hex(a), "mnemonic": m, "operands": o} for a, _, m, o in decoded]})
    return samples


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("arm", type=Path)
    parser.add_argument("x64", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = {}
    for name, path, collect in [("arm64", args.arm, collect_arm), ("x64", args.x64, collect_x64)]:
        with path.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest().upper()
        result[name] = {"sha256": digest, "samples": collect(path)}
    result["limits"] = "Entry records and independent disassembly only. Not a logical signature, full CFG, NIR or execution proof."
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({name: len(result[name]["samples"]) for name in ["arm64", "x64"]}))


if __name__ == "__main__":
    main()
