"""独立解码跳转字节，检查接口传播与保守拒绝。"""
import argparse
import json
from pathlib import Path
import struct

import capstone
import pefile
from elftools.elf.elffile import ELFFile

from nir_contract_inventory import Binary, identity
from nir_external_contracts import augment_external_contracts, pure_jump, standard_prototypes, DECLARATIONS


class Sample:
    offset = Binary.offset
    executable = Binary.executable
    add = Binary.add

    def __init__(self, architecture, data, base=0x1000):
        self.architecture, self.data = architecture, bytearray(data)
        self.ranges = [(base, 0, len(data), True)]
        self.entries = {}
        self.identity = {"sha256": "fixture"}


def seed(image, address, name=None):
    return image.add(address, {"kind": "pe.export" if name else "test.entry", "name": name})


def fixture_checks():
    count = 0
    for architecture in ("Arm64", "X64"):
        data = bytearray(0x80)
        if architecture == "Arm64":
            struct.pack_into("<I", data, 0, 0x14000008)
            struct.pack_into("<I", data, 0x10, 0x14000004)
            struct.pack_into("<I", data, 0x20, 0xD65F03C0)
            struct.pack_into("<I", data, 0x30, 0x94000004)
            struct.pack_into("<I", data, 0x40, 0x14000000)
            struct.pack_into("<I", data, 0x50, 0x17FFFFF4)
            struct.pack_into("<I", data, 0x60, 0x14000004)
            struct.pack_into("<I", data, 0x70, 0x17FFFFFC)
        else:
            data[:5] = b"\xe9" + struct.pack("<i", 0x1B)
            data[0x10:0x15] = b"\xe9" + struct.pack("<i", 0xB)
            data[0x20] = 0xC3
            data[0x30:0x35] = b"\xe8" + struct.pack("<i", 0xB)
            data[0x40:0x45] = b"\xe9" + struct.pack("<i", -5)
            data[0x50:0x55] = b"\xe9" + struct.pack("<i", -0x35)
            data[0x60:0x65] = b"\xe9" + struct.pack("<i", 0xB)
            data[0x70:0x75] = b"\xe9" + struct.pack("<i", -0x15)
        image = Sample(architecture, data)
        seed(image, 0x1000, "il2cpp_runtime_class_init")
        for address in (0x1010, 0x1030, 0x1040, 0x1050, 0x1060, 0x1070):
            seed(image, address)
        result = augment_external_contracts(image)
        assert result["addedContracts"] == 4
        for address in (0x1000, 0x1010, 0x1020, 0x1050):
            contract = image.entries[address]["contract"]
            assert contract["signature"] == {"arguments": [{"width": 64, "kind": "Address"}], "result": None}
            assert all(contract["effects"].values())
            count += 1
        for address in (0x1030, 0x1040, 0x1060, 0x1070):
            assert image.entries[address]["contract"] is None
            count += 1
        verify_alias_bytes(image)
        conflict = Sample(architecture, data)
        seed(conflict, 0x1000, "il2cpp_runtime_class_init")
        seed(conflict, 0x1010, "il2cpp_value_box")
        assert augment_external_contracts(conflict)["rejectedAliasGroups"] == 1
        assert all(entry["contract"] is not None for entry in conflict.entries.values())
        assert 0x1020 not in conflict.entries
        same_entry = Sample(architecture, data)
        seed(same_entry, 0x1000, "il2cpp_runtime_class_init")
        seed(same_entry, 0x1000, "il2cpp_value_box")
        assert augment_external_contracts(same_entry)["rejectedDirectExports"] == 1
        assert same_entry.entries[0x1000]["contract"] is None
        unresolved = Sample(architecture, data)
        seed(unresolved, 0x1000, "il2cpp_runtime_class_init")
        seed(unresolved, 0x1010)["unresolvedSignatureAliases"] = True
        assert augment_external_contracts(unresolved)["rejectedAliasGroups"] == 1
        assert unresolved.entries[0x1000]["contract"] is not None
        assert unresolved.entries[0x1010]["contract"] is None
        impostor = Sample(architecture, data)
        seed(impostor, 0x1000, "prefix_il2cpp_runtime_class_init_suffix")
        assert not augment_external_contracts(impostor).get("addedContracts")
        cyclic_export = Sample(architecture, data)
        seed(cyclic_export, 0x1060, "il2cpp_runtime_class_init")
        assert augment_external_contracts(cyclic_export)["cyclicExportAliases"] == 1
        assert cyclic_export.entries[0x1060]["contract"] is not None
        assert 0x1070 not in cyclic_export.entries
        count += 5
    return count


def verify_alias_bytes(image):
    decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM) if image.architecture == "Arm64" else capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    count = 0
    for entry in image.entries.values():
        for evidence in entry["signatureEvidence"]:
            if evidence.get("kind") != "machine.pure-jump-alias":
                continue
            address, target = int(evidence["address"], 16), int(evidence["target"], 16)
            raw = bytes.fromhex(evidence["bytes"])
            offset = int(evidence["recordFileOffset"], 16)
            assert bytes(image.data[offset:offset + len(raw)]) == raw
            decoded = list(decoder.disasm(raw, address))
            assert len(decoded) == 1 and decoded[0].size == len(raw)
            assert decoded[0].mnemonic == ("b" if image.architecture == "Arm64" else "jmp")
            assert int(decoded[0].op_str.lstrip("#"), 16) == target
            count += 1
    return count


def check_inventory(path):
    manifest = json.loads(path.read_text(encoding="utf-8"))
    binary_path = Path(manifest["binary"]["path"])
    image = Sample(manifest["binary"]["architecture"], binary_path.read_bytes(), 0)
    image.identity = identity(binary_path)
    assert image.identity["sha256"] == manifest["binary"]["sha256"]
    if image.architecture == "Arm64":
        with binary_path.open("rb") as stream:
            elf = ELFFile(stream)
            image.ranges = [(segment["p_vaddr"], segment["p_offset"], segment["p_filesz"], bool(segment["p_flags"] & 1))
                            for segment in elf.iter_segments() if segment["p_type"] == "PT_LOAD"]
            actual_exports = {(symbol["st_value"], symbol.name) for section in elf.iter_sections()
                              if section["sh_type"] in ("SHT_DYNSYM", "SHT_SYMTAB") for symbol in section.iter_symbols()
                              if symbol["st_info"]["type"] == "STT_FUNC"}
    else:
        pe = pefile.PE(data=bytes(image.data), fast_load=True)
        image.ranges = [(pe.OPTIONAL_HEADER.ImageBase + section.VirtualAddress, section.PointerToRawData,
                         section.SizeOfRawData, bool(section.Characteristics & 0x20000000)) for section in pe.sections]
        pe.parse_data_directories(directories=[0])
        actual_exports = {(pe.OPTIONAL_HEADER.ImageBase + symbol.address, symbol.name.decode("utf-8"))
                          for symbol in pe.DIRECTORY_ENTRY_EXPORT.symbols if symbol.name and symbol.forwarder is None}
    entries_path = path.parent / manifest["entriesFile"]
    targets = set()
    prototypes = standard_prototypes()
    with entries_path.open(encoding="utf-8") as stream:
        for line in stream:
            entry = json.loads(line)
            address = int(entry["entry"], 16)
            jump = pure_jump(image, address)
            if jump is not None or any(e.get("name") in prototypes for e in entry["evidence"]):
                image.entries[address] = entry
                if jump is not None:
                    targets.add(jump[0])
    with entries_path.open(encoding="utf-8") as stream:
        for line in stream:
            entry = json.loads(line)
            address = int(entry["entry"], 16)
            if address in targets and address not in image.entries:
                image.entries[address] = entry
    prior = {address for address, entry in image.entries.items() if entry["contract"] is not None}
    counts = augment_external_contracts(image)
    counts["independentJumpDecodes"] = verify_alias_bytes(image)
    for entry in image.entries.values():
        for evidence in entry["signatureEvidence"]:
            if evidence.get("kind") == "adopted-standard-export-prototype":
                assert (int(evidence["exportAddress"], 16), evidence["name"]) in actual_exports
    additions = {hex(address): entry["contract"] for address, entry in image.entries.items()
                 if entry["contract"] is not None and address not in prior}
    assert all(all(contract["effects"].values()) for contract in additions.values())
    return {"inventory": str(path), "counts": counts, "addedContracts": additions}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventories", type=Path, nargs="*")
    parser.add_argument("--header", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.header is not None:
        lines = set(args.header.read_text(encoding="utf-8").splitlines())
        assert all(declaration in lines for declaration in DECLARATIONS.strip().splitlines())
    results = {"fixtureChecks": fixture_checks(), "inventories": [check_inventory(path) for path in args.inventories]}
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"fixtureChecks": results["fixtureChecks"], "inventories": [
        {"inventory": result["inventory"], "counts": result["counts"]} for result in results["inventories"]]}))


if __name__ == "__main__":
    main()
