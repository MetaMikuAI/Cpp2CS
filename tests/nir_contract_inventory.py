"""独立核对 IL2CPP 元数据与二进制注册表，输出有证据的入口和签名清单。"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import struct

import pefile
from elftools.elf.elffile import ELFFile

from nir_il2cpp_types import Types, GenericMethods
from nir_external_contracts import augment_external_contracts


FORMAT = "cpp2cs.nir-contract-inventory.v1"
METHOD_INFO_SOURCE = "https://unity.com/blog/engine-platform/il2cpp-internals-method-calls"
SCALAR_WIDTHS = {2: 8, 3: 16, 4: 8, 5: 8, 6: 16, 7: 16, 8: 32, 9: 32,
                 10: 64, 11: 64, 24: 64, 25: 64}
POINTER_TYPES = {14, 15, 16, 18, 20, 27, 28, 29}


def identity(path):
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest().upper()
    return {"path": str(path.resolve()), "sha256": digest}


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def leb(data, offset, signed=False):
    value, shift = 0, 0
    while True:
        byte = data[offset]
        offset += 1
        value |= (byte & 127) << shift
        shift += 7
        if not byte & 128:
            return (value - (1 << shift) if signed and byte & 64 else value), offset


def cie_pointer_encoding(data, offset):
    length, cie_id = struct.unpack_from("<II", data, offset)
    assert cie_id == 0 and data[offset + 8] in (1, 3)
    version = data[offset + 8]
    augmentation_end = data.index(0, offset + 9, offset + 4 + length)
    augmentation = data[offset + 9:augmentation_end].decode("ascii")
    assert augmentation.startswith("z")
    _, cursor = leb(data, augmentation_end + 1)
    _, cursor = leb(data, cursor, True)
    if version == 1:
        cursor += 1
    else:
        _, cursor = leb(data, cursor)
    augmentation_size, cursor = leb(data, cursor)
    augmentation_limit = cursor + augmentation_size
    pointer_encoding = 0
    for kind in augmentation[1:]:
        if kind == "R":
            pointer_encoding = data[cursor]
            cursor += 1
        elif kind == "L":
            cursor += 1
        elif kind == "P":
            encoding = data[cursor]
            cursor += 1
            width = {0: 8, 2: 2, 3: 4, 4: 8, 10: 2, 11: 4, 12: 8}.get(encoding & 15)
            assert width is not None
            cursor += width
        else:
            assert kind == "S", f"unsupported CIE augmentation {kind}"
    assert cursor == augmentation_limit
    return pointer_encoding


class Metadata:
    def __init__(self, path):
        self.identity = identity(path)
        self.data = path.read_bytes()
        magic, self.version = struct.unpack_from("<II", self.data)
        assert magic == 0xFAB11BAF, "metadata magic is not standard IL2CPP"
        assert self.version in (29, 31), f"unsupported metadata version {self.version}"
        self.string_offset, self.string_size = struct.unpack_from("<II", self.data, 24)
        self.method_offset, self.methods = self.table(48, "<7i4H" if self.version == 31 else "<6i4H")
        self.parameter_offset, self.parameters = self.table(88, "<Iii")
        self.field_offset, self.fields = self.table(96, "<Iii")
        self.generic_parameter_offset, self.generic_parameters = self.table(104, "<iIhhHH")
        self.generic_container_offset, self.generic_containers = self.table(120, "<iiii")
        self.type_offset, self.types = self.table(160, "<16i8HII")
        self.image_offset, self.images = self.table(168, "<10i")
        self.method_images = [-1] * len(self.methods)
        self.image_methods = []
        for image_index, image in enumerate(self.images):
            assert image[3] == 0 or image[2] >= 0 and image[2] + image[3] <= len(self.types)
            indices = []
            for type_index in range(image[2], image[2] + image[3]):
                row = self.types[type_index]
                start, count = row[9], row[16]
                if count == 0:
                    continue
                assert 0 <= start <= len(self.methods) and start + count <= len(self.methods)
                for method_index in range(start, start + count):
                    assert self.methods[method_index][1] == type_index
                    assert self.method_images[method_index] == -1
                    self.method_images[method_index] = image_index
                    indices.append(method_index)
            tokens = [self.method_parts(self.methods[i])[2] & 0xFFFFFF for i in indices]
            assert len(set(tokens)) == len(tokens)
            self.image_methods.append(indices)
        assert -1 not in self.method_images

    def table(self, header_offset, layout):
        offset, size = struct.unpack_from("<II", self.data, header_offset)
        item_size = struct.calcsize(layout)
        assert offset + size <= len(self.data) and size % item_size == 0
        return offset, list(struct.iter_unpack(layout, self.data[offset:offset + size]))

    def string(self, index):
        assert 0 <= index < self.string_size
        start = self.string_offset + index
        end = self.data.index(0, start, self.string_offset + self.string_size)
        return self.data[start:end].decode("utf-8")

    def method_parts(self, row):
        shift = int(self.version == 31)
        return row[3 + shift], row[4 + shift], row[5 + shift], row[6 + shift], row[9 + shift]


class Binary:
    def __init__(self, path):
        self.identity = identity(path)
        self.data = bytearray(path.read_bytes())
        self.ranges = []
        self.virtual_ranges = []
        self.sections = {}
        self.entries = {}
        self.relocation_count = 0
        with path.open("rb") as stream:
            if self.data[:4] == b"\x7fELF":
                self.architecture = "Arm64"
                elf = ELFFile(stream)
                assert elf["e_machine"] == "EM_AARCH64" and elf.elfclass == 64
                for segment in elf.iter_segments():
                    if segment["p_type"] == "PT_LOAD":
                        self.ranges.append((segment["p_vaddr"], segment["p_offset"], segment["p_filesz"], bool(segment["p_flags"] & 1)))
                        self.virtual_ranges.append((segment["p_vaddr"], segment["p_memsz"]))
                for section in elf.iter_sections():
                    self.sections[section.name] = (section["sh_addr"], section["sh_offset"], section["sh_size"])
                    if section["sh_type"] == "SHT_RELA":
                        assert section["sh_entsize"] == 24
                        for target, info, addend in struct.iter_unpack("<QQq", section.data()):
                            if info & 0xFFFFFFFF == 1027:
                                offset = self.offset(target, 8)
                                assert offset is not None
                                struct.pack_into("<Q", self.data, offset, addend & 0xFFFFFFFFFFFFFFFF)
                                self.relocation_count += 1
                    if section["sh_type"] in ("SHT_DYNSYM", "SHT_SYMTAB"):
                        for index, symbol in enumerate(section.iter_symbols()):
                            start, size = symbol["st_value"], symbol["st_size"]
                            if symbol["st_info"]["type"] == "STT_FUNC" and self.executable(start):
                                self.add(start, {"kind": "elf.symbol", "section": section.name,
                                                "recordFileOffset": hex(section["sh_offset"] + index * section["sh_entsize"]),
                                                "name": symbol.name}, start + size if size else None)
                self.elf_unwind()
            else:
                self.architecture = "X64"
                pe = pefile.PE(data=bytes(self.data), fast_load=True)
                assert pe.FILE_HEADER.Machine == 0x8664
                base = pe.OPTIONAL_HEADER.ImageBase
                for section in pe.sections:
                    self.ranges.append((base + section.VirtualAddress, section.PointerToRawData,
                                        section.SizeOfRawData, bool(section.Characteristics & 0x20000000)))
                    self.virtual_ranges.append((base + section.VirtualAddress, max(section.Misc_VirtualSize, section.SizeOfRawData)))
                directory = pe.OPTIONAL_HEADER.DATA_DIRECTORY[3]
                offset = pe.get_offset_from_rva(directory.VirtualAddress)
                for index, (start, end, unwind) in enumerate(struct.iter_unpack("<III", pe.get_data(directory.VirtualAddress, directory.Size))):
                    assert start < end and self.executable(base + start)
                    self.add(base + start, {"kind": "pe.pdata", "recordFileOffset": hex(offset + index * 12),
                                           "unwindRva": hex(unwind)}, base + end)
                pe.parse_data_directories(directories=[0])
                if hasattr(pe, "DIRECTORY_ENTRY_EXPORT"):
                    for symbol in pe.DIRECTORY_ENTRY_EXPORT.symbols:
                        if symbol.forwarder is None and self.executable(base + symbol.address):
                            self.add(base + symbol.address, {"kind": "pe.export", "ordinal": symbol.ordinal,
                                                            "name": symbol.name.decode("utf-8") if symbol.name else None})

    def offset(self, address, size=1):
        for start, offset, length, _ in self.ranges:
            if start <= address and address + size <= start + length:
                return offset + address - start
        return None

    def address(self, offset):
        for start, file_offset, length, _ in self.ranges:
            if file_offset <= offset < file_offset + length:
                return start + offset - file_offset
        return None

    def executable(self, address):
        return any(executable and start <= address < start + size for start, _, size, executable in self.ranges)

    def words(self, address, count):
        offset = self.offset(address, count * 8)
        if offset is not None:
            return struct.unpack_from(f"<{count}Q", self.data, offset)
        if any(start <= address and address + count * 8 <= start + length for start, length in self.virtual_ranges):
            if not any(start <= address < start + length for start, _, length, _ in self.ranges):
                return (0,) * count
        return None

    def file_location(self, address):
        offset = self.offset(address)
        return hex(offset) if offset is not None else None

    def add(self, address, evidence, end=None):
        assert self.executable(address), f"entry outside executable image: {address:x}"
        entry = self.entries.setdefault(address, {"entry": hex(address), "evidence": [], "methodDefinitions": [],
                                                  "signatureStatus": "unknown", "signatureEvidence": [],
                                                  "signatureSynthetic": False, "contract": None, "gaps": []})
        entry["evidence"].append(evidence)
        if end is not None:
            entry.setdefault("ranges", []).append({"end": hex(end), "kind": evidence["kind"]})
            entry["end"] = hex(max(end, int(entry.get("end", "0"), 16)))
        return entry

    def matches(self, pattern):
        offset = self.data.find(pattern)
        while offset >= 0:
            yield offset
            offset = self.data.find(pattern, offset + 1)

    def references(self, targets):
        result = defaultdict(list)
        for start, offset, size, executable in self.ranges:
            if executable:
                continue
            aligned = (offset + 7) & ~7
            for index, (value,) in enumerate(struct.iter_unpack("<Q", self.data[aligned:offset + size - (offset + size - aligned) % 8])):
                if value in targets:
                    result[value].append(start + aligned - offset + index * 8)
        return result

    def elf_unwind(self):
        section = self.sections.get(".eh_frame_hdr")
        if section is None:
            return
        address, offset, size = section
        version, frame_encoding, count_encoding, table_encoding = self.data[offset:offset + 4]
        assert (version, frame_encoding, count_encoding, table_encoding) == (1, 0x1B, 3, 0x3B), "unsupported ELF unwind header encoding"
        count = struct.unpack_from("<I", self.data, offset + 8)[0]
        assert 12 + count * 8 <= size
        assert all(value == 0 for value in self.data[offset + 12 + count * 8:offset + size])
        cies = {}
        for index, (initial, fde_relative) in enumerate(struct.iter_unpack("<ii", self.data[offset + 12:offset + 12 + count * 8])):
            start, fde = address + initial, address + fde_relative
            fde_offset = self.offset(fde, 16)
            assert fde_offset is not None and self.executable(start)
            length, cie_delta, initial_relative, address_range = struct.unpack_from("<IIiI", self.data, fde_offset)
            assert length >= 12 and fde + 8 + initial_relative == start
            cie = fde + 4 - cie_delta
            cie_offset = self.offset(cie, 8)
            assert cie_offset is not None and struct.unpack_from("<I", self.data, cie_offset + 4)[0] == 0
            if cie not in cies:
                cies[cie] = cie_pointer_encoding(self.data, cie_offset)
            assert cies[cie] == 0x1B, "unsupported FDE pointer encoding"
            assert address_range == 0 or self.executable(start + address_range - 1)
            self.add(start, {"kind": "elf.eh_frame_hdr", "recordFileOffset": hex(offset + 12 + index * 8),
                             "fdeFileOffset": hex(fde_offset), "cieAddress": hex(cie), "addressRange": address_range},
                     start + address_range if address_range else None)


def find_modules(binary, metadata):
    string_addresses = defaultdict(list)
    for image_index, image in enumerate(metadata.images):
        name = metadata.string(image[0])
        for offset in binary.matches(name.encode() + b"\0"):
            address = binary.address(offset)
            if address is not None:
                string_addresses[address].append(image_index)
    references = binary.references(string_addresses)
    candidates = defaultdict(list)
    for string_address, indices in string_addresses.items():
        for address in references[string_address]:
            words = binary.words(address, 3)
            if words is None:
                continue
            _, count, pointers = words
            for image_index in indices:
                method_indices = metadata.image_methods[image_index]
                max_token = max((metadata.method_parts(metadata.methods[i])[2] & 0xFFFFFF for i in method_indices), default=0)
                if count != max_token:
                    continue
                methods = binary.words(pointers, count) if count else ()
                if methods is None or any(value and not binary.executable(value) for value in methods):
                    continue
                candidates[image_index].append({"address": address, "count": count, "pointers": pointers,
                                                "methods": methods, "name": metadata.string(metadata.images[image_index][0])})
    result = {}
    for index in range(len(metadata.images)):
        matches = candidates[index]
        assert len(matches) == 1, f"expected one codegen module for {metadata.string(metadata.images[index][0])}, got {len(matches)}"
        result[index] = matches[0]
    return result


def find_metadata_registration(binary, metadata):
    count = len(metadata.types)
    matches = []
    for offset in binary.matches(struct.pack("<Q", count)):
        if offset < 80 or offset + 48 > len(binary.data) or offset % 8:
            continue
        if struct.unpack_from("<Q", binary.data, offset + 16)[0] != count:
            continue
        address = binary.address(offset - 80)
        if address is None:
            continue
        words = binary.words(address, 16)
        type_count, type_table = words[6:8]
        if not 0 < type_count < 10_000_000:
            continue
        pointers = binary.words(type_table, type_count)
        if pointers is None or any(binary.offset(pointer, 12) is None for pointer in pointers):
            continue
        valid = True
        for type_index, row in enumerate(metadata.types):
            byval = row[2]
            if not 0 <= byval < type_count:
                valid = False
                break
            data, bits = struct.unpack_from("<QI", binary.data, binary.offset(pointers[byval], 12))
            if data != type_index or ((bits >> 16) & 255) not in set(range(1, 15)) | {17, 18, 22, 24, 25, 28}:
                valid = False
                break
        if valid:
            matches.append((address, words, pointers))
    assert len(matches) == 1, f"expected one metadata registration, got {len(matches)}"
    return matches[0]


def find_code_registration(binary, modules, metadata_registration):
    count = len(modules)
    expected = {module["address"] for module in modules.values()}
    matches = []
    generic_spec_count = metadata_registration[1][8]
    generic_count, generic_table = metadata_registration[1][4:6]
    generic_offset = binary.offset(generic_table, generic_count * 16)
    assert generic_offset is not None
    generic_rows = struct.iter_unpack("<iiii", binary.data[generic_offset:generic_offset + generic_count * 16])
    expected_pointer_count = max(row[1] for row in generic_rows) + 1
    for offset in binary.matches(struct.pack("<Q", count)):
        if offset % 8 or offset + 16 > len(binary.data):
            continue
        table = struct.unpack_from("<Q", binary.data, offset + 8)[0]
        pointers = binary.words(table, count)
        if pointers is None or set(pointers) != expected:
            continue
        for prefix in (104, 120):
            address = binary.address(offset - prefix)
            if address is None:
                continue
            words = binary.words(address, (prefix + 16) // 8)
            generic_count, generic_table = words[2:4]
            if not 0 < generic_count <= generic_spec_count or generic_count != expected_pointer_count:
                continue
            generic_pointers = binary.words(generic_table, generic_count)
            if generic_pointers is None or any(p and not binary.executable(p) for p in generic_pointers):
                continue
            matches.append((address, words, generic_pointers, prefix))
    assert len(matches) == 1, f"expected one code registration, got {len(matches)}"
    return matches[0]


def make_method(metadata, binary, types, module, index, accept_method_info, instance=None):
    row = metadata.methods[index]
    parameter_start, generic_container, token, flags, parameter_count = metadata.method_parts(row)
    type_definition = metadata.types[row[1]]
    pointer_index = (token & 0xFFFFFF) - 1
    assert token >> 24 == 6 and 0 <= pointer_index < module["count"]
    address = module["methods"][pointer_index]
    if instance is not None:
        address = instance["address"]
    record_offset = metadata.method_offset + index * (36 if metadata.version == 31 else 32)
    name = f"{module['name']}::{metadata.string(type_definition[1])}.{metadata.string(type_definition[0])}::{metadata.string(row[0])}#{token:08x}"
    evidence = [{"kind": "metadata.method", "methodDefinition": index, "recordFileOffset": hex(record_offset),
                 "token": hex(token), "flags": flags, "parameterStart": parameter_start, "parameterCount": parameter_count,
                 "metadataSha256": metadata.identity["sha256"]},
                {"kind": "il2cpp.module-method-pointer", "moduleAddress": hex(module["address"]),
                 "recordFileOffset": binary.file_location(module["pointers"] + pointer_index * 8),
                 "recordAddress": hex(module["pointers"] + pointer_index * 8), "pointerIndex": pointer_index,
                 "binarySha256": binary.identity["sha256"]}]
    if instance is not None:
        evidence[1:2] = instance["evidence"]
    gaps = []
    if instance is not None and instance["fullySharedMarkers"]:
        gaps.append("registered fully-shared generic context requires a separately proven native prototype")
    if instance is None and (generic_container >= 0 or type_definition[6] >= 0):
        gaps.append("generic definition requires concrete instantiation and sharing evidence")
    context = instance["context"] if instance is not None else ((), ())
    result, result_evidence, gap = types.scalar(row[2], context)
    evidence.extend(result_evidence)
    if gap:
        gaps.append(gap)
    arguments = []
    if flags & 0x10 == 0:
        arguments.append({"width": 64, "kind": "Address"})
        evidence.append({"kind": "il2cpp.instance-this", "typeDefinition": row[1], "valueType": bool(type_definition[24] & 1)})
    for parameter_index in range(parameter_start, parameter_start + parameter_count):
        assert 0 <= parameter_index < len(metadata.parameters)
        parameter = metadata.parameters[parameter_index]
        scalar, parameter_evidence, gap = types.scalar(parameter[2], context)
        evidence.append({"kind": "metadata.parameter", "parameterDefinition": parameter_index,
                         "recordFileOffset": hex(metadata.parameter_offset + parameter_index * 12)})
        evidence.extend(parameter_evidence)
        if gap or scalar is None:
            gaps.append(gap or "void parameter is not a callable scalar")
        else:
            arguments.append(scalar)
    if accept_method_info:
        arguments.append({"width": 64, "kind": "Address"})
        evidence.append({"kind": "adopted-il2cpp-generated-method-prototype", "source": METHOD_INFO_SOURCE,
                         "role": "trailing MethodInfo pointer", "scope": "registered generated method, conditional native prototype",
                         "assumption": "registered codegen method follows standard IL2CPP generated free-function prototype"})
    else:
        gaps.append("native hidden MethodInfo parameter convention has not been explicitly adopted")
    signature = {"arguments": arguments, "result": result} if not gaps else None
    contract = None
    if address and signature is not None:
        contract = {"name": f"method_{address:x}", "entryAddress": address, "signature": signature,
                    "abi": "Aapcs64" if binary.architecture == "Arm64" else "WindowsX64",
                    "effects": {"readsMemory": True, "writesMemory": True, "externalEffects": True, "mayThrow": True,
                                "mayReturn": True, "mayDiverge": True, "mayTerminate": True},
                    "assumptions": ["Metadata and binary registration tables are structurally cross-validated.",
                                    "Standard IL2CPP generated-method prototype including explicit trailing MethodInfo is adopted.",
                                    "Analysis domain is conditional; no claim that every execution is normal or sequential."],
                    "domain": {"normalExecution": True, "validPrivateFrame": True, "stableThreadEnvironment": True, "sequentialMemory": True}}
    record = {"methodDefinition": index, "name": name, "entry": hex(address) if address else None,
            "token": hex(token), "signature": signature, "signatureEvidence": evidence, "gaps": gaps,
            "contract": contract, "signatureStatus": "unsupported" if gaps else "known"}
    if instance is not None:
        record["genericInstance"] = {key: value for key, value in instance.items() if key not in ("context", "evidence", "address")}
    return record


def merge_method(binary, method):
    if method["entry"] is None:
        return
    address = int(method["entry"], 16)
    generic = method.get("genericInstance")
    pointer_kind = "il2cpp.generic-method-pointer" if generic is not None else "il2cpp.module-method-pointer"
    pointer_evidence = next(item for item in method["signatureEvidence"] if item.get("kind") == pointer_kind)
    entry = binary.add(address, pointer_evidence)
    if method["methodDefinition"] not in entry["methodDefinitions"]:
        entry["methodDefinitions"].append(method["methodDefinition"])
    if generic is not None:
        entry.setdefault("genericMethodSpecs", []).append(generic)
    entry["signatureEvidence"].extend(method["signatureEvidence"])
    entry["gaps"].extend(method["gaps"])
    contract = method["contract"]
    if contract is not None:
        if entry["contract"] is not None and entry["contract"]["signature"] != contract["signature"]:
            entry["signatureStatus"] = "conflict"
            entry["gaps"].append("multiple metadata definitions or instantiations assign incompatible signatures to one native entry")
        elif entry["signatureStatus"] != "conflict":
            entry["contract"] = contract
            entry["signatureStatus"] = "known"
    else:
        if entry["signatureStatus"] == "unknown":
            entry["signatureStatus"] = "unsupported"
        entry["unresolvedSignatureAliases"] = True


def add_registration_entries(binary, modules, registration, code_registration):
    _, words, _, prefix = code_registration
    tables = [("reverse-pinvoke", words[0], words[1]), ("invoker", words[5], words[6]),
              ("unresolved-virtual-call", words[7], words[8])]
    if prefix == 120:
        tables.extend([("unresolved-instance-call", words[7], words[9]),
                       ("unresolved-static-call", words[7], words[10])])
    generic_count, generic_table = registration[1][4:6]
    generic_offset = binary.offset(generic_table, generic_count * 16)
    assert generic_offset is not None
    adjustor_count = max(row[3] for row in struct.iter_unpack("<iiii", binary.data[generic_offset:generic_offset + generic_count * 16])) + 1
    if adjustor_count:
        tables.append(("generic-adjustor-thunk", adjustor_count, words[4]))
    counts = {}
    for kind, count, table in tables:
        pointers = binary.words(table, count) if count else ()
        assert pointers is not None and all(not p or binary.executable(p) for p in pointers), kind
        counts[kind] = len(pointers)
        for index, address in enumerate(pointers):
            if address:
                entry = binary.add(address, {"kind": "il2cpp." + kind, "pointerIndex": index,
                                            "recordFileOffset": binary.file_location(table + index * 8)})
                entry["unresolvedSignatureAliases"] = True
                entry["gaps"].append("runtime adapter prototype is not resolved: " + kind)
    module_adjustors = 0
    for module in modules.values():
        module_words = binary.words(module["address"], 5)
        count, table = module_words[3:5]
        if not count:
            continue
        offset = binary.offset(table, count * 16)
        assert offset is not None
        for index, (token, _, address) in enumerate(struct.iter_unpack("<IIQ", binary.data[offset:offset + count * 16])):
            assert binary.executable(address) and token >> 24 == 6
            entry = binary.add(address, {"kind": "il2cpp.module-adjustor-thunk", "moduleAddress": hex(module["address"]),
                                        "token": hex(token), "recordFileOffset": hex(offset + index * 16)})
            entry["unresolvedSignatureAliases"] = True
            entry["gaps"].append("value-type adjustor thunk prototype is not resolved")
        module_adjustors += count
    counts["module-adjustor-thunk"] = module_adjustors
    return counts


def inventory(binary_path, metadata_path, output, accept_method_info, reference_script=None):
    metadata = Metadata(metadata_path)
    binary = Binary(binary_path)
    print(json.dumps({"phase": "entry-records", "architecture": binary.architecture, "entries": len(binary.entries),
                      "methods": len(metadata.methods)}), flush=True)
    modules = find_modules(binary, metadata)
    registration = find_metadata_registration(binary, metadata)
    types = Types(binary, metadata, registration)
    code_registration = find_code_registration(binary, modules, registration)
    generic_methods = GenericMethods(binary, metadata, registration, code_registration, types)
    registration_entry_counts = add_registration_entries(binary, modules, registration, code_registration)
    reference_check = None
    if reference_script is not None:
        reference = json.loads(reference_script.read_text(encoding="utf-8"))
        addresses = [method["Address"] for method in reference["ScriptMethod"]]
        registered = set(code_registration[2]) | {pointer for module in modules.values() for pointer in module["methods"] if pointer}
        reference_check = identity(reference_script) | {
            "scriptMethodCount": len(addresses), "uniqueAddresses": len(set(addresses)),
            "executableRecords": sum(binary.executable(address) for address in addresses),
            "independentlyRegisteredRecords": sum(address in registered for address in addresses),
            "role": "corroboration only; no imported names, signatures or entries"}
        del reference
    print(json.dumps({"phase": "registrations", "modules": len(modules), "metadataRegistration": hex(registration[0]),
                      "codeRegistration": hex(code_registration[0]), "types": len(registration[2]),
                      "genericMethodPointers": len(code_registration[2])}), flush=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    methods_path = output.with_suffix(".methods.jsonl")
    method_counts = Counter()
    with methods_path.open("w", encoding="utf-8") as stream:
        for index in range(len(metadata.methods)):
            module = modules[metadata.method_images[index]]
            method = make_method(metadata, binary, types, module, index, accept_method_info)
            method_counts[method["signatureStatus"]] += 1
            merge_method(binary, method)
            if method["entry"] is None:
                method_counts["noNativePointer"] += 1
            stream.write(json.dumps(method, ensure_ascii=False, separators=(",", ":")) + "\n")
    generics_path = output.with_suffix(".generic-methods.jsonl")
    generic_counts = Counter()
    represented_pointers = set()
    with generics_path.open("w", encoding="utf-8") as stream:
        for instance in generic_methods.records():
            index = instance["methodDefinition"]
            module = modules[metadata.method_images[index]]
            method = make_method(metadata, binary, types, module, index, accept_method_info, instance)
            generic_counts[method["signatureStatus"]] += 1
            generic_counts["fullySharedMarkerRecords"] += bool(instance["fullySharedMarkers"])
            if method["entry"] is None:
                generic_counts["noNativePointer"] += 1
            represented_pointers.add(instance["pointerIndex"])
            merge_method(binary, method)
            stream.write(json.dumps(method, ensure_ascii=False, separators=(",", ":")) + "\n")
    generic_table = code_registration[1][3]
    for index, address in enumerate(code_registration[2]):
        if address and index not in represented_pointers:
            entry = binary.add(address, {"kind": "il2cpp.generic-method-pointer", "pointerIndex": index,
                                         "recordFileOffset": hex(binary.offset(generic_table + index * 8))})
            entry["unresolvedSignatureAliases"] = True
            entry["gaps"].append("generic method pointer has no exact registered MethodSpec")
    external_counts = augment_external_contracts(binary)
    entries_path = output.with_suffix(".entries.jsonl")
    entry_counts = Counter()
    evidence_counts = Counter()
    with entries_path.open("w", encoding="utf-8") as stream:
        for address in sorted(binary.entries):
            entry = binary.entries[address]
            if entry["signatureStatus"] == "conflict":
                entry["contract"] = None
            elif entry.get("unresolvedSignatureAliases"):
                entry["signatureStatus"] = "unsupported"
                entry["contract"] = None
            if entry["signatureStatus"] == "unknown":
                entry["gaps"].append("entry evidence does not provide a logical function signature")
            entry["gaps"] = sorted(set(entry["gaps"]))
            entry_counts[entry["signatureStatus"]] += 1
            evidence_counts.update({item["kind"] for item in entry["evidence"]})
            stream.write(json.dumps(entry, ensure_ascii=False, separators=(",", ":")) + "\n")
    manifest = {"format": FORMAT, "binary": binary.identity | {"architecture": binary.architecture,
                                                               "relativeRelocationsApplied": binary.relocation_count},
                "metadata": metadata.identity | {"version": metadata.version, "methodCount": len(metadata.methods),
                                                   "typeDefinitionCount": len(metadata.types), "imageCount": len(metadata.images)},
                "provider": identity(Path(__file__)), "entriesFile": entries_path.name, "methodsFile": methods_path.name,
                "providerSources": [identity(Path(__file__).with_name(name)) for name in ("nir_il2cpp_types.py", "nir_external_contracts.py")],
                "genericMethodsFile": generics_path.name, "genericMethodsSha256": identity(generics_path)["sha256"],
                "entriesSha256": identity(entries_path)["sha256"], "methodsSha256": identity(methods_path)["sha256"],
                "entryCount": len(binary.entries), "summary": {"entries": dict(entry_counts), "methods": dict(method_counts),
                                                               "entryEvidence": dict(evidence_counts), "genericMethods": dict(generic_counts),
                                                               "externalContracts": external_counts},
                "registrations": {"metadata": hex(registration[0]), "code": hex(code_registration[0]),
                                  "types": len(registration[2]), "genericMethodPointers": len(code_registration[2]),
                                  "genericTables": dict(generic_methods.counts),
                                  "fullySharedTypeMarkers": list(types.shared_markers.values()),
                                  "otherEntryTables": registration_entry_counts,
                                  "codeGenModules": [{"name": m["name"], "address": hex(m["address"]), "methodCount": m["count"]} for m in modules.values()]},
                "adoptedNativePrototype": {"enabled": accept_method_info, "source": METHOD_INFO_SOURCE},
                "referenceScriptCheck": reference_check,
                "limits": ["All available entry records are inventoried; this is not proof that every machine function has a record.",
                           "Signature availability is separate from NIR recovery or runtime equivalence.",
                           "Effects are conservative, including MayThrow; analysis-domain conditions are explicit assumptions.",
                           "Generic contracts use exact registered MethodSpec records, with no inferred fallback specialization.",
                           "Fully-shared marker contexts and unresolved same-address aliases are rejected; ordinary generated prototypes are explicitly adopted.",
                           "Value-type layout requires registered size and every instance field; generic value layouts and padding remain gaps."]}
    write_json(output, manifest)
    print(json.dumps({"phase": "complete", "output": str(output), "entryCount": len(binary.entries), "summary": manifest["summary"]}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("metadata", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--adopt-standard-il2cpp-prototype", action="store_true",
                        help="显式采用标准 IL2CPP native 原型；隐藏 MethodInfo 作为逻辑参数保留")
    parser.add_argument("--reference-script", type=Path, help="只核对独立注册地址覆盖，不导入 Dumper 签名")
    args = parser.parse_args()
    inventory(args.binary, args.metadata, args.output, args.adopt_standard_il2cpp_prototype, args.reference_script)


if __name__ == "__main__":
    main()
