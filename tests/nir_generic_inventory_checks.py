"""不导入库存生成器，从原始字节复核泛型实参链、共享边界和聚合字段。"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import struct

import pefile
from elftools.elf.elffile import ELFFile


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest().upper()


class RawProof:
    def __init__(self, manifest):
        path = Path(manifest["binary"]["path"])
        assert digest(path) == manifest["binary"]["sha256"]
        self.binary = path.read_bytes()
        self.ranges, self.relocations = [], {}
        if self.binary[:4] == b"\x7fELF":
            with path.open("rb") as stream:
                image = ELFFile(stream)
                for segment in image.iter_segments():
                    if segment["p_type"] == "PT_LOAD":
                        self.ranges.append((segment["p_vaddr"], segment["p_offset"], segment["p_filesz"]))
                for section in image.iter_sections():
                    if section["sh_type"] == "SHT_RELA":
                        for row in section.iter_relocations():
                            if row["r_info_type"] == 1027:
                                self.relocations[self.offset(row["r_offset"])] = row["r_addend"] & ((1 << 64) - 1)
        else:
            image = pefile.PE(data=self.binary, fast_load=True)
            self.ranges = [(image.OPTIONAL_HEADER.ImageBase + section.VirtualAddress,
                            section.PointerToRawData, section.SizeOfRawData) for section in image.sections]
        path = Path(manifest["metadata"]["path"])
        assert digest(path) == manifest["metadata"]["sha256"]
        self.metadata = path.read_bytes()
        self.version = struct.unpack_from("<I", self.metadata, 4)[0]
        self.tables = {key: struct.unpack_from("<II", self.metadata, key) for key in (24, 48, 88, 96, 104, 120, 160)}
        registration = self.offset(int(manifest["registrations"]["metadata"], 16))
        self.registration = tuple(self.pointer(registration + i * 8) for i in range(16))
        self.types = self.offset(self.registration[7])
        self.specs = self.offset(self.registration[9])
        self.methods = self.offset(self.registration[5])
        self.insts = self.offset(self.registration[3])
        code = self.offset(int(manifest["registrations"]["code"], 16))
        self.generic_pointers = self.offset(self.pointer(code + 24))
        self.counts = Counter()
        self.value_checks = set()
        self.marker_checks = {}
        self.entry_signatures = {}
        self.entry_gaps = set()
        self.entry_conflicts = set()
        self.marker_indices = {item["typeDefinition"] for item in manifest["registrations"]["fullySharedTypeMarkers"]}
        expected_markers = {index for index in range(self.tables[160][1] // 88)
                            for definition in [self.type_definition(index)]
                            if self.string(definition[1]) == "Unity.IL2CPP.Metadata"
                            and self.string(definition[0]) in ("__Il2CppFullySharedGenericType", "__Il2CppFullySharedGenericStructType")}
        assert self.marker_indices == expected_markers
        for item in manifest["registrations"]["fullySharedTypeMarkers"]:
            definition = self.type_definition(item["typeDefinition"])
            assert self.string(definition[1]) + "." + self.string(definition[0]) == item["name"]
            assert definition[18] == item["fieldCount"] == 0 and definition[24] == item["bitfield"]
            raw = self.offset(self.pointer(self.types + definition[2] * 8))
            assert (struct.unpack_from("<I", self.binary, raw + 8)[0] >> 16) & 255 == 17
            size_table = self.offset(self.registration[13])
            size = self.offset(self.pointer(size_table + item["typeDefinition"] * 8))
            assert size == int(item["sizeRecordFileOffset"], 16)
            assert struct.unpack_from("<Ii", self.binary, size) == (item["instanceSize"], item["nativeSize"])
            assert item["nativeSize"] == -1

    def offset(self, address):
        matches = [file + address - start for start, file, size in self.ranges if start <= address < start + size]
        assert len(matches) == 1, hex(address)
        return matches[0]

    def pointer(self, offset):
        return self.relocations.get(offset, struct.unpack_from("<Q", self.binary, offset)[0])

    def string(self, index):
        start = self.tables[24][0] + index
        return self.metadata[start:self.metadata.index(0, start)].decode("utf-8")

    def type_definition(self, index):
        assert 0 <= index < self.tables[160][1] // 88
        return struct.unpack_from("<16i8HII", self.metadata, self.tables[160][0] + index * 88)

    def context(self, index):
        if index < 0:
            assert index == -1
            return ()
        assert index < self.registration[2]
        inst = self.offset(self.pointer(self.insts + index * 8))
        count = self.pointer(inst)
        argv = self.offset(self.pointer(inst + 8))
        return tuple(self.pointer(argv + i * 8) for i in range(count))

    def markers(self, pointer):
        if pointer in self.marker_checks:
            return self.marker_checks[pointer]
        offset = self.offset(pointer)
        data = self.pointer(offset)
        kind = (struct.unpack_from("<I", self.binary, offset + 8)[0] >> 16) & 255
        result = set()
        if kind in (17, 18) and data in self.marker_indices:
            result.add(data)
        elif kind in (15, 16, 29):
            result.update(self.markers(data))
        elif kind == 20:
            result.update(self.markers(self.pointer(self.offset(data))))
        elif kind == 21:
            generic = self.offset(data)
            for member in (8, 16):
                inst_pointer = self.pointer(generic + member)
                if not inst_pointer:
                    continue
                inst = self.offset(inst_pointer)
                argc, argv = self.pointer(inst), self.offset(self.pointer(inst + 8))
                for index in range(argc):
                    result.update(self.markers(self.pointer(argv + index * 8)))
        self.marker_checks[pointer] = tuple(sorted(result))
        return self.marker_checks[pointer]

    def check_type(self, value, pointer, contexts):
        cache_key = json.dumps(value, sort_keys=True), pointer, contexts
        if cache_key in self.value_checks:
            return
        self.value_checks.add(cache_key)
        raw = self.offset(pointer)
        data = self.pointer(raw)
        bits = struct.unpack_from("<I", self.binary, raw + 8)[0]
        kind = (bits >> 16) & 255
        if bits & (1 << 29) or kind in (14, 15, 16, 18, 20, 27, 28, 29):
            assert value == {"width": 64, "kind": "Address"}
            return
        if kind == 1:
            assert value is None
            return
        widths = {2: 8, 3: 16, 4: 8, 5: 8, 6: 16, 7: 16, 8: 32, 9: 32, 10: 64, 11: 64, 24: 64, 25: 64}
        if kind in widths or kind in (12, 13):
            assert value == {"width": widths.get(kind, 32 if kind == 12 else 64),
                             "kind": "Float" if kind in (12, 13) else "Integer"}
            return
        if kind in (19, 30):
            owner, _, _, _, ordinal, _ = struct.unpack_from("<iIhhHH", self.metadata, self.tables[104][0] + data * 16)
            container = struct.unpack_from("<iiii", self.metadata, self.tables[120][0] + owner * 16)
            assert bool(container[2]) == (kind == 30) and container[3] + ordinal == data
            self.counts["genericParameterSubstitutions"] += 1
            self.check_type(value, contexts[int(kind == 30)][ordinal], contexts)
            return
        if kind == 21:
            generic = self.offset(data)
            definition = self.offset(self.pointer(generic))
            assert (struct.unpack_from("<I", self.binary, definition + 8)[0] >> 16) & 255 == 18
            assert value == {"width": 64, "kind": "Address"}
            return
        assert kind == 17 and data not in self.marker_indices
        definition = self.type_definition(data)
        if definition[24] & 2:
            field = self.tables[96][0] + definition[8] * 12
            name, underlying, _ = struct.unpack_from("<Iii", self.metadata, field)
            assert self.string(name) == "value__"
            self.check_type(value, self.pointer(self.types + underlying * 8), contexts)
            self.counts["enumLayouts"] += 1
            return
        assert value["kind"] == "Aggregate" and definition[24] & 1 and definition[6] < 0
        sizes = self.offset(self.registration[13])
        size_record = self.offset(self.pointer(sizes + data * 8))
        size = struct.unpack_from("<I", self.binary, size_record)[0] - 16
        assert value["width"] == size * 8
        offsets = self.offset(self.registration[11])
        offset_record = self.offset(self.pointer(offsets + data * 8))
        instance_fields = []
        alignments = []
        for local in range(definition[18]):
            field = self.tables[96][0] + (definition[8] + local) * 12
            type_index = struct.unpack_from("<i", self.metadata, field + 4)[0]
            field_pointer = self.pointer(self.types + type_index * 8)
            attributes = struct.unpack_from("<I", self.binary, self.offset(field_pointer) + 8)[0] & 0xFFFF
            if attributes & 0x10:
                continue
            instance_fields.append((struct.unpack_from("<i", self.binary, offset_record + local * 4)[0] - 16, field_pointer))
        layout = value["aggregate"]
        assert len(layout["fields"]) == len(instance_fields) > 0
        covered = 0
        for actual, (offset, field_pointer) in zip(layout["fields"], instance_fields):
            assert actual["byteOffset"] == offset == covered
            self.check_type(actual["type"], field_pointer, contexts)
            field_width = actual["type"]["width"] // 8
            natural = actual["type"].get("aggregate", {}).get("alignmentBytes", field_width)
            packing_code = (definition[24] >> 6) & 15
            alignment = min(natural, 1 << (packing_code - 1)) if packing_code else natural
            assert alignment == natural
            assert offset % alignment == 0
            alignments.append(alignment)
            covered += field_width
        assert covered == size and layout["alignmentBytes"] == max(alignments)
        assert size % layout["alignmentBytes"] == 0
        self.counts["aggregateLayouts"] += 1

    def check_method(self, method, instance=None):
        contexts = ((), ())
        if instance is not None:
            table_index, spec_index = instance["tableIndex"], instance["methodSpec"]
            table = struct.unpack_from("<iiii", self.binary, self.methods + table_index * 16)
            assert table[0] == spec_index and table[1] == instance["pointerIndex"]
            spec = struct.unpack_from("<iii", self.binary, self.specs + spec_index * 12)
            assert spec == (method["methodDefinition"], instance["classInstantiation"], instance["methodInstantiation"])
            address = self.pointer(self.generic_pointers + table[1] * 8)
            assert method["entry"] == (hex(address) if address else None)
            contexts = self.context(spec[1]), self.context(spec[2])
            markers = {marker for context in contexts for pointer in context for marker in self.markers(pointer)}
            assert sorted(markers) == instance["fullySharedMarkers"]
            self.counts["genericRecords"] += 1
            if instance["fullySharedMarkers"]:
                assert method["contract"] is None and method["signature"] is None
                self.counts["fullySharedRejected"] += 1
        if method["signature"] is None:
            assert method["contract"] is None
            if method["entry"] is not None:
                self.entry_gaps.add(method["entry"])
            return
        stride = 36 if self.version == 31 else 32
        row = struct.unpack_from("<7i4H" if self.version == 31 else "<6i4H", self.metadata,
                                 self.tables[48][0] + method["methodDefinition"] * stride)
        shift = int(self.version == 31)
        start, flags, count = row[3 + shift], row[6 + shift], row[9 + shift]
        signature = method["signature"]
        self.check_type(signature["result"], self.pointer(self.types + row[2] * 8), contexts)
        cursor = int(flags & 0x10 == 0)
        assert len(signature["arguments"]) == cursor + count + 1
        if cursor:
            assert signature["arguments"][0] == {"width": 64, "kind": "Address"}
        for ordinal in range(count):
            parameter = self.tables[88][0] + (start + ordinal) * 12
            parameter_type = struct.unpack_from("<i", self.metadata, parameter + 8)[0]
            self.check_type(signature["arguments"][cursor + ordinal], self.pointer(self.types + parameter_type * 8), contexts)
        assert signature["arguments"][-1] == {"width": 64, "kind": "Address"}
        assert method["signatureStatus"] == "known" and not method["gaps"]
        if method["entry"] is not None:
            signature_json = json.dumps(signature, sort_keys=True)
            previous = self.entry_signatures.setdefault(method["entry"], signature_json)
            if previous != signature_json:
                self.entry_conflicts.add(method["entry"])
        self.counts["knownGenericSignatures" if instance else "knownDefinitionSignatures"] += 1


def check(path):
    manifest = json.loads(path.read_text(encoding="utf-8"))
    for source in [manifest["provider"]] + manifest["providerSources"]:
        assert digest(Path(source["path"])) == source["sha256"]
    proof = RawProof(manifest)
    for file_key, hash_key, generic in (("methodsFile", "methodsSha256", False),
                                      ("genericMethodsFile", "genericMethodsSha256", True)):
        rows = path.parent / manifest[file_key]
        assert digest(rows) == manifest[hash_key]
        with rows.open(encoding="utf-8") as stream:
            for line in stream:
                record = json.loads(line)
                proof.check_method(record, record["genericInstance"] if generic else None)
    assert proof.counts["genericRecords"] == manifest["registrations"]["genericTables"]["methodTableRecords"]
    assert proof.counts["fullySharedRejected"] == manifest["summary"]["genericMethods"]["fullySharedMarkerRecords"]
    rows = path.parent / manifest["entriesFile"]
    assert digest(rows) == manifest["entriesSha256"]
    with rows.open(encoding="utf-8") as stream:
        for line in stream:
            record = json.loads(line)
            if record["entry"] in proof.entry_gaps or record["entry"] in proof.entry_conflicts:
                assert record["contract"] is None and record["signatureStatus"] != "known"
            elif record["contract"] is not None and record["entry"] in proof.entry_signatures:
                assert json.dumps(record["contract"]["signature"], sort_keys=True) == proof.entry_signatures[record["entry"]]
                proof.counts["mergedEntrySignatures"] += 1
            if any(alias["fullySharedMarkers"] for alias in record.get("genericMethodSpecs", [])):
                assert record["contract"] is None and record["signatureStatus"] != "known"
                proof.counts["fullySharedEntryAliasesRejected"] += 1
    result = {"manifest": str(path), "checks": "passed", "counts": dict(proof.counts)}
    print(json.dumps(result, ensure_ascii=False), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifests", type=Path, nargs="+")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = [check(path) for path in args.manifests]
    if args.output:
        args.output.write_text(json.dumps({"results": results, "providerSha256": digest(Path(__file__))},
                                         ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
