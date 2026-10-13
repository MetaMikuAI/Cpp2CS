"""泛型标量替换、聚合布局拒绝和同址签名冲突的固定负例。"""
import json
import struct
from types import SimpleNamespace

from nir_contract_inventory import merge_method
from nir_il2cpp_types import Types


class FixtureBinary:
    def __init__(self):
        self.data = bytearray(4096)
        self.entries = {}

    def offset(self, address, size=1):
        return address if 0 < address and address + size <= len(self.data) else None

    def file_location(self, address):
        return hex(address) if self.offset(address) is not None else None

    def words(self, address, count):
        if self.offset(address, count * 8) is None:
            return None
        return struct.unpack_from(f"<{count}Q", self.data, address)

    def add(self, address, evidence):
        entry = self.entries.setdefault(address, {"methodDefinitions": [], "signatureEvidence": [], "evidence": [],
                                                  "gaps": [], "signatureStatus": "unknown", "contract": None})
        entry["evidence"].append(evidence)
        return entry


def value_fixture(offsets=(16, 20), size=24, bitfield=1, field_codes=(12, 12), marker=False):
    binary = FixtureBinary()
    strings = {0: "Pair", 1: "Example", 2: "left", 3: "right", 4: "value__"}
    definition = [0] * 26
    definition[0], definition[1], definition[2] = 0, 1, 0
    definition[6], definition[8], definition[18], definition[24] = -1, 0, len(field_codes), bitfield
    fields = [(2 + index, index + 1, 0) for index in range(len(field_codes))]
    if bitfield & 2:
        fields[0] = (4, 1, 0)
    if marker:
        strings[0], strings[1] = "__Il2CppFullySharedGenericStructType", "Unity.IL2CPP.Metadata"
    pointers = (128,) + tuple(144 + index * 16 for index in range(len(field_codes)))
    struct.pack_into("<QI", binary.data, 128, 0, 17 << 16)
    for pointer, code in zip(pointers[1:], field_codes):
        struct.pack_into("<QI", binary.data, pointer, 0, code << 16)
    struct.pack_into("<Q", binary.data, 512, 1024)
    struct.pack_into("<Q", binary.data, 520, 1536)
    for index, offset in enumerate(offsets):
        struct.pack_into("<i", binary.data, 1024 + index * 4, offset)
    struct.pack_into("<IiII", binary.data, 1536, size, -1 if marker else size - 16, 0, 0)
    registration = [0] * 16
    registration[10:14] = 1, 512, 1, 520
    metadata = SimpleNamespace(types=[tuple(definition)], fields=fields, type_offset=200,
                               field_offset=300, string=lambda index: strings[index],
                               generic_parameters=[], generic_containers=[])
    return Types(binary, metadata, (2048, tuple(registration), pointers))


def method(signature, index=0, gaps=()):
    return {"entry": "0x100", "methodDefinition": index,
            "signatureEvidence": [{"kind": "il2cpp.module-method-pointer", "pointerIndex": index}],
            "gaps": list(gaps), "contract": {"entryAddress": 256, "signature": signature} if signature is not None else None}


def main():
    checks = 0
    pair = value_fixture()
    value, _, gap = pair.scalar(0)
    assert gap is None and value == {"width": 64, "kind": "Aggregate", "aggregate": {
        "alignmentBytes": 4, "fields": [{"byteOffset": 0, "type": {"width": 32, "kind": "Float"}},
                                         {"byteOffset": 4, "type": {"width": 32, "kind": "Float"}}]}}
    checks += 1
    for arguments in ({"offsets": (16, 24), "size": 32}, {"offsets": (16, 16)},
                      {"size": 32}, {"offsets": (12, 16)}, {"offsets": (), "size": 24, "field_codes": ()}):
        value, _, gap = value_fixture(**arguments).scalar(0)
        assert value is None and gap
        checks += 1
    packed = value_fixture(offsets=(16, 17), size=21, bitfield=1 | (1 << 6), field_codes=(5, 8))
    value, _, gap = packed.scalar(0)
    assert value is None and "packing reduces" in gap
    checks += 1
    packed_pair = value_fixture(offsets=(16, 24), size=32, bitfield=1 | (3 << 6), field_codes=(11, 11))
    value, _, gap = packed_pair.scalar(0)
    assert value is None and "packing reduces" in gap
    checks += 1
    byte_pair = value_fixture(offsets=(16, 17), size=18, bitfield=1 | (1 << 6), field_codes=(5, 5))
    value, _, gap = byte_pair.scalar(0)
    assert gap is None and value["width"] == 16 and value["aggregate"]["alignmentBytes"] == 1
    checks += 1
    enum = value_fixture(offsets=(16,), size=20, bitfield=3, field_codes=(8,))
    value, evidence, gap = enum.scalar(0)
    assert value == {"width": 32, "kind": "Integer"} and gap is None
    assert any(item.get("kind") == "metadata.enum-underlying" for item in evidence)
    checks += 1
    marker = value_fixture(offsets=(), field_codes=(), marker=True)
    assert marker.markers(128) == (0,) and marker.scalar(0)[2]
    checks += 1
    generic = value_fixture(field_codes=(18, 8))
    generic.metadata.generic_parameters = [(0, 0, -1, 0, 0, 0)]
    generic.metadata.generic_containers = [(0, 1, 0, 0)]
    generic.metadata.generic_parameter_offset = 2000
    struct.pack_into("<QI", generic.binary.data, 128, 0, 19 << 16)
    reference, _, gap = generic.scalar(0, ((144,), ()))
    assert reference == {"width": 64, "kind": "Address"} and gap is None
    integer, _, gap = generic.scalar(0, ((160,), ()))
    assert integer == {"width": 32, "kind": "Integer"} and gap is None
    assert generic.scalar(0)[0] is None and generic.scalar(0)[2]
    checks += 3
    byref = value_fixture()
    struct.pack_into("<QI", byref.binary.data, 128, 0, (19 << 16) | (1 << 29))
    assert byref.scalar(0)[0] == {"width": 64, "kind": "Address"}
    checks += 1
    address_signature = {"arguments": [{"width": 64, "kind": "Address"}], "result": None}
    integer_signature = {"arguments": [{"width": 64, "kind": "Integer"}], "result": None}
    binary = FixtureBinary()
    merge_method(binary, method(address_signature))
    merge_method(binary, method(address_signature, 1))
    assert binary.entries[256]["signatureStatus"] == "known"
    assert binary.entries[256]["methodDefinitions"] == [0, 1]
    merge_method(binary, method(integer_signature, 2))
    assert binary.entries[256]["signatureStatus"] == "conflict"
    assert binary.entries[256]["methodDefinitions"] == [0, 1, 2]
    checks += 2
    binary = FixtureBinary()
    merge_method(binary, method(address_signature))
    merge_method(binary, method(None, 1, ["unresolved fully-shared prototype"]))
    assert binary.entries[256]["unresolvedSignatureAliases"]
    assert "unresolved fully-shared prototype" in binary.entries[256]["gaps"]
    checks += 1
    print(json.dumps({"checks": "passed", "cases": checks}))


if __name__ == "__main__":
    main()
