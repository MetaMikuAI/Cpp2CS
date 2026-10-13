"""从原始 metadata/binary 字节复核清单中的标量与浮点合同。"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import struct


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest().upper()


def check_float(scalar, evidence, binary, counts):
    offset = int(evidence["typeFileOffset"], 16)
    bits = struct.unpack_from("<I", binary, offset + 8)[0]
    code, byref = (bits >> 16) & 255, bool(bits & (1 << 29))
    assert code == evidence["typeCode"] and byref == evidence["byref"]
    if code in (12, 13) and not byref:
        assert scalar == {"width": 32 if code == 12 else 64, "kind": "Float"}
        counts["float32Slots" if code == 12 else "float64Slots"] += 1
    elif byref:
        assert scalar == {"width": 64, "kind": "Address"}
    else:
        assert scalar is None or scalar["kind"] != "Float"


def check(path):
    manifest = json.loads(path.read_text(encoding="utf-8"))
    assert manifest["format"] == "cpp2cs.nir-contract-inventory.v1"
    binary_path, metadata_path = Path(manifest["binary"]["path"]), Path(manifest["metadata"]["path"])
    assert digest(binary_path) == manifest["binary"]["sha256"]
    assert digest(metadata_path) == manifest["metadata"]["sha256"]
    binary, metadata = binary_path.read_bytes(), metadata_path.read_bytes()
    methods_path, entries_path = path.parent / manifest["methodsFile"], path.parent / manifest["entriesFile"]
    assert digest(methods_path) == manifest["methodsSha256"]
    assert digest(entries_path) == manifest["entriesSha256"]
    counts = Counter()
    metadata_method_offset, metadata_method_size = struct.unpack_from("<II", metadata, 48)
    version = struct.unpack_from("<I", metadata, 4)[0]
    stride = 36 if version == 31 else 32
    with methods_path.open(encoding="utf-8") as stream:
        for expected_index, line in enumerate(stream):
            method = json.loads(line)
            assert method["methodDefinition"] == expected_index
            counts["methods"] += 1
            if method["signatureStatus"] != "known":
                assert method["signature"] is None and method["contract"] is None
                continue
            counts["knownMethodSignatures"] += 1
            evidence = method["signatureEvidence"]
            method_offset = int(evidence[0]["recordFileOffset"], 16)
            assert method_offset == metadata_method_offset + expected_index * stride
            assert struct.unpack_from("<i", metadata, method_offset + 8)[0] == evidence[2]["typeIndex"]
            signature = method["signature"]
            check_float(signature["result"], evidence[2], binary, counts)
            static = bool(evidence[0]["flags"] & 0x10)
            arg_index = 0 if static else 1
            assert len(signature["arguments"]) == evidence[0]["parameterCount"] + arg_index + 1
            for index, source in enumerate(evidence):
                if source.get("kind") != "metadata.parameter":
                    continue
                offset = int(source["recordFileOffset"], 16)
                assert struct.unpack_from("<i", metadata, offset + 8)[0] == evidence[index + 1]["typeIndex"]
                check_float(signature["arguments"][arg_index], evidence[index + 1], binary, counts)
                arg_index += 1
            assert signature["arguments"][-1] == {"width": 64, "kind": "Address"}
            assert evidence[-1]["kind"] == "adopted-il2cpp-generated-method-prototype"
            assert not method["gaps"]
    assert counts["methods"] == metadata_method_size // stride == manifest["metadata"]["methodCount"]
    statuses = Counter()
    previous = -1
    with entries_path.open(encoding="utf-8") as stream:
        for line in stream:
            entry = json.loads(line)
            address = int(entry["entry"], 16)
            assert address > previous
            previous = address
            statuses[entry["signatureStatus"]] += 1
            if entry["signatureStatus"] != "known":
                assert entry["contract"] is None
                continue
            contract = entry["contract"]
            assert contract is not None and contract["entryAddress"] == address
            assert not entry["signatureSynthetic"] and not entry.get("unresolvedSignatureAliases")
            assert entry["signatureEvidence"] and contract["effects"]["mayThrow"]
            signature = contract["signature"]
            if any(value is not None and value["kind"] == "Float" for value in signature["arguments"] + [signature["result"]]):
                counts["entriesWithFloatContract"] += 1
    assert dict(statuses) == manifest["summary"]["entries"]
    assert sum(statuses.values()) == manifest["entryCount"]
    result = {"manifest": str(path), "checks": "passed", "counts": dict(counts), "entryStatuses": dict(statuses)}
    print(json.dumps(result, ensure_ascii=False))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifests", type=Path, nargs="+")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = [check(path) for path in args.manifests]
    if args.output:
        args.output.write_text(json.dumps({"results": results, "providerSha256": digest(Path(__file__))}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
