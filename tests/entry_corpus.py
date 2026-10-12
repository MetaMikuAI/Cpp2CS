"""按全部 PE .pdata 入口补充主线性扫描遗漏的候选，直到主边界合流或函数记录结束。"""
import argparse
import bisect
import collections
import gzip
import hashlib
import json
import struct
import subprocess
import sys
import time
from pathlib import Path

import capstone


ROOT = Path(__file__).resolve().parents[1]


def file_hash(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest().upper()


def pe_runtime_functions(data):
    nt = struct.unpack_from("<I", data, 60)[0]
    assert data[:2] == b"MZ" and data[nt:nt + 4] == b"PE\0\0"
    assert struct.unpack_from("<H", data, nt + 4)[0] == 0x8664
    optional = nt + 24
    assert struct.unpack_from("<H", data, optional)[0] == 0x20B
    image_base = struct.unpack_from("<Q", data, optional + 24)[0]
    directory_count = struct.unpack_from("<I", data, optional + 108)[0]
    if directory_count <= 3:
        return image_base, [], None
    directory_rva, directory_size = struct.unpack_from("<II", data, optional + 112 + 3 * 8)
    if directory_size == 0:
        assert directory_rva == 0
        return image_base, [], None
    assert directory_size % 12 == 0
    section_count = struct.unpack_from("<H", data, nt + 6)[0]
    optional_size = struct.unpack_from("<H", data, nt + 20)[0]
    section_table = optional + optional_size
    mappings = []
    for index in range(section_count):
        section = section_table + index * 40
        virtual_size, rva, raw_size, raw_offset = struct.unpack_from("<IIII", data, section + 8)
        file_size = min(raw_size, virtual_size if virtual_size else raw_size)
        if rva <= directory_rva and directory_rva - rva < file_size and directory_size <= file_size - (directory_rva - rva):
            mappings.append(raw_offset + directory_rva - rva)
    assert len(mappings) == 1, "异常目录必须完整映射到唯一文件范围"
    offset = mappings[0]
    assert offset + directory_size <= len(data)
    entries = []
    for index, (begin, end, unwind) in enumerate(struct.iter_unpack("<III", data[offset:offset + directory_size])):
        entries.append((image_base + begin, image_base + end, index, unwind))
    return image_base, sorted(entries), {"rva": hex(directory_rva), "fileOffset": hex(offset), "size": directory_size}


def primary_boundaries(path):
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        assert stream.readline().rstrip() == "address\tfileOffset\tlength\tstatus"
        for line in stream:
            address, offset, length, status = line.rstrip().split("\t")
            yield int(address, 16), int(offset, 16), int(length), status


def write_entry(stream, entry, classification, address=None, length=None, status="-"):
    begin, end, index, unwind = entry
    stream.write(f"{index}\t{begin:X}\t{end:X}\t{unwind:X}\t{classification}\t{address:X}" if address is not None else f"{index}\t{begin:X}\t{end:X}\t{unwind:X}\t{classification}\t-")
    stream.write(f"\t{length if length is not None else '-'}\t{status}\n")


def classify_entries(report, entries, evidence_path):
    counts = collections.Counter({key: 0 for key in ["atCandidateStart", "insideCandidate", "notCovered", "malformedEntries"]})
    primary_statuses = collections.Counter()
    seeds = []
    active = []
    entry_index = 0
    candidate_count = 0
    candidate_bytes = 0
    previous_end = 0
    with gzip.open(evidence_path, "wt", encoding="utf-8") as evidence:
        evidence.write("pdataIndex\tentryAddress\tendAddress\tunwindRva\tclassification\tprimaryAddress\tprimaryLength\tprimaryStatus\n")
        for address, offset, length, status in primary_boundaries(report["boundaryIndex"]):
            assert address >= previous_end and 0 < length <= 15 and status in {"V", "E", "U", "I"}
            previous_end = address + length
            candidate_count += 1
            candidate_bytes += length
            active = [seed for seed in active if seed["end"] >= address]
            for seed in active:
                if seed["begin"] < address <= seed["end"]:
                    seed["primaryBoundaries"].add(address)
            while entry_index < len(entries) and entries[entry_index][0] < address + length:
                entry = entries[entry_index]
                begin, end, index, unwind = entry
                classification = "notCovered" if begin < address else "atCandidateStart" if begin == address else "insideCandidate"
                counts[classification] += 1
                if begin >= end:
                    counts["malformedEntries"] += 1
                elif classification != "atCandidateStart":
                    seed = {"begin": begin, "end": end, "pdataIndex": index, "unwindRva": unwind,
                            "primaryClassification": classification, "primaryCoverAddress": address if classification == "insideCandidate" else None,
                            "primaryCoverLength": length if classification == "insideCandidate" else None, "primaryBoundaries": set()}
                    if begin < address <= end:
                        seed["primaryBoundaries"].add(address)
                    seeds.append(seed)
                    active.append(seed)
                if classification == "atCandidateStart":
                    primary_statuses[status] += 1
                write_entry(evidence, entry, classification, address if classification != "notCovered" else None,
                            length if classification != "notCovered" else None, status if classification != "notCovered" else "-")
                entry_index += 1
            if candidate_count % 1_000_000 == 0:
                print(f"entry coverage: {candidate_count:,} primary candidates, {entry_index:,} .pdata entries classified", file=sys.stderr)
        while entry_index < len(entries):
            entry = entries[entry_index]
            begin, end, index, unwind = entry
            counts["notCovered"] += 1
            if begin >= end:
                counts["malformedEntries"] += 1
            else:
                seeds.append({"begin": begin, "end": end, "pdataIndex": index, "unwindRva": unwind,
                              "primaryClassification": "notCovered", "primaryCoverAddress": None, "primaryCoverLength": None, "primaryBoundaries": set()})
            write_entry(evidence, entry, "notCovered")
            entry_index += 1
    assert candidate_count == report["candidates"]
    assert candidate_bytes + report["truncatedOrUnalignedBytes"] == report["bytesCovered"]
    return counts, primary_statuses, seeds


def clean(value):
    return str(value).replace("\t", " ").replace("\r", " ").replace("\n", " ")


def run(report_path, binary_path, dll_path, output_directory):
    started = time.monotonic()
    report = json.loads(report_path.read_text(encoding="utf-8-sig"))
    assert report["architecture"] == "X64", "本脚本只支持 PE32+ AMD64 .pdata 入口"
    data = binary_path.read_bytes()
    input_hash = hashlib.sha256(data).hexdigest().upper()
    assert input_hash == report["inputSha256"].upper(), "输入文件与主扫描报告哈希不一致"
    boundary_hash = file_hash(report["boundaryIndex"])
    assert boundary_hash == report["boundaryIndexSha256"], "主候选边界流哈希不一致"
    assembly_hash = file_hash(dll_path)
    image_base, entries, exception_directory = pe_runtime_functions(data)
    assert image_base == int(report["preferredBase"], 16)
    output_directory.mkdir(parents=True, exist_ok=True)
    stem = report_path.name.removesuffix(".report.json")
    evidence_path = output_directory / f"{stem}.pdata-entries.tsv.gz"
    index_path = output_directory / f"{stem}.entry-supplement.tsv.gz"
    result_path = output_directory / f"{stem}.entry.report.json"
    coverage, primary_statuses, seeds = classify_entries(report, entries, evidence_path)
    ranges = report["executableRanges"]
    starts = [int(region["address"], 16) for region in ranges]
    counts = collections.Counter({key: 0 for key in ["paths", "candidates", "validated", "unsupported", "invalid", "operations", "bytes", "mergedPrimary", "reachedFunctionEnd", "mappingUnavailable", "codeRelocationRequired", "decoderDisagreements"]})
    support_classes = collections.Counter()
    forms = collections.Counter()
    unsupported_mnemonics = collections.Counter()
    seen_candidates = set()
    paths = []
    decoder = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    process = subprocess.Popen(["dotnet", str(dll_path), "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, encoding="utf-8", bufsize=1)
    with gzip.open(index_path, "wt", encoding="utf-8") as index:
        index.write("pdataIndex\tentryAddress\taddress\tfileOffset\tlength\tstatus\tform\tsupport\tbytes\tcapstoneLength\tcapstone\treason\n")
        for seed in seeds:
            counts["paths"] += 1
            address = seed["begin"]
            path_candidates = 0
            outcome = None
            while address < seed["end"]:
                if address != seed["begin"] and address in seed["primaryBoundaries"]:
                    outcome = "mergedPrimary"
                    break
                range_index = bisect.bisect_right(starts, address) - 1
                if range_index < 0:
                    outcome = "mappingUnavailable"
                    break
                region = ranges[range_index]
                region_start = starts[range_index]
                file_size = region["FileSize"]
                if address >= region_start + file_size:
                    outcome = "mappingUnavailable"
                    break
                offset = int(region["fileOffset"], 16) + address - region_start
                length_available = min(15, seed["end"] - address, region_start + file_size - address)
                window = data[offset:offset + length_available]
                assert len(window) == length_available and window
                if any(address < relocation["Address"] + relocation["Size"] and address + length_available > relocation["Address"] for relocation in report["codeRelocations"]):
                    outcome = "codeRelocationRequired"
                    break
                request = {"arch": "x64", "address": hex(address), "bytes": window.hex(), "decodeFirst": True, "evaluate": False}
                process.stdin.write(json.dumps(request) + "\n")
                process.stdin.flush()
                response_line = process.stdout.readline()
                assert response_line, f"产品解码/提升进程提前结束，exit={process.poll()}"
                response = json.loads(response_line)
                length = response["length"]
                decoded = response["decoded"]
                assert isinstance(decoded, bool) and isinstance(length, int) and 0 < length <= length_available
                cap = next(decoder.disasm_lite(window, address, count=1), None)
                cap_decoded = cap is not None
                cap_length = cap[1] if cap_decoded else 0
                cap_display = f"{cap[2]} {cap[3]}" if cap_decoded else "undecoded"
                disagreement = decoded != cap_decoded or (decoded and length != cap_length)
                counts["decoderDisagreements"] += int(disagreement)
                counts["candidates"] += 1
                counts["bytes"] += length
                path_candidates += 1
                raw = data[offset:offset + length].hex()
                seen_candidates.add((address, length, raw))
                form = response.get("Form", "invalid")
                reason = response.get("Reason") or ""
                forms[form] += 1
                support = response.get("support", "-")
                if not decoded:
                    status = "I"
                    assert not response["supported"]
                    counts["invalid"] += 1
                elif response["supported"]:
                    status = "V"
                    counts["validated"] += 1
                    counts["operations"] += response["operations"]
                    support_classes[support] += 1
                else:
                    status = "U"
                    counts["unsupported"] += 1
                    unsupported_mnemonics[cap[2] if cap_decoded else "undecoded"] += 1
                if disagreement:
                    reason = "decoder disagreement; " + reason
                index.write(f"{seed['pdataIndex']}\t{seed['begin']:X}\t{address:X}\t{offset:X}\t{length}\t{status}\t{clean(form)}\t{clean(support)}\t{raw}\t{cap_length}\t{clean(cap_display)}\t{clean(reason)}\n")
                address += length
                if not decoded:
                    outcome = "invalid"
                    break
            if outcome is None:
                assert address == seed["end"]
                outcome = "reachedFunctionEnd"
            if outcome != "invalid":
                counts[outcome] += 1
            paths.append({"pdataIndex": seed["pdataIndex"], "entry": hex(seed["begin"]), "end": hex(seed["end"]),
                          "unwindRva": hex(seed["unwindRva"]), "primaryClassification": seed["primaryClassification"],
                          "primaryCoverAddress": hex(seed["primaryCoverAddress"]) if seed["primaryCoverAddress"] is not None else None,
                          "primaryCoverLength": seed["primaryCoverLength"], "candidates": path_candidates, "stopAddress": hex(address), "outcome": outcome})
    process.stdin.close()
    process.stdout.close()
    assert process.wait(timeout=30) == 0
    entries_recovered = sum(path["candidates"] > 0 for path in paths)
    closed_paths = counts["mergedPrimary"] + counts["reachedFunctionEnd"]
    result = {
        "schemaVersion": 1,
        "inputSha256": input_hash,
        "primaryReport": str(report_path.resolve()),
        "primaryAssemblySha256": report["implementationAssemblySha256"],
        "supplementAssembly": str(dll_path.resolve()),
        "supplementAssemblySha256": assembly_hash,
        "sameAssemblyAsPrimary": assembly_hash == report["implementationAssemblySha256"],
        "primaryBoundaryIndex": report["boundaryIndex"],
        "primaryBoundaryIndexSha256": boundary_hash,
        "scriptSha256": file_hash(__file__),
        "exceptionDirectory": exception_directory,
        "pdataEntries": len(entries),
        "primaryCoverage": dict(coverage),
        "primaryEntryStatuses": dict(primary_statuses),
        "supplementCounts": dict(counts),
        "supplementUniqueCandidates": len(seen_candidates),
        "supportClasses": dict(sorted(support_classes.items())),
        "forms": dict(sorted(forms.items())),
        "unsupportedMnemonics": dict(sorted(unsupported_mnemonics.items())),
        "entriesWithSupplementaryCandidate": entries_recovered,
        "allKnownEntriesHaveCandidate": coverage["atCandidateStart"] + entries_recovered == len(entries) and coverage["malformedEntries"] == 0,
        "allSupplementaryPathsJoinedOrEnded": closed_paths == len(seeds),
        "structuralChecksPassed": True,
        "independentDecoder": f"Capstone {capstone.__version__}",
        "decoderChecksPassed": counts["decoderDisagreements"] == 0,
        "paths": paths,
        "entryEvidence": str(evidence_path.resolve()),
        "entryEvidenceSha256": file_hash(evidence_path),
        "supplementaryIndex": str(index_path.resolve()),
        "supplementaryIndexSha256": file_hash(index_path),
        "elapsedSeconds": time.monotonic() - started,
        "limitations": "Supplementary linear paths start at PE .pdata BeginAddress evidence and use product Iced boundaries until primary-boundary join or EndAddress. This is not a complete CFG, branch-target discovery, native equivalence, complete ISA support, or proof all code entries were found. Structural checks run inside product serve for every supported MIR; normal-path-only support retains its original limitations. Unwind semantics are not reconstructed.",
    }
    result_path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(result_path.resolve())
    return 0 if result["allKnownEntriesHaveCandidate"] and result["allSupplementaryPathsJoinedOrEnded"] and result["decoderChecksPassed"] and counts["invalid"] == 0 else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--dll", type=Path, default=ROOT / "src/Cpp2CS/bin/Release/net10.0/Cpp2CS.dll")
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/verified")
    args = parser.parse_args()
    sys.exit(run(args.report, args.binary, args.dll, args.output))
