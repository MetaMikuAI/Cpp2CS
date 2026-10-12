"""全量独立解码核对；消费 C# 扫描的全部候选边界，不验证 MIR 的值语义。"""
import argparse
import bisect
import collections
import gzip
import hashlib
import json
import mmap
import struct
import sys
import time
from pathlib import Path

import capstone
import pefile


def boundaries(path):
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        assert stream.readline().rstrip() == "address\tfileOffset\tlength\tstatus"
        for line in stream:
            address, offset, length, status = line.rstrip().split("\t")
            yield int(address, 16), int(offset, 16), int(length), status


def arm_decodings(data, ranges, decoder):
    for region in ranges:
        start = int(region["address"], 16)
        offset = int(region["fileOffset"], 16)
        length = region["FileSize"]
        prefix = min((-start) % 4, length)
        position = prefix
        aligned_end = prefix + (length - prefix) // 4 * 4
        while position < aligned_end:
            size = min(262144, aligned_end - position)
            consumed = 0
            for address, width, mnemonic, operands in decoder.disasm_lite(data[offset + position:offset + position + size], start + position):
                assert width == 4 and address == start + position + consumed
                consumed += width
                yield address, width, mnemonic != ".byte", mnemonic, operands
            assert consumed == size
            position += size


def pe_entries(path):
    image = pefile.PE(str(path), fast_load=True)
    directory = image.OPTIONAL_HEADER.DATA_DIRECTORY[3]
    if directory.Size == 0:
        return [], 0
    assert directory.Size % 12 == 0
    raw = image.get_data(directory.VirtualAddress, directory.Size)
    assert len(raw) == directory.Size
    starts = []
    malformed = 0
    for begin, end, unwind in struct.iter_unpack("<III", raw):
        if begin >= end:
            malformed += 1
        starts.append(image.OPTIONAL_HEADER.ImageBase + begin)
    return sorted(starts), malformed


def run(report_path, binary_path, output_directory):
    report = json.loads(report_path.read_text(encoding="utf-8-sig"))
    with Path(report["boundaryIndex"]).open("rb") as boundary_file:
        boundary_hash = hashlib.file_digest(boundary_file, "sha256").hexdigest().upper()
    assert boundary_hash == report["boundaryIndexSha256"], "候选边界流与扫描报告不一致"
    output_directory.mkdir(parents=True, exist_ok=True)
    stem = report_path.name.removesuffix(".report.json")
    issues_path = output_directory / f"{stem}.decoder.issues.tsv.gz"
    entry_issues_path = output_directory / f"{stem}.entry-issues.tsv.gz"
    output_path = output_directory / f"{stem}.decoder.report.json"
    is_arm = report["architecture"] == "Arm64"
    assert is_arm or report["architecture"] == "X64"
    ranges = report["executableRanges"]
    starts = [int(region["address"], 16) for region in ranges]
    expected_next = [start + min((-start) % 4, region["FileSize"]) if is_arm else start for start, region in zip(starts, ranges)]
    entries, malformed_entries = ([], 0) if is_arm else pe_entries(binary_path)
    entry_index = 0
    stats = collections.Counter({name: 0 for name in ["candidates", "candidateBytes", "capstoneDecoded", "capstoneNotDecoded", "disagreements", "supported_arm_encoding_not_decoded", "decoder_validity_disagreement", "decoder_length_disagreement"]})
    unsupported_mnemonics = collections.Counter()
    entry_stats = collections.Counter()
    examples = []
    decoder = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_LITTLE_ENDIAN) if is_arm else capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    decoder.skipdata = is_arm
    begin_time = time.monotonic()
    with binary_path.open("rb") as binary, mmap.mmap(binary.fileno(), 0, access=mmap.ACCESS_READ) as data, gzip.open(issues_path, "wt", encoding="utf-8") as issues, gzip.open(entry_issues_path, "wt", encoding="utf-8") as entry_issues:
        digest = hashlib.sha256(data).hexdigest()
        assert digest.upper() == report["inputSha256"].upper(), "输入文件哈希与扫描报告不一致"
        issues.write("address\tfileOffset\ticedLength\tcapstoneLength\tstatus\tdisagreement\tbytes\tcapstone\n")
        entry_issues.write("entryAddress\tclassification\tcandidateAddress\tcandidateLength\n")
        arm_stream = iter(arm_decodings(data, ranges, decoder)) if is_arm else None
        for address, offset, length, status in boundaries(report["boundaryIndex"]):
            assert status in {"V", "E", "U", "I"}
            region_index = bisect.bisect_right(starts, address) - 1
            assert region_index >= 0
            region = ranges[region_index]
            region_start = starts[region_index]
            region_offset = int(region["fileOffset"], 16)
            assert address == expected_next[region_index], "候选边界流存在未解释的空隙或重复"
            assert offset == region_offset + address - region_start
            assert 0 < length <= 15 and address + length <= region_start + region["FileSize"]
            expected_next[region_index] += length
            stats["candidates"] += 1
            stats["candidateBytes"] += length
            stats[f"scannerStatus_{status}"] += 1
            if is_arm:
                decoded_address, decoded_length, decoded, mnemonic, operands = next(arm_stream)
                assert address == decoded_address and length == decoded_length == 4
            else:
                window_end = min(offset + 15, region_offset + region["FileSize"])
                instruction = next(decoder.disasm_lite(data[offset:window_end], address, count=1), None)
                decoded = instruction is not None
                decoded_length = instruction[1] if decoded else 0
                mnemonic, operands = instruction[2:] if decoded else ("", "")
            stats["capstoneDecoded" if decoded else "capstoneNotDecoded"] += 1
            if status == "U":
                unsupported_mnemonics[mnemonic if decoded else "undecoded"] += 1
            disagreement = None
            if is_arm:
                if not decoded and status in {"V", "E"}:
                    disagreement = "supported_arm_encoding_not_decoded"
            elif decoded != (status != "I"):
                disagreement = "decoder_validity_disagreement"
            elif decoded and decoded_length != length:
                disagreement = "decoder_length_disagreement"
            if disagreement:
                stats["disagreements"] += 1
                stats[disagreement] += 1
                raw = data[offset:offset + length].hex()
                issues.write(f"{address:X}\t{offset:X}\t{length}\t{decoded_length}\t{status}\t{disagreement}\t{raw}\t{mnemonic} {operands}\n")
                if len(examples) < 16:
                    examples.append({"address": hex(address), "kind": disagreement, "bytes": raw, "capstone": f"{mnemonic} {operands}"})
            while entry_index < len(entries) and entries[entry_index] < address:
                entry_stats["notCovered"] += 1
                entry_issues.write(f"{entries[entry_index]:X}\tnotCovered\t{address:X}\t{length}\n")
                entry_index += 1
            while entry_index < len(entries) and entries[entry_index] < address + length:
                entry = entries[entry_index]
                if entry == address:
                    entry_stats["atCandidateStart"] += 1
                else:
                    entry_stats["insideCandidate"] += 1
                    entry_issues.write(f"{entry:X}\tinsideCandidate\t{address:X}\t{length}\n")
                entry_index += 1
            if stats["candidates"] % 1_000_000 == 0:
                print(f"{report['architecture']}: {stats['candidates']:,} independent decoder checks, {stats['disagreements']:,} disagreements", file=sys.stderr)
        if arm_stream is not None:
            assert next(arm_stream, None) is None
        while entry_index < len(entries):
            entry_stats["notCovered"] += 1
            entry_issues.write(f"{entries[entry_index]:X}\tnotCovered\t-\t0\n")
            entry_index += 1
    for region, start, next_address in zip(ranges, starts, expected_next):
        prefix = min((-start) % 4, region["FileSize"]) if is_arm else 0
        expected_end = start + prefix + (region["FileSize"] - prefix) // 4 * 4 if is_arm else start + region["FileSize"]
        assert next_address == expected_end
    assert stats["candidates"] == report["candidates"]
    assert stats["candidateBytes"] + report["truncatedOrUnalignedBytes"] == report["bytesCovered"]
    result = {
        "schemaVersion": 1,
        "inputSha256": digest.upper(),
        "scannerReport": str(report_path.resolve()),
        "scannerAssemblySha256": report["implementationAssemblySha256"],
        "boundaryIndex": report["boundaryIndex"],
        "boundaryIndexSha256": boundary_hash,
        "architecture": report["architecture"],
        "independentDecoder": f"Capstone {capstone.__version__}",
        "counts": dict(stats),
        "unsupportedMnemonics": dict(sorted(unsupported_mnemonics.items())),
        "peRuntimeFunctionEntries": len(entries),
        "peMalformedEntries": malformed_entries,
        "peEntryCoverage": dict(entry_stats),
        "decoderChecksPassed": stats["disagreements"] == 0,
        "peEntryBoundariesCovered": entry_stats["notCovered"] == 0 and entry_stats["insideCandidate"] == 0 and malformed_entries == 0,
        "limitations": "Full candidate decode comparison, not MIR execution equivalence or proof of reachable code. ARM undecoded unsupported words may be embedded data or unsupported ISA. PE .pdata entries are entry evidence, not a complete function inventory. Decoder disagreements require investigation rather than majority voting.",
        "elapsedSeconds": time.monotonic() - begin_time,
        "issues": str(issues_path.resolve()),
        "entryIssues": str(entry_issues_path.resolve()),
        "firstDisagreements": examples,
    }
    output_path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(output_path.resolve())
    return 0 if result["decoderChecksPassed"] and result["peEntryBoundariesCovered"] else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--output-directory", type=Path, required=True)
    args = parser.parse_args()
    sys.exit(run(args.report, args.binary, args.output_directory))
