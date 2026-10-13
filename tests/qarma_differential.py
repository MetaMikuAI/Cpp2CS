"""用未改写的 QEMU C QARMA 函数，对照生产 Qarma64 的完整 64 位输出。"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess


parser = argparse.ArgumentParser()
parser.add_argument("--core-dll", type=Path, required=True)
parser.add_argument("--qemu-source", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
source = args.qemu_source.read_text(encoding="utf-8")
first = source.index("static uint64_t pac_cell_shuffle(")
last = source.index("static uint64_t pauth_computepac_impdef(")
# The algorithm remains in C with its own shuffle, mixing and tweak implementation.
wrapper = """#define _CRT_SECURE_NO_WARNINGS
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <inttypes.h>
typedef struct { uint64_t hi, lo; } ARMPACKey;
#define MAKE_64BIT_MASK(start, length) (((UINT64_C(1) << (length)) - 1) << (start))
static uint64_t extract64(uint64_t x, int start, int length) { return (x >> start) & ((UINT64_C(1) << length) - 1); }
static uint32_t extract32(uint32_t x, int start, int length) { return (x >> start) & ((UINT32_C(1) << length) - 1); }
""" + source[first:last] + """
int main(void) {
    uint64_t data, modifier;
    ARMPACKey key;
    while (scanf("%" SCNx64 " %" SCNx64 " %" SCNx64 " %" SCNx64, &data, &modifier, &key.hi, &key.lo) == 4)
        printf("%016" PRIX64 "\\n", pauth_computepac_architected(data, modifier, key, false));
    return 0;
}
"""
args.output.parent.mkdir(parents=True, exist_ok=True)
oracle_source = args.output.parent / "qemu-qarma-oracle.c"
oracle_exe = args.output.parent / "qemu-qarma-oracle.exe"
oracle_source.write_text(wrapper, encoding="utf-8")
subprocess.run(["clang", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", str(oracle_source), "-o", str(oracle_exe)], check=True)
rng = random.Random(0x5141524D41)
edges = [0, 1, (1 << 64) - 1, 1 << 63, 0x0123456789ABCDEF, 0xFEDCBA9876543210]
vectors = list(itertools.product(edges, repeat=4))
vectors += [tuple(rng.getrandbits(64) for _ in range(4)) for _ in range(8192)]
payload = "".join(" ".join(f"{value:016X}" for value in vector) + "\n" for vector in vectors)
oracle = subprocess.run([str(oracle_exe)], input=payload, text=True, capture_output=True, check=True).stdout.splitlines()
actual = subprocess.run(["dotnet", str(args.core_dll)], input=payload, text=True, capture_output=True, check=True).stdout.splitlines()
assert len(oracle) == len(actual) == len(vectors)
for vector, expected, output in zip(vectors, oracle, actual):
    assert expected == output, (vector, expected, output)
summary = dict(cases=len(vectors), boundary="QEMU C source oracle, not hardware execution", seed=hex(0x5141524D41),
               source_url="https://raw.githubusercontent.com/qemu/qemu/master/target/arm/tcg/pauth_helper.c",
               source_sha256=hashlib.sha256(args.qemu_source.read_bytes()).hexdigest(),
               source_extraction="pac_cell_shuffle through pauth_computepac_architected, unchanged; wrapper supplies integer extraction helpers and stdin/stdout",
               core_dll_sha256=hashlib.sha256(args.core_dll.read_bytes()).hexdigest(),
               test_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               samples=[dict(data=f"{values[0]:016X}", modifier=f"{values[1]:016X}", key_high=f"{values[2]:016X}",
                             key_low=f"{values[3]:016X}", result=result) for values, result in zip(vectors[1290:1306], oracle[1290:1306])])
args.output.write_text(json.dumps(summary, indent=2), encoding="utf-8")
print(json.dumps({key: value for key, value in summary.items() if key != "samples"}))
