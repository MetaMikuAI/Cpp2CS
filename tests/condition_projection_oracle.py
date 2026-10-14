"""逐条条件对照 ARM64 与两条恢复路径编译后的 C#，包含回绕、进位及溢出。"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X30, UC_ARM64_REG_PC

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('configuration', type=Path)
parser.add_argument('--tool', type=Path, required=True)
parser.add_argument('--probe', action='store_true')
args = parser.parse_args()
config = json.loads(args.configuration.read_text(encoding='utf-8-sig'))
out = ROOT / 'artifacts/condition-projection'
out.mkdir(parents=True, exist_ok=True)
samples = []


def case(name, width, instructions, ssa=False, reject=False, types=None):
    samples.append(dict(Name=name, ReturnType='int32_t', Types=types or [f'int{width}_t'] * 2,
                        Names=['a', 'b'], Instructions=instructions, Ssa=ssa, Reject=reject))


conditions = ['eq', 'ne', 'hs', 'lo', 'mi', 'pl', 'vs', 'vc', 'hi', 'ls', 'ge', 'lt', 'gt', 'le']
for width, reg in [(32, 'w'), (64, 'x')]:
    for op in ['cmp', 'cmn', 'tst', 'adds', 'subs']:
        instruction = f'{op} {reg}0, {reg}1' if op in ['cmp', 'cmn', 'tst'] else f'{op} {reg}0, {reg}0, {reg}1'
        for condition in conditions:
            for ssa in [True, False]:
                for consumer in ['branch', 'set', 'select']:
                    name = f'{"ssa" if ssa else "native"}_{op}{width}_{condition}_{consumer}'
                    tail = [f'b.{condition} .L{name}', 'mov w0, #0', 'ret', f'.L{name}:', 'mov w0, #1'] if consumer == 'branch' else \
                        [f'cset w0, {condition}'] if consumer == 'set' else ['mov w2, #1', 'mov w3, #0', f'csel w0, w2, w3, {condition}']
                    case(name, width, [instruction] + tail, ssa)
for ssa in [True, False]:
    for op in ['cmp', 'cmn', 'tst']:
        case(f'undefined_{op}_{ssa}', 64, [f'{op} x0, x1', 'cset w0, eq'], ssa, True, ['int32_t', 'int64_t'])
        case(f'reference_{op}_{ssa}', 64, [f'{op} x0, x1', 'cset w0, hi'], ssa, True, ['Il2CppObject*', 'int64_t'])
        case(f'reference_equal_{op}_{ssa}', 64, [f'{op} x0, x1', 'b.eq 1f', 'mov w0, #0', 'ret', '1: mov w0, #1'], ssa, True, ['Il2CppObject*', 'int64_t'])
    case(f'clobbered_flags_{ssa}', 64, ['cmp x0, x1', 'mov x0, #0', 'mov x1, #0', 'cset w0, hi'], ssa)
    case(f'zero_extended_flags_{ssa}', 64, ['mov w0, w0', 'cmn x0, x1', 'cset w0, vs'], ssa, types=['int32_t', 'int64_t'])
    case(f'truncated_reference_{ssa}', 32, ['mov w0, w0', 'cmp w0, w1', 'b.eq 1f', 'mov w0, #0', 'ret', '1: mov w0, #1'], ssa, True, ['Il2CppObject*', 'int32_t'])
    case(f'undefined_boolean_{ssa}', 32, ['cmp w0, #0', 'cset w0, ne'], ssa, True, ['bool', 'int64_t'])
    case(f'masked_boolean_{ssa}', 32, ['and w0, w0, #1', 'cmp w0, #0', 'cset w0, ne'], ssa, types=['bool', 'int64_t'])
if args.probe:
    samples = [s for s in samples if s['Name'] == 'ssa_cmn32_eq_branch']
source = '.text\n' + '\n'.join(f'.global {s["Name"]}\n.type {s["Name"]}, %function\n{s["Name"]}:\n' +
    '\n'.join(s['Instructions'] + ['ret']) + f'\n.size {s["Name"]}, .-{s["Name"]}' for s in samples)
(out / 'cases.s').write_text(source, encoding='utf-8')
subprocess.run([config['Clang'], '-target', 'aarch64-linux-gnu', '-c', str(out / 'cases.s'), '-o', str(out / 'cases.o')], check=True)
with (out / 'cases.o').open('rb') as stream:
    elf = ELFFile(stream)
    code = elf.get_section_by_name('.text').data()
    symbols = {s.name: s.entry for s in elf.get_section_by_name('.symtab').iter_symbols() if s.entry['st_info']['type'] == 'STT_FUNC'}
for sample in samples:
    symbol = symbols[sample['Name']]
    sample.update(Offset=symbol['st_value'], Size=symbol['st_size'], Address=0x100000 + symbol['st_value'])
(out / 'cases.bin').write_bytes(code)
(out / 'cases.json').write_text(json.dumps(samples), encoding='utf-8')
(out / 'il2cpp.h').write_text('// Synthetic scalar signatures.\n', encoding='utf-8')
(out / 'script.json').write_text(json.dumps({'ScriptMethod': [dict(Address=s['Address'], Name='ConditionFixture$$' + s['Name'],
    Signature='int32_t ' + s['Name'] + '(' + ', '.join(t + ' ' + n for t, n in zip(s['Types'], s['Names'])) + ');') for s in samples]}), encoding='utf-8')
subprocess.run(['dotnet', str(args.tool.resolve()), 'native-projection', str(args.configuration.resolve()), str(out)], cwd=ROOT, check=True)
rng = random.Random(49173)
edges = [0, 1, 2, 0x7ffffffe, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff]
inputs = [(a, b) for a in edges for b in edges] + [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(96)]
rows = []
stop = 0x100000 + ((len(code) + 4095) & ~4095)
for sample in samples:
    if sample['Reject']:
        continue
    uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    uc.mem_map(0x100000, stop - 0x100000 + 4096)
    uc.mem_write(0x100000, code)
    for a, b in inputs:
        if sample['Types'][0] == 'bool':
            a = (a & ~255) | (a & 1)
        uc.reg_write(UC_ARM64_REG_X0, a)
        uc.reg_write(UC_ARM64_REG_X1, b)
        uc.reg_write(UC_ARM64_REG_X30, stop)
        uc.emu_start(sample['Address'], stop, count=32)
        assert uc.reg_read(UC_ARM64_REG_PC) == stop, sample['Name']
        rows.append(dict(Name=sample['Name'], A=a, B=b, Expected=uc.reg_read(UC_ARM64_REG_X0) & 0xffffffff))
(out / 'observations.json').write_text(json.dumps(rows), encoding='utf-8')
types = {'int32_t': 'int', 'int64_t': 'long'}
arms = [f'"{s["Name"]}" => Recovered.{s["Name"]}(' + ', '.join(f'(({n} & 1) != 0)' if t == 'bool' else f'unchecked(({types[t]}){n})' for t, n in zip(s['Types'], s['Names'])) + ')' for s in samples if not s['Reject']]
fixture = '''using System.Text.Json;
var rows = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(args[0]))!;
foreach (var row in rows)
{
    var a = row.GetProperty("A").GetUInt64(); var b = row.GetProperty("B").GetUInt64();
    var name = row.GetProperty("Name").GetString();
    var actual = name switch { /* ARMS */, _ => throw new Exception(name) };
    if (unchecked((uint)actual) != row.GetProperty("Expected").GetUInt32()) throw new Exception($"{name}: {a:x}/{b:x}: {actual} != {row}");
}
Console.WriteLine($"PASS: {rows.Length} generated C# / ARM64 flag scenarios");
'''
(out / 'Program.cs').write_text(fixture.replace('/* ARMS */', ',\n'.join(arms)), encoding='utf-8')
# TST 的 C/V 恒为零，保留这些分支用于执行对照；仅允许对应的不可达代码警告。
(out / 'ConditionFixture.csproj').write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><ImplicitUsings>enable</ImplicitUsings><NoWarn>CS0162</NoWarn></PropertyGroup></Project>', encoding='utf-8')
subprocess.run(['dotnet', 'restore', str(out / 'ConditionFixture.csproj'), '--source', str(ROOT / 'artifacts')], cwd=ROOT, check=True)
subprocess.run(['dotnet', 'run', '--project', str(out / 'ConditionFixture.csproj'), '-c', 'Release', '--no-restore', '--', str(out / 'observations.json')], cwd=ROOT, check=True)
report = dict(functions=len(samples), rejected=sum(s['Reject'] for s in samples), cases=len(rows),
              codeSha256=hashlib.sha256(code).hexdigest(), generatedSha256=hashlib.sha256((out / 'Recovered.cs').read_bytes()).hexdigest(),
              scope='synthetic ARM64 and compiled SSA/fallback C#; no game runtime claim')
(out / 'report.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
print(json.dumps(report))
