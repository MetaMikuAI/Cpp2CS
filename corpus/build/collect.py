"""保留 Bee 的实际输出、裁剪后程序集与命令证据，生成文本清单。"""
import argparse
import hashlib
import json
import re
from commands import conversion_commands
from pathlib import Path
import shutil
import subprocess
import sys


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--unity', type=Path, required=True)
    a = p.parse_args()
    bee = a.project / 'Library' / 'Bee'
    target = a.output / 'artifacts'
    target.mkdir()
    il2cpp = bee / 'artifacts' / 'Android' / 'il2cppOutput'
    shutil.copytree(il2cpp, target / 'il2cppOutput')
    stripped = list(bee.rglob('ManagedStripped'))
    if len(stripped) != 1 or not (stripped[0] / 'Corpus.Cases.dll').is_file():
        raise RuntimeError(f'裁剪后程序集目录不唯一或缺少用例: {stripped}')
    commands = conversion_commands(bee)
    if len(commands) != 1:
        raise RuntimeError(f'预期一次 IL2CPP 转换，实际 {len(commands)}')
    assemblies = re.findall(r'--assembly="([^"]+)"', commands[0])
    if not assemblies:
        raise RuntimeError('转换命令没有程序集输入')
    for assembly in assemblies:
        source = (a.project / assembly).resolve()
        if source.parent != stripped[0].resolve() or not source.is_file():
            raise RuntimeError(f'实际程序集输入不在保留目录中: {source}')
    shutil.copytree(stripped[0], target / 'ManagedStripped')
    evidence = target / 'commands'
    evidence.mkdir()
    for file in bee.rglob('*'):
        if file.is_file() and file.suffix in ('.rsp', '.json'):
            dest = evidence / file.relative_to(bee)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(file, dest)
    ndk = a.unity.parent / 'Data' / 'PlaybackEngines' / 'AndroidPlayer' / 'NDK'
    toolbin = ndk / 'toolchains' / 'llvm' / 'prebuilt' / 'windows-x86_64' / 'bin'
    nm, objdump = toolbin / 'llvm-nm.exe', toolbin / 'llvm-objdump.exe'
    methods = a.output / 'source' / 'cases' / 'methods.json'
    entries = json.loads(methods.read_text(encoding='utf-8'))
    args = [sys.executable, str(Path(__file__).with_name('check_symbols.py')),
            '--methods', str(methods), '--output', str(a.output / 'symbol-check.json')]
    for abi in ('arm64-v8a', 'x86_64'):
        libdir = target / 'il2cppOutput' / 'build' / abi
        for name in ('libil2cpp.so', 'libil2cpp.sym.so', 'libil2cpp.dbg.so'):
            if not (libdir / name).is_file():
                raise RuntimeError(f'缺少产物: {libdir / name}')
        lib = libdir / 'libil2cpp.sym.so'
        symbols = subprocess.check_output([str(nm), '--defined-only', str(lib)], text=True, encoding='utf-8')
        # 仅取用例与支撑方法的文本，避免传输全库符号表。
        prefixes = tuple(m['symbolPrefix'] for m in entries) + ('Support_', 'Initialized_')
        filtered = '\n'.join(line for line in symbols.splitlines() if any(prefix in line for prefix in prefixes))
        symbolfile = a.output / f'{abi}-symbols.txt'
        symbolfile.write_text(filtered + '\n', encoding='utf-8')
        args += ['--symbols', f'{abi}={symbolfile}']
        names = [line.split()[-1] for line in filtered.splitlines()
                 if len(line.split()) == 3 and line.split()[1] in ('t', 'T')
                 and line.split()[-1].startswith(('Guards_', 'Dispatch_', 'TypeChecks_', 'Checks_'))]
        disassembly = subprocess.check_output(
            [str(objdump), '-d', '--no-show-raw-insn',
             '--disassemble-symbols=' + ','.join(names), str(libdir / 'libil2cpp.dbg.so')],
            text=True, encoding='utf-8')
        if not names or any('<' + name + '>:' not in disassembly for name in names):
            raise RuntimeError(f'{abi} 反汇编缺少用例函数体')
        (a.output / f'{abi}-shapes.txt').write_text(disassembly, encoding='utf-8')
    if not list((target / 'il2cppOutput').rglob('global-metadata.dat')):
        raise RuntimeError('缺少 global-metadata.dat')
    with (a.output / 'symbol-check.txt').open('w', encoding='utf-8') as f:
        subprocess.run(args, stdout=f, check=True, encoding='utf-8')
    provenance = {'conversionCommands': commands, 'assemblyInputs': assemblies,
                  'managedSource': str(stripped[0]), 'unity': str(a.unity),
                  'clang': subprocess.check_output([str(toolbin / 'clang++.exe'), '--version'], text=True),
                  'ndk': (ndk / 'source.properties').read_text(encoding='utf-8')}
    (a.output / 'provenance.json').write_text(json.dumps(provenance, indent=2), encoding='utf-8')
    records = []
    for file in sorted(target.rglob('*')):
        if file.is_file():
            with file.open('rb') as f:
                digest = hashlib.sha256()
                for block in iter(lambda: f.read(1024 * 1024), b''):
                    digest.update(block)
            records.append({'path': file.relative_to(a.output).as_posix(), 'bytes': file.stat().st_size,
                            'sha256': digest.hexdigest()})
    (a.output / 'manifest.json').write_text(json.dumps(records, indent=2), encoding='utf-8')
    # 单独提供用例 C++，便于通过慢隧道复核。
    cpp = target / 'il2cppOutput' / 'cpp' / 'Corpus.Cases.cpp'
    shutil.copy2(cpp, a.output / 'cases-cpp.txt')


if __name__ == '__main__':
    main()
