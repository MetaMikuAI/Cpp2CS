"""后台构建；每次使用独立项目与输出，完整保留生成链输入和输出。"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def stage(root, project, output):
    inventory = json.loads((root / 'source-files.json').read_text(encoding='utf-8'))
    if not inventory:
        raise RuntimeError('源码清单为空')
    for relative, digest in inventory.items():
        path = Path(relative)
        if path.is_absolute() or '..' in path.parts or path.parts[0] not in ('cases', 'unity', 'build'):
            raise RuntimeError(f'非法源码路径: {relative}')
        source = root / path
        if sha256(source) != digest:
            raise RuntimeError(f'源码同步不完整: {relative}')
        snapshot = output / 'source' / path
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, snapshot)
        if path.parts[0] == 'unity':
            destination = project / Path(*path.parts[1:])
        elif path.parts[0] == 'cases':
            destination = project / 'Assets' / 'Corpus' / 'Cases' / Path(*path.parts[1:])
        else:
            continue
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
    shutil.copy2(root / 'source-files.json', output / 'source' / 'source-files.json')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--unity', type=Path, required=True)
    p.add_argument('--run', required=True)
    a = p.parse_args()
    root = a.root.resolve()
    run = root / 'runs' / a.run
    # launch.ps1 已独占创建运行目录；不覆盖历史产物。
    project, output = run / 'project', run / 'output'
    output.mkdir()
    stage(root, project, output)
    for key, directory in (('GRADLE_USER_HOME', 'gradle'), ('UPM_CACHE_ROOT', 'upm'), ('TEMP', 'temp'), ('TMP', 'temp')):
        path = root / 'cache' / directory
        path.mkdir(parents=True, exist_ok=True)
        os.environ[key] = str(path)
    (run / 'state.txt').write_text('building\n', encoding='utf-8')
    result = subprocess.run([str(a.unity), '-batchmode', '-nographics', '-quit',
                             '-projectPath', str(project), '-buildTarget', 'Android',
                             '-executeMethod', 'CorpusBuild.Android', '-corpusOut', str(output),
                             '-logFile', str(output / 'editor.log')])
    (run / 'unity-exit.txt').write_text(str(result.returncode), encoding='utf-8')
    if result.returncode:
        (run / 'state.txt').write_text('unity-failed\n', encoding='utf-8')
        return result.returncode
    (run / 'state.txt').write_text('collecting\n', encoding='utf-8')
    subprocess.run([sys.executable, str(output / 'source' / 'build' / 'collect.py'), '--project', str(project),
                    '--output', str(output), '--unity', str(a.unity)], check=True)
    archive = run / 'corpus-artifacts.zip'
    (run / 'state.txt').write_text('packing\n', encoding='utf-8')
    with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED, compresslevel=6, allowZip64=True) as z:
        for path in sorted(output.rglob('*')):
            if path.is_file() and path.suffix != '.apk' and not path.name.endswith('.symbols.zip'):
                z.write(path, path.relative_to(output))
    info = {'path': str(archive), 'bytes': archive.stat().st_size,
            'sha256': sha256(archive)}
    (run / 'archive.json').write_text(json.dumps(info, indent=2), encoding='utf-8')
    (run / 'state.txt').write_text('complete\n', encoding='utf-8')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
