"""本机驱动：同步小文件、脱离会话启动、查询进度、取回文本。"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('action', choices=('sync', 'probe', 'start', 'status', 'fetch'))
    p.add_argument('--config', type=Path, required=True, help='本机 *.local.json 配置')
    p.add_argument('--run', default='first')
    p.add_argument('--destination', type=Path, help='fetch 的仓库外目录或 *.local.* 目录')
    a = p.parse_args()
    config = json.loads(a.config.read_text(encoding='utf-8'))
    host, root, unity = (config[k] for k in ('host', 'root', 'unity'))
    if not re.fullmatch(r'[A-Za-z0-9_.@-]+', host) or host.startswith('-'):
        p.error('host 必须是 SSH 配置别名或主机名')
    for value in (root, unity):
        if not re.fullmatch(r'[A-Za-z]:[/\\][A-Za-z0-9_ .:/\\-]+', value):
            p.error('Windows 路径包含不支持的字符')
    if not re.fullmatch(r'[A-Za-z0-9_-]+', a.run):
        p.error('run 只接受字母、数字、下划线、短横线')
    root = root.replace('\\', '/').rstrip('/')
    corpus = Path(__file__).resolve().parents[1]
    def remote(script, *args):
        values = ['powershell', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File',
                  root + '/build/' + script, '-Root', root, *args]
        subprocess.run(['ssh', host, values[0] + ' ' + ' '.join('"' + v + '"' for v in values[1:])], check=True)
    if a.action == 'sync':
        # 初次同步的父目录必须存在，scp 创建指定的 corpus 根目录。
        if root.rsplit('/', 1)[-1] != 'corpus':
            p.error('独立远端目录的末级必须为 corpus')
        import tempfile
        import shutil
        with tempfile.TemporaryDirectory(prefix='corpus-sync-') as temp:
            stage = Path(temp) / 'corpus'
            for directory in ('cases', 'unity', 'build'):
                for src in (corpus / directory).rglob('*'):
                    if src.is_file() and '.local.' not in src.name and '__pycache__' not in src.parts:
                        if src.stat().st_size > 5_000_000:
                            p.error(f'拒绝传输超过 5 MB 的文件: {src}')
                        dst = stage / src.relative_to(corpus)
                        dst.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(src, dst)
            inventory = {file.relative_to(stage).as_posix(): hashlib.sha256(file.read_bytes()).hexdigest()
                         for file in sorted(stage.rglob('*')) if file.is_file()}
            (stage / 'source-files.json').write_text(json.dumps(inventory, indent=2), encoding='utf-8')
            subprocess.run(['scp', '-r', str(stage), host + ':' + root.rsplit('/', 1)[0] + '/'], check=True)
    elif a.action == 'start':
        remote('launch.ps1', '-Unity', unity, '-Run', a.run)
    elif a.action == 'probe':
        remote('probe.ps1')
    elif a.action == 'status':
        remote('status.ps1', '-Run', a.run)
    else:
        if a.destination is None:
            p.error('fetch 需要 --destination')
        # 远端先检查固定文本清单的大小；不下载 so、压缩包或整个目录。
        remote('texts.ps1', '-Run', a.run)
        a.destination.mkdir(parents=True, exist_ok=True)
        names = ('build-report.txt', 'symbol-check.txt', 'symbol-check.json', 'manifest.json',
                 'provenance.json', 'cases-cpp.txt', 'arm64-v8a-symbols.txt', 'x86_64-symbols.txt',
                 'arm64-v8a-shapes.txt', 'x86_64-shapes.txt')
        paths = [host + ':' + root + '/runs/' + a.run + '/output/' + name for name in names]
        subprocess.run(['scp', *paths, str(a.destination)], check=True)
        subprocess.run(['scp', host + ':' + root + '/runs/' + a.run + '/archive.json',
                        str(a.destination)], check=True)


if __name__ == '__main__':
    main()
