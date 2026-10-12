"""真实原始输入的 CLI 集成检查；工具依赖沿用当前环境。"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.stdout.reconfigure(encoding='utf-8')
cli, binary, metadata = (Path(p).resolve() for p in sys.argv[1:4])
success_va, partial_va = sys.argv[4:6]
Path('artifacts').mkdir(exist_ok=True)
workspace = Path(tempfile.mkdtemp(prefix='cli smoke ', dir='artifacts')).resolve()
for source, name in ((binary, 'binary file.so'), (metadata, 'metadata file.dat')):
    shutil.copyfile(source, workspace/name)
(workspace/'native.local.json').write_text('this file must never be read', encoding='utf-8')

def run(*args):
    return subprocess.run(['dotnet', str(cli), *args], cwd=workspace, capture_output=True, text=True, encoding='utf-8')

def check(condition, label):
    assert condition, label
    print('PASS:', label, flush=True)

raw = ['binary file.so', 'metadata file.dat']
first = run(*raw, success_va)
check(first.returncode == 0 and '{' in first.stdout and not first.stderr, '冷启动三参数直接输出 C#，忽略旧配置，支持带空格路径')
check(not (workspace/'artifacts').exists(), '默认不生成诊断产物')
manifests = list((workspace/'.cpp2cs').rglob('inputs.json'))
check(len(manifests) == 1, '首次仅产生一个有效缓存')
provenance = json.loads(manifests[0].read_text())
check(provenance['binarySha256'] == hashlib.sha256(binary.read_bytes()).hexdigest()
      and provenance['metadataSha256'] == hashlib.sha256(metadata.read_bytes()).hexdigest(), '缓存绑定两个实际输入哈希')
marker = manifests[0].parent/'assemblies.json'
timestamp = marker.stat().st_mtime_ns
second = run(*raw, success_va, '--diagnostics', 'reports')
check(second.returncode == 0 and second.stdout == first.stdout and marker.stat().st_mtime_ns == timestamp,
      '缓存复用且诊断选项不改变 C# 输出')
report = json.loads((workspace/'reports'/f'{success_va}.json').read_text(encoding='utf-8'))
check(all(not Path(p).is_absolute() for p in report['inputs'].values())
      and all(not Path(p).is_absolute() for p in report['inputSha256']), '诊断报告不保存本机绝对输入路径')
partial = run(*raw, partial_va)
check(partial.returncode == 3 and '未恢复' in partial.stderr, '未完整恢复返回 3')
for args, label in (([*raw, 'oops'], '非法地址'), (['missing.so', raw[1], success_va], '缺少二进制'),
                    ([raw[0], 'missing.dat', success_va], '缺少 metadata'), ([raw[1], raw[1], success_va], '错误二进制格式'),
                    ([raw[0], raw[0], success_va], '错误 metadata 格式'), ([*raw, '0x1'], '未知方法入口')):
    result = run(*args)
    check(result.returncode == 2 and not result.stdout and len(result.stderr.splitlines()) == 1, label + '：简洁错误且无源码输出')
print('工作目录：', workspace.name)
