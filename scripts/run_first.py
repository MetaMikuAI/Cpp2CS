"""重新导出真实方法、恢复 C# 并执行原生差分验证；不安装工具或依赖。"""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
database = Path(sys.argv[1]).resolve()
output = root / 'artifacts/first'
exported = database.parent / 'first'
tool = root / 'src/Cpp2CS/bin/Debug/net10.0/Cpp2CS.dll'
target = root.parent / '.re-jp-pjsk-7.0.0'

def run(*args, stdin=None):
    subprocess.run([str(a) for a in args], cwd=root, stdin=stdin, check=True)

run('dotnet', 'build', 'src/Cpp2CS/Cpp2CS.csproj', '--ignore-failed-sources', '-p:NuGetAudit=false', '-p:UseSharedCompilation=false', '-v:quiet')
run('dotnet', tool, 'metadata', target/'DummyDll', 'cases/first.json', output)
with (output/'requests.jsonl').open(encoding='utf-8') as requests:
    run(sys.executable, '-X', 'utf8', '-u', root/'scripts/ida_probe.py', database, exported, stdin=requests)
run('dotnet', tool, 'recover', output/'metadata.json', exported, output/'recovered')
run('dotnet', 'build', output/'recovered/Recovered.csproj', '-p:NuGetAudit=false', '-p:UseSharedCompilation=false', '-v:quiet')
run(sys.executable, '-X', 'utf8', 'tests/oracle/first.py', root.parent/'lib/arm64/libil2cpp.so', output/'metadata.json', output/'native.json')
run('dotnet', 'run', '--project', 'tests/FirstCases/FirstCases.csproj', '-p:NuGetAudit=false', '-p:UseSharedCompilation=false', '--', output/'native.json')
print('PASS: metadata -> IDA ctree -> managed semantics -> C# -> compile -> native differential execution')
