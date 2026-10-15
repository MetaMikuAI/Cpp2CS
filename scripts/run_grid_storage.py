"""重放 GridAreaCell 的导出、恢复、独立编译及原始指令对照。"""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
database = Path(sys.argv[1]).resolve()
output = root / 'artifacts/grid-storage'
exported = database.parent / 'grid-storage'
tool = root / 'src/Cpp2CS/bin/Debug/net10.0/Cpp2CS.dll'
target = root.parent / '.re-jp-pjsk-7.0.0'


def run(*args, stdin=None):
    subprocess.run([str(a) for a in args], cwd=root, stdin=stdin, check=True)


run('dotnet', 'build', 'src/Cpp2CS/Cpp2CS.csproj', '--no-restore', '-p:UseSharedCompilation=false', '-v:quiet')
run('dotnet', tool, 'metadata', target/'DummyDll', 'cases/grid-storage.json', output)
with (output/'requests.jsonl').open(encoding='utf-8') as requests:
    run(sys.executable, '-X', 'utf8', '-u', root/'scripts/ida_probe.py', database, exported, stdin=requests)
run('dotnet', tool, 'recover', output/'metadata.json', exported, output/'recovered')
run('dotnet', 'build', output/'recovered/Recovered.csproj', '-p:NuGetAudit=false', '-p:UseSharedCompilation=false', '-v:quiet')
run(sys.executable, '-X', 'utf8', 'tests/oracle/grid_storage.py', root.parent/'lib/arm64/libil2cpp.so', output/'metadata.json', output/'native.json')
run('dotnet', 'run', '--project', 'tests/GridStorage/GridStorage.csproj', '-p:NuGetAudit=false', '-p:UseSharedCompilation=false', '--', output/'native.json')
print('PASS: GridAreaCell complete; GridPosition layout only; GridAreaData and API chain remain incomplete')
