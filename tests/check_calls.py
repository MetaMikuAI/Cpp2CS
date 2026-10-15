"""合成调用点使用真实恢复方法体；错误绑定或依赖缺失必须拒绝。"""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
subprocess.run(['dotnet','build','tests/Calls/Calls.csproj','-p:NuGetAudit=false','-p:UseSharedCompilation=false','-v:quiet'], cwd=root, check=True)
command = ['dotnet',str(root/'tests/Calls/bin/Debug/net10.0/Calls.dll')]
for kind, message in [('ambiguous','调用身份不唯一'),('missing-body','缺少已恢复的调用依赖'),('bad-arity','数量不同')]:
    result = subprocess.run(command+[kind,str(root),sys.argv[1]],cwd=root,capture_output=True,encoding='utf-8')
    if result.returncode == 0 or message not in result.stderr:
        raise AssertionError((kind,result.stdout,result.stderr))
    print(kind,'rejected',flush=True)
subprocess.run(command+['emit',str(root),sys.argv[1]],cwd=root,check=True)
subprocess.run(['dotnet','run','--project','tests/CallExecution/CallExecution.csproj','-p:NuGetAudit=false','-p:UseSharedCompilation=false','--',str(root/'artifacts/first/native.json')],cwd=root,check=True)
