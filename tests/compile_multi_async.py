"""编译生成文件本身，不手写替代方法。"""
import json
import hashlib
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path(sys.argv[1]) if len(sys.argv) == 2 else ROOT / 'artifacts/recovered'
parts = []
for address in ['0x55d684c','0x55d4ad8','0x5bea518']:
    body = json.loads((SOURCE/f'{address}.async-body.json').read_text())
    assert body['CSharp'] and not body['Problems']
    generated = (SOURCE/f'{address}.cs.txt').read_bytes().decode('utf-8')
    assert generated == body['CSharp']
    namespace, owner = body['Source']['Owner'].rsplit('.',1)
    parts.append(f'namespace {namespace} {{ public partial class {owner} {{\n' + generated + '\n} }')
(ROOT/'artifacts/multi-async-generated.cs').write_text('\n'.join(parts),encoding='utf-8')
subprocess.run(['dotnet','run','--project','tests/MultiAsyncOutputFixture','-c','Release','--disable-build-servers'],cwd=ROOT,check=True)
report = ROOT/'artifacts/multi-async-compiled.json'
result = json.loads(report.read_text())
result['generatedSha256'] = hashlib.sha256((ROOT/'artifacts/multi-async-generated.cs').read_bytes()).hexdigest()
result['observationsSha256'] = hashlib.sha256((ROOT/'artifacts/multi-async-observations.json').read_bytes()).hexdigest()
report.write_text(json.dumps(result,indent=2))
