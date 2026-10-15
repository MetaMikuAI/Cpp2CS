"""破坏 ctree 或布局后必须拒绝输出；改变合法公式后必须被原生对照测试检出。"""
import copy
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
catalog = json.loads((root/'artifacts/first/metadata.json').read_text(encoding='utf-8'))
source = Path(sys.argv[1])
tool = root/'src/Cpp2CS/bin/Debug/net10.0/Cpp2CS.dll'
cases = {}
for p in source.glob('*.json'):
    x = json.loads(p.read_text(encoding='utf-8'))
    if 'structured' in x:
        cases[p.name] = x

def prepare(name, documents, metadata):
    directory = root/'artifacts/negative'/name
    directory.mkdir(parents=True, exist_ok=True)
    for file, content in documents.items():
        (directory/file).write_text(json.dumps(content), encoding='utf-8')
    (directory/'metadata.json').write_text(json.dumps(metadata), encoding='utf-8')
    return directory

def recover(directory):
    return subprocess.run(['dotnet',str(tool),'recover',str(directory/'metadata.json'),str(directory),str(directory/'out')],cwd=root,capture_output=True)

mutations = ['unknown_op','field_gap','wrong_hash','ida_warning','wrong_this','wrong_prototype']
for name in mutations:
    documents = copy.deepcopy(cases)
    metadata = copy.deepcopy(catalog)
    method = documents['5208344.json']
    if name == 'unknown_op': method['structured']['nodes'][0]['op'] = 'unsupported'
    if name == 'field_gap': metadata['types'][0]['fields'][0]['offset'] += 1
    if name == 'wrong_hash': method['input_sha256'] = '0'*64
    if name == 'ida_warning': method['warnings'] = [{'ea':'0x5208344','text':'unresolved type'}]
    if name == 'wrong_this': method['structured']['arguments'][0:2] = method['structured']['arguments'][1::-1]
    if name == 'wrong_prototype': method['prototype_applied'] = 'void changed();'
    directory = prepare(name, documents, metadata)
    result = recover(directory)
    assert result.returncode != 0 and not (directory/'out/Recovered.cs').exists(), name
    (directory/'diagnostic.txt').write_bytes(result.stdout+result.stderr)
    print(name, 'rejected')

documents = copy.deepcopy(cases)
for method in documents.values():
    for key in ['pseudocode', 'ctree', 'microcode']:
        method.pop(key, None)
directory = prepare('structured_only', documents, catalog)
assert recover(directory).returncode == 0
assert (directory/'out/Recovered.cs').read_bytes() == (root/'artifacts/first/recovered/Recovered.cs').read_bytes()
print('structured_only matches baseline without pseudocode text')

documents = copy.deepcopy(cases)
method = documents['59015c0.json']
constant, = [n for n in method['structured']['nodes'] if n['op']=='num' and n['number']=='1']
constant['number'] = '2'
directory = prepare('changed_condition', documents, catalog)
assert recover(directory).returncode == 0
result = subprocess.run(['dotnet','run','--project','tests/FirstCases/FirstCases.csproj',
                         '-p:NuGetAudit=false','-p:UseSharedCompilation=false',
                         '-p:RecoveredSource='+str(directory/'out/Recovered.cs'),
                         '--',str(root/'artifacts/first/native.json')],cwd=root,capture_output=True)
assert result.returncode != 0 and b'empty' in result.stderr, result.stdout+result.stderr
(directory/'diagnostic.txt').write_bytes(result.stdout+result.stderr)
print('changed_condition detected by native differential tests')
