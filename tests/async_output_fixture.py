import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
plan=json.loads((root/'artifacts/recovered/0x55d9650.async.json').read_text(encoding='utf-8'))
assert not plan['Problems'] and plan['CSharp']
owner=plan['Source']['Owner']; namespace,_,name=owner.rpartition('.')
text='namespace '+namespace+';\npublic static class '+name+'\n{\n'+plan['CSharp']+'}\n'
(root/'tests/AsyncOutputFixture/Recovered.cs').write_text(text,encoding='utf-8')
print('generated fixture from current async IR')
