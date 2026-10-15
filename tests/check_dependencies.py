"""绑定使用原始槽位和方法定义；重复、错配及无效令牌不能降级为名称猜测。"""
import copy
import json
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from dependencies import bind_call, runtime_bindings

runtime = json.loads(Path(sys.argv[1]).read_text(encoding='utf-8'))
owners,slots = runtime_bindings(runtime)
source = next(s for s in runtime['slots'] if s['displayName'].endswith('APICaller<EmptyRequest, SuiteUser>.Call()'))
target, = {s['address'] for s in runtime['specs'] if s['definition'] == source['definition'] and
           s['address'] and s['typeArguments'] and all(a['kind'] == 28 for a in s['typeArguments'])}
info = [{'Address':source['address']}]
bound = bind_call(target,info,runtime,owners,slots)
assert bound['status'] == 'identity-bound' and bound['abi'] == 'unchecked'
assert [x['name'] for x in bound['typeArguments']] == ['Sekai.EmptyRequest','Sekai.SuiteUser']
assert runtime['specs'][source['index']]['address'] == 0
assert bind_call(target,[],runtime,owners,slots)['status'] == 'unresolved'
assert bind_call(target,info*2,runtime,owners,slots)['status'] == 'unresolved'
assert bind_call(1,info,runtime,owners,slots)['reason'] == 'definition-does-not-own-target'
invalid = dict(slots)
invalid[source['address']] = dict(source,valid=False)
assert bind_call(target,info,runtime,owners,invalid)['reason'] == 'invalid-metadata-slot'
wrong = dict(slots)
wrong[source['address']] = dict(source,definition=source['definition']+1)
assert bind_call(target,info,runtime,owners,wrong)['reason'] == 'definition-does-not-own-target'
renamed = copy.deepcopy(runtime)
renamed['definitions'][source['definition']]['owner'] = 'UnrelatedDisplayName'
assert bind_call(target,info,renamed,owners,slots) == bound
print('PASS: 8 shared-call binding checks; zero exported address resolved by definition identity, ABI remains unchecked')
