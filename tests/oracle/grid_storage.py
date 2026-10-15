"""对照整个 GridAreaCell；GridPosition 仅作四字节布局输入。"""
import json
from pathlib import Path
import random
import struct
import sys
from machine import Machine

catalog = json.loads(Path(sys.argv[2]).read_text(encoding='utf-8'))
owner, = [t for t in catalog['types'] if t['complete']]
methods = {m['name']:int(m['address'],0) for m in owner['methods']}
assert set(methods) == {'.ctor','get_TilePosition','set_TilePosition','SetPosition'}
machine = Machine(sys.argv[1],catalog['binarySha256'],[*methods.values(),int(catalog['objectConstructorAddress'],0)])
offset = owner['fields'][0]['offset']
randomizer = random.Random(20261016)
values = [0,1,0xffffffff,0x80000000,0x7fffffff,0x80808001,0x7f7f7f00,0x01010101]
values += [randomizer.getrandbits(32) for _ in range(2048)]
rows = []
for value in values:
    before = b'\xa5'*offset+b'\x00'*4+b'\xa5'*12
    machine.cpu.mem_write(machine.memory,before)
    machine.run(methods['.ctor'],[machine.memory])
    assert bytes(machine.cpu.mem_read(machine.memory,len(before))) == before
    machine.run(methods['set_TilePosition'],[machine.memory,value])
    after = bytes(machine.cpu.mem_read(machine.memory,len(before)))
    assert after[:offset] == before[:offset] and after[offset+4:] == before[offset+4:]
    first = machine.run(methods['get_TilePosition'],[machine.memory])[0] & 0xffffffff
    other = randomizer.getrandbits(32)
    machine.run(methods['SetPosition'],[machine.memory,other])
    second = machine.run(methods['get_TilePosition'],[machine.memory])[0] & 0xffffffff
    after = bytes(machine.cpu.mem_read(machine.memory,len(before)))
    assert after[:offset] == before[:offset] and after[offset+4:] == before[offset+4:]
    rows.append({'input':value,'other':other,'setterResult':first,'methodResult':second})
Path(sys.argv[3]).write_text(json.dumps({'binarySha256':machine.digest,'nativeCalls':machine.calls,'rows':rows}),encoding='utf-8')
print(f'PASS native: {len(rows)} rows, {machine.calls} original calls; constructor/getter/private setter/SetPosition')
