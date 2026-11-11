"""读取 Bee 构建图中的实际 IL2CPP 转换命令。"""
import argparse
import json
from pathlib import Path


def strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for child in value:
            yield from strings(child)
    elif isinstance(value, dict):
        for child in value.values():
            yield from strings(child)


def conversion_commands(bee):
    commands = set()
    for path in bee.glob('*.dag.json'):
        data = json.loads(path.read_text(encoding='utf-8-sig'))
        commands.update(value for value in strings(data) if '--convert-to-cpp' in value)
    return sorted(commands)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('bee', type=Path)
    args = p.parse_args()
    print('\n'.join(conversion_commands(args.bee)))
