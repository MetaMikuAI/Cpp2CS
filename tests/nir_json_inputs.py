"""通过独立 CLI 进程核对 NIR JSON 必填字段及结构错误。"""
import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dll", type=Path)
    parser.add_argument("module", type=Path)
    args = parser.parse_args()
    module = json.loads(args.module.read_text(encoding="utf-8-sig"))

    def run(value):
        return subprocess.run(["dotnet", str(args.dll), "validate-nir"],
                              input=value if isinstance(value, str) else json.dumps(value),
                              text=True, encoding="utf-8", capture_output=True)

    valid = run(module)
    assert valid.returncode == 0 and json.loads(valid.stdout)["isValid"]
    checks = 1
    for field in ("signature", "blocks", "entry", "id"):
        missing = deepcopy(module)
        del missing["functions"][0][field]
        result = run(missing)
        assert result.returncode != 0 and "JsonException" in result.stderr
        checks += 1
    duplicate = json.dumps(module).replace('"version":', '"version":"duplicate", "version":', 1)
    result = run(duplicate)
    assert result.returncode != 0 and "JsonException" in result.stderr
    checks += 1
    for mutation in ("function", "block", "operation", "signature-type"):
        invalid = deepcopy(module)
        if mutation == "function":
            invalid["functions"][0] = None
        elif mutation == "block":
            invalid["functions"][0]["blocks"][0] = None
        elif mutation == "operation":
            invalid["functions"][0]["blocks"][0]["operations"] = [None]
        else:
            invalid["functions"][0]["signature"]["parameters"] = [None]
        result = run(invalid)
        assert result.returncode == 1 and not json.loads(result.stdout)["isValid"] and not result.stderr
        checks += 1
    print(json.dumps({"checks": checks, "passed": True}))


if __name__ == "__main__":
    main()
