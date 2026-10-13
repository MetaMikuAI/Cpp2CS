"""按完整定义清单运行恢复；进程崩溃、超时、缺少入口均保留为结果。"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import queue
import shutil
import subprocess
import threading


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def lines(process, inbox):
    for line in process.stdout:
        inbox.put(line)
    inbox.put("")


def receive(inbox, timeout):
    # 等待外部进程的输出；恢复逻辑错误由子进程直接暴露。
    try:
        return inbox.get(timeout=timeout)
    except queue.Empty:
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("configuration", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--tool", type=Path, help="测试程序 DLL；默认使用 Release 构建")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    dll = (args.tool or root / "tests/Cpp2CS.Tests/bin/Release/net10.0/Cpp2CS.Tests.dll").resolve()
    config = json.loads(args.configuration.read_text(encoding="utf-8-sig"))
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    for key, field in (("Binary", "binarySha256"), ("Metadata", "metadataSha256"),
                       ("Symbols", "symbolsSha256"), ("Header", "headerSha256")):
        if manifest["inputs"][field] is not None:
            assert digest(config[key]) == manifest["inputs"][field], f"输入不匹配：{key}"
    for assembly in manifest["assemblies"]:
        assert digest(Path(config["ManagedAssembly"]).parent / assembly["name"]) == assembly["sha256"]
    args.output.mkdir(parents=True, exist_ok=True)
    provenance = {"manifestSha256": digest(args.manifest), "timeoutSeconds": args.timeout,
                  "binaries": {p.name: digest(p) for p in dll.parent.glob("*.dll")},
                  "runnerSha256": digest(__file__)}
    provenance_file = args.output / "run.json"
    if provenance_file.exists():
        assert json.loads(provenance_file.read_text()) == provenance, "运行器或输入变化，请使用新输出目录"
    else:
        provenance_file.write_text(json.dumps(provenance, indent=2), encoding="utf-8")
    # 固定本次运行的程序，后续构建不能使同一份报告混入不同版本。
    snapshot = args.output / "tool"
    snapshot.mkdir(exist_ok=True)
    for source in dll.parent.iterdir():
        if source.suffix not in (".dll", ".json", ".pdb"):
            continue
        target = snapshot / source.name
        if target.exists():
            assert digest(target) == digest(source), "工具快照已改变"
        else:
            shutil.copyfile(source, target)
    dll = (snapshot / dll.name).resolve()
    results_file = args.output / "results.jsonl"
    results = [json.loads(line) for line in results_file.read_text(encoding="utf-8").splitlines()] if results_file.exists() else []
    done = {r["id"] for r in results}
    assert len(done) == len(results), "结果中存在重复定义"
    process = None
    log = None
    current_assembly = None
    used = 0
    executed = 0
    inbox = queue.Queue()

    def stop():
        if process is not None:
            if process.poll() is None:
                process.kill()
            process.wait()
            process.stdin.close()
            process.stdout.close()
            log.close()

    with results_file.open("a", encoding="utf-8") as output:
        for entry in manifest["methods"]:
            if entry["id"] in done:
                continue
            if args.limit is not None and executed >= args.limit:
                break
            result = {"id": entry["id"], "address": entry["address"], "status": "no-native-entry"}
            if entry["address"] is not None:
                if process is None or process.poll() is not None or current_assembly != entry["assembly"] or used >= 256:
                    stop()
                    current_assembly = entry["assembly"]
                    log_name = f"worker-{len(results):06d}.stderr.txt"
                    log = (args.output / log_name).open("w", encoding="utf-8")
                    process = subprocess.Popen(["dotnet", str(dll), "namespace-worker", str(args.configuration.resolve()),
                                                current_assembly, str((args.output / "sources" / current_assembly).resolve())],
                                               cwd=root, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=log,
                                               text=True, encoding="utf-8", bufsize=1)
                    inbox = queue.Queue()
                    threading.Thread(target=lines, args=(process, inbox), daemon=True).start()
                    ready = receive(inbox, 180)
                    if ready is None or ready.strip() != "READY":
                        stop()
                        raise RuntimeError(f"worker 初始化失败：{log_name}")
                    used = 0
                process.stdin.write(json.dumps({"id": entry["id"], "address": entry["address"]}) + "\n")
                process.stdin.flush()
                line = receive(inbox, args.timeout)
                if line is None:
                    result.update(status="timeout", stderr=log_name)
                    stop()
                    process = None
                elif line == "":
                    result.update(status="crash", exitCode=process.wait(), stderr=log_name)
                else:
                    result = json.loads(line)
                    assert result["id"] == entry["id"], "worker 返回了其他方法的结果"
                used += 1
            output.write(json.dumps(result, ensure_ascii=False) + "\n")
            output.flush()
            results.append(result)
            done.add(entry["id"])
            executed += 1
            if len(results) % 100 == 0 or result["status"] in ("crash", "timeout"):
                print(f"{len(results)}/{len(manifest['methods'])}: {dict(Counter(r['status'] for r in results))}", flush=True)
    stop()
    summary = {"definitions": len(manifest["methods"]), "processed": len(results),
               "pending": len(manifest["methods"]) - len(results), "statuses": dict(Counter(r["status"] for r in results)),
               "routes": dict(Counter(r.get("route", "none") for r in results)),
               "additionalNativeSymbols": len(manifest["additionalSymbols"]),
               "additionalNativeSymbolsStatus": "pending-context-resolution",
               "runtimeValidated": False}
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
