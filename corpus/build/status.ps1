param([string]$Root, [string]$Run)
$ErrorActionPreference = "Stop"
$runDir = Join-Path $Root "runs\$Run"
foreach ($name in @('state.txt', 'unity-exit.txt', 'exit.txt', 'archive.json')) {
    $p = Join-Path $runDir $name
    if (Test-Path $p) { "$name : $([IO.File]::ReadAllText($p).Trim())" }
}
$log = Join-Path $runDir 'output\editor.log'
if (Test-Path $log) { Get-Content $log -Tail 4 }
$worker = Join-Path $runDir 'worker.log'
if (Test-Path $worker) { Get-Content $worker -Tail 5 }
$launcher = Join-Path $runDir 'launcher.log'
if (Test-Path $launcher) { Get-Content $launcher -Tail 8 }
