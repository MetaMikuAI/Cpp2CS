param([string]$Root, [string]$Run)
$ErrorActionPreference = "Stop"
$runDir = Join-Path $Root "runs\$Run"
$names = @('build-report.txt','symbol-check.txt','symbol-check.json','manifest.json','provenance.json','cases-cpp.txt','arm64-v8a-symbols.txt','x86_64-symbols.txt','arm64-v8a-shapes.txt','x86_64-shapes.txt')
$files = @($names | ForEach-Object { Get-Item (Join-Path $runDir "output\$_") })
$files += Get-Item (Join-Path $runDir 'archive.json')
foreach ($f in $files) { if ($f.Length -gt 5000000) { throw "文本超过传输上限: $($f.Name)" }; "$($f.Name) $($f.Length)" }
