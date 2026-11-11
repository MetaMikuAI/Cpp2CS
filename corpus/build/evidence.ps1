param([string]$Root, [string]$Run)
$ErrorActionPreference = 'Stop'
$runDir = Join-Path $Root "runs\$Run"
$bee = Join-Path $runDir 'project\Library\Bee'
Get-ChildItem $bee -Recurse -Directory -Filter ManagedStripped | Select-Object FullName | Format-List
Get-ChildItem $bee -Recurse -File -Filter *.rsp | ForEach-Object {
    $text = [IO.File]::ReadAllText($_.FullName)
    if ($text -match 'convert-to-cpp') { $_.FullName; $text }
}
$log = Join-Path $runDir 'output\editor.log'
Select-String $log -Pattern 'il2cpp.exe|error CS|error:|Exception|enable-divide' | Select-Object -Last 12 | ForEach-Object { $_.Line }
