param(
    [Parameter(Mandatory=$true)][string]$Root,
    [Parameter(Mandatory=$true)][string]$Unity,
    [Parameter(Mandatory=$true)][ValidatePattern('^[a-zA-Z0-9_-]+$')][string]$Run
)
$ErrorActionPreference = "Stop"
$Root = [IO.Path]::GetFullPath($Root)
if (-not (Test-Path $Unity)) { throw "Unity 不存在" }
$active = @(Get-CimInstance Win32_Process | Where-Object { $_.Name -eq 'Unity.exe' })
if ($active.Count) { $active | Select-Object ProcessId, CommandLine | Format-List; throw "Unity 正在使用，未启动构建" }
$runDir = Join-Path $Root "runs\$Run"
if (Test-Path $runDir) { throw "运行目录已存在，换一个 Run" }
New-Item -ItemType Directory -Path $runDir | Out-Null
$python = (Get-Command python.exe -ErrorAction Stop).Source
$wrapper = Join-Path $runDir 'run.cmd'
$lines = @('@echo off', 'set PYTHONUTF8=1',
    ('"{0}" "{1}\build\worker.py" --root "{1}" --unity "{2}" --run "{3}" > "{4}\worker.log" 2>&1' -f $python, $Root, $Unity, $Run, $runDir),
    ('> "{0}\exit.txt" echo %ERRORLEVEL%' -f $runDir))
[IO.File]::WriteAllLines($wrapper, $lines, [Text.Encoding]::Default)
$command = 'cmd.exe /d /c ""{0}""' -f $wrapper
[IO.File]::WriteAllText((Join-Path $runDir 'launch-command.txt'), $command)
$result = Invoke-CimMethod -ClassName Win32_Process -MethodName Create -Arguments @{CommandLine=$command; CurrentDirectory=$Root}
if ($result.ReturnValue -ne 0) { throw "后台启动失败: $($result.ReturnValue)" }
$result.ProcessId | Set-Content (Join-Path $runDir 'launcher-pid.txt')
"pid=$($result.ProcessId)"
