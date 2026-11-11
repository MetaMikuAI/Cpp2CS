param([Parameter(Mandatory=$true)][string]$Root)
$ErrorActionPreference = "Stop"
Get-CimInstance Win32_Process | Where-Object { $_.Name -eq 'Unity.exe' } | Select-Object ProcessId, CommandLine | Format-List
Get-PSDrive ([IO.Path]::GetPathRoot($Root).Substring(0,1)) | Select-Object Used, Free | Format-List
Get-Command python.exe | Select-Object Source | Format-List
