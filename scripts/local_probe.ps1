$ErrorActionPreference = 'SilentlyContinue'
"===HOST==="
hostname
"===CPU==="
Get-CimInstance Win32_Processor | ForEach-Object {
  "$($_.Name) | Cores: $($_.NumberOfCores) | Threads: $($_.NumberOfLogicalProcessors)"
}
"===RAM==="
'{0:N2} GB' -f ((Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory/1GB)
"===GPU==="
nvidia-smi --query-gpu=name,memory.total,driver_version,compute_cap --format=csv,noheader 2>&1
"===STORAGE==="
Get-CimInstance Win32_LogicalDisk -Filter 'DriveType=3' | ForEach-Object {
  "$($_.DeviceID) {0:N1} GB free / {1:N1} GB total" -f ($_.FreeSpace/1GB), ($_.Size/1GB)
}
"===NET_ADAPTERS==="
Get-NetAdapter | Where-Object Status -eq 'Up' | ForEach-Object {
  "$($_.Name) | $($_.InterfaceDescription) | $($_.LinkSpeed) | MAC $($_.MacAddress)"
}
"===PYTHON==="
python --version
"===CONDA==="
conda --version
"===TORCH==="
python -c "import torch; print('torch', torch.__version__, '| cuda', torch.version.cuda, '| device', torch.cuda.get_device_name(0) if torch.cuda.is_available() else 'NO CUDA')"
"===GIT==="
git --version
"===ELAN==="
& "$env:USERPROFILE\.elan\bin\elan.exe" --version
& "$env:USERPROFILE\.elan\bin\lake.exe" --version
"===POWERSHELL==="
$PSVersionTable.PSVersion.ToString()
"===PWSH7==="
pwsh --version
"===OS==="
$v = Get-ItemProperty 'HKLM:\SOFTWARE\Microsoft\Windows NT\CurrentVersion'
"$($v.ProductName) | $($v.DisplayVersion) | Build $($v.CurrentBuild).$($v.UBR)"
"===TIMEZONE==="
(Get-TimeZone).Id
"===DONE==="
