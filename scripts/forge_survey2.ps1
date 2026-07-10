"===PSVERSION==="
$PSVersionTable.PSVersion.ToString()
"===WSL==="
wsl --status 2>&1
wsl --list --verbose 2>&1
"===RAM_DETAIL==="
Get-CimInstance Win32_PhysicalMemory | ForEach-Object {
  "Slot $($_.BankLabel): $($_.Capacity/1GB) GB $($_.Speed) MT/s $($_.Manufacturer)"
}
"===GPU_PCIE==="
nvidia-smi --query-gpu=pcie.link.gen.max,pcie.link.gen.current,pcie.link.width.max,pcie.link.width.current --format=csv,noheader 2>&1
"===NVIDIA_SDK==="
if (Test-Path "C:\Program Files\NVIDIA Corporation") { Get-ChildItem "C:\Program Files\NVIDIA Corporation" -Name } else { "No NVIDIA Corp dir" }
"===ENV_PATH==="
$env:Path -split ';' | Where-Object { $_ -match 'cuda|python|conda|git|lean' }
"===DISK_DETAIL==="
Get-PhysicalDisk | ForEach-Object {
  "$($_.FriendlyName) $($_.MediaType) $([math]::Round($_.Size/1GB,1))GB"
}
"===DONE==="
