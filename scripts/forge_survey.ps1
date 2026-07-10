$ErrorActionPreference = 'SilentlyContinue'
"===OS==="
(Get-WmiObject Win32_OperatingSystem).Caption
"===CPU==="
Get-CimInstance Win32_Processor | ForEach-Object {
  "$($_.Name) | Cores: $($_.NumberOfCores) | Threads: $($_.NumberOfLogicalProcessors) | Base: $($_.MaxClockSpeed)MHz"
}
"===RAM==="
$ram = (Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory
'{0:N2} GB' -f ($ram/1GB)
"===GPU==="
nvidia-smi --query-gpu=name,memory.total,driver_version,compute_cap,power.limit --format=csv,noheader 2>&1
"===GPUDETAIL==="
nvidia-smi -L 2>&1
"===STORAGE==="
Get-CimInstance Win32_LogicalDisk -Filter 'DriveType=3' | ForEach-Object {
  "$($_.DeviceID) {0:N1} GB free / {1:N1} GB total" -f ($_.FreeSpace/1GB), ($_.Size/1GB)
}
"===MOTHERBOARD==="
Get-CimInstance Win32_BaseBoard | ForEach-Object {
  "$($_.Manufacturer) $($_.Product) (Serial: $($_.SerialNumber))"
}
"===PYTHON==="
python --version 2>&1
py --version 2>&1
"===CUDA==="
nvcc --version 2>&1
"===CONDA==="
conda --version 2>&1
"===PIP==="
pip --version 2>&1
"===GIT==="
git --version 2>&1
"===LEAN==="
where.exe lean 2>&1
where.exe lake 2>&1
"===TAILSCALE==="
tailscale status 2>&1 | Select-Object -First 5
"===NVIDIA_LIBS==="
where.exe nvcuda.dll 2>&1
[System.Environment]::Is64BitOperatingSystem
"===DONE==="
