$ErrorActionPreference = 'SilentlyContinue'
"===OS_BUILD==="
$v = Get-ItemProperty 'HKLM:\SOFTWARE\Microsoft\Windows NT\CurrentVersion'
"$($v.ProductName) | DisplayVersion: $($v.DisplayVersion) | Build: $($v.CurrentBuild).$($v.UBR)"
"===UPTIME==="
$os = Get-CimInstance Win32_OperatingSystem
"LastBoot: $($os.LastBootUpTime) | InstallDate: $($os.InstallDate)"
"===NET_ADAPTERS==="
Get-NetAdapter | ForEach-Object {
  "$($_.Name) | $($_.InterfaceDescription) | $($_.Status) | $($_.LinkSpeed) | MAC $($_.MacAddress)"
}
"===IP_CONFIG==="
Get-NetIPAddress -AddressFamily IPv4 | Where-Object { $_.IPAddress -notlike '127.*' } | ForEach-Object {
  "$($_.InterfaceAlias): $($_.IPAddress)/$($_.PrefixLength) ($($_.PrefixOrigin))"
}
"===POWER_PLAN==="
powercfg /getactivescheme
"===SLEEP_STATES==="
powercfg /a | Select-Object -First 12
"===VIRTUALIZATION==="
"HypervisorPresent: $((Get-CimInstance Win32_ComputerSystem).HypervisorPresent)"
"VirtFirmwareEnabled: $((Get-CimInstance Win32_Processor).VirtualizationFirmwareEnabled)"
"===DEFENDER==="
$mp = Get-MpComputerStatus
"RealTime: $($mp.RealTimeProtectionEnabled) | Exclusions: $((Get-MpPreference).ExclusionPath -join '; ')"
"===GPU_STATE==="
nvidia-smi --query-gpu=temperature.gpu,clocks.sm,clocks.mem,power.draw,utilization.gpu,memory.used --format=csv,noheader
"===GPU_RESIZABLE_BAR==="
nvidia-smi -q | Select-String -Pattern "Resizable|Addressing" | ForEach-Object { $_.Line.Trim() }
"===PAGEFILE==="
Get-CimInstance Win32_PageFileUsage | ForEach-Object { "$($_.Name): current $($_.CurrentUsage) MB / allocated $($_.AllocatedBaseSize) MB" }
"===WINGET==="
winget --version
"===CHOCO==="
choco --version
"===DOTNET==="
dotnet --list-sdks
"===LONG_PATHS==="
"LongPathsEnabled: $((Get-ItemProperty 'HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem').LongPathsEnabled)"
"===DEV_MODE==="
"DevMode: $((Get-ItemProperty 'HKLM:\SOFTWARE\Microsoft\Windows\CurrentVersion\AppModelUnlock' -ErrorAction SilentlyContinue).AllowDevelopmentWithoutDevLicense)"
"===TIME_SYNC==="
w32tm /query /status | Select-String "Source|Last Successful" | ForEach-Object { $_.Line.Trim() }
"TimeZone: $((Get-TimeZone).Id)"
"===FIREWALL==="
Get-NetFirewallProfile | ForEach-Object { "$($_.Name): $($_.Enabled)" }
"===DISK_HEALTH==="
Get-PhysicalDisk | ForEach-Object { "$($_.FriendlyName): $($_.HealthStatus) | Bus: $($_.BusType)" }
"===ONEDRIVE==="
"OneDrive process: $((Get-Process OneDrive -ErrorAction SilentlyContinue) -ne $null)"
"Documents path: $([Environment]::GetFolderPath('MyDocuments'))"
"===C_ROOT==="
Get-ChildItem C:\ -Directory | Select-Object -ExpandProperty Name
"===USERPROFILE==="
$env:USERPROFILE
"===INSTALLED_RELEVANT==="
$keys = @('HKLM:\SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall\*','HKLM:\SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\Uninstall\*')
Get-ItemProperty $keys | Where-Object { $_.DisplayName -match 'NVIDIA|Python|Git|CUDA|Visual|Tailscale|Steam|conda' } | ForEach-Object { $_.DisplayName } | Sort-Object -Unique
"===SSH_SERVER==="
Get-Service sshd | ForEach-Object { "sshd: $($_.Status) / $($_.StartType)" }
"DefaultShell: $((Get-ItemProperty 'HKLM:\SOFTWARE\OpenSSH' -ErrorAction SilentlyContinue).DefaultShell)"
"===WINDOWS_UPDATE==="
"wuauserv: $((Get-Service wuauserv).Status)"
$au = Get-ItemProperty 'HKLM:\SOFTWARE\Policies\Microsoft\Windows\WindowsUpdate\AU' -ErrorAction SilentlyContinue
"NoAutoReboot policy: $($au.NoAutoRebootWithLoggedOnUsers)"
"===DONE==="
