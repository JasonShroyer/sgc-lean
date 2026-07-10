$ErrorActionPreference = 'Continue'
"=== 0.1 TIMEZONE + NTP ==="
Set-TimeZone -Id "Mountain Standard Time"
w32tm /config /syncfromflags:manual /manualpeerlist:"time.windows.com" /update 2>&1
Restart-Service w32time -Force
Start-Sleep -Seconds 2
w32tm /resync /force 2>&1
"TZ now: $((Get-TimeZone).Id) | Time now: $(Get-Date)"

"=== 0.2 POWER PLAN ==="
powercfg /setactive 8c5e7fda-e8bf-4a96-9a85-a6e23a8c635c 2>&1
powercfg /change standby-timeout-ac 0
powercfg /change hibernate-timeout-ac 0
powercfg /change monitor-timeout-ac 15
powercfg /hibernate off
powercfg /getactivescheme

"=== 0.3 LONG PATHS ==="
Set-ItemProperty 'HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem' -Name LongPathsEnabled -Value 1
"LongPathsEnabled: $((Get-ItemProperty 'HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem').LongPathsEnabled)"

"=== 0.4 WINDOWS UPDATE ACTIVE HOURS ==="
Set-ItemProperty 'HKLM:\SOFTWARE\Microsoft\WindowsUpdate\UX\Settings' -Name ActiveHoursStart -Value 8 -Type DWord
Set-ItemProperty 'HKLM:\SOFTWARE\Microsoft\WindowsUpdate\UX\Settings' -Name ActiveHoursEnd -Value 2 -Type DWord
"ActiveHours: $((Get-ItemProperty 'HKLM:\SOFTWARE\Microsoft\WindowsUpdate\UX\Settings').ActiveHoursStart)-$((Get-ItemProperty 'HKLM:\SOFTWARE\Microsoft\WindowsUpdate\UX\Settings').ActiveHoursEnd)"

"=== 0.5 WORK ROOT ==="
New-Item -ItemType Directory -Path C:\forge, C:\forge\runs, C:\forge\datasets, C:\forge\tools -Force | Out-Null
"C:\forge tree: $((Get-ChildItem C:\forge -Directory).Name -join ', ')"

"=== 0.6 DEFENDER EXCLUSIONS ==="
Add-MpPreference -ExclusionPath 'C:\forge'
Add-MpPreference -ExclusionPath "$env:USERPROFILE\miniconda3"
"Exclusions: $((Get-MpPreference).ExclusionPath -join '; ')"

"=== 0.7 DIRECT LINK STATIC IP ==="
$existing = Get-NetIPAddress -InterfaceAlias 'Ethernet' -AddressFamily IPv4 -ErrorAction SilentlyContinue | Where-Object { $_.IPAddress -eq '10.10.10.2' }
if (-not $existing) {
  New-NetIPAddress -InterfaceAlias 'Ethernet' -IPAddress 10.10.10.2 -PrefixLength 30 -ErrorAction Continue | Out-Null
}
Get-NetIPAddress -InterfaceAlias 'Ethernet' -AddressFamily IPv4 | ForEach-Object { "Ethernet: $($_.IPAddress)/$($_.PrefixLength)" }
"=== PHASE0 DONE ==="
