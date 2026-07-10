Start-Transcript -Path C:\forge\runs\phase34.log -Force
$ErrorActionPreference = 'Continue'

"=== GIT IDENTITY ==="
git config --global user.name "JasonShroyer"
git config --global user.email "jasonshroyer@live.com"
git config --global core.longpaths true

"=== CLONE FROM BUNDLES ==="
Set-Location C:\forge
if (-not (Test-Path C:\forge\lean4-projects)) {
  git clone C:\forge\transfer\sgc-lean.bundle lean4-projects 2>&1 | Select-Object -Last 2
}
Set-Location C:\forge\lean4-projects
git checkout cantor-layer-wip 2>&1 | Select-Object -Last 1
git log --oneline -1
git remote set-url origin https://github.com/JasonShroyer/thermodynamic-intelligence-engine.git

Set-Location C:\forge
if (-not (Test-Path C:\forge\sgc-second-brain)) {
  git clone C:\forge\transfer\second-brain.bundle sgc-second-brain 2>&1 | Select-Object -Last 2
}
Set-Location C:\forge\sgc-second-brain
git log --oneline -1
git remote set-url origin https://github.com/JasonShroyer/sgc-second-brain.git

"=== ELAN INSTALL ==="
if (-not (Test-Path "$env:USERPROFILE\.elan\bin\elan.exe")) {
  Invoke-WebRequest https://elan.lean-lang.org/elan-init.ps1 -OutFile C:\forge\tools\elan-init.ps1
  & C:\forge\tools\elan-init.ps1 -NoPrompt 1
}
$env:Path = "$env:USERPROFILE\.elan\bin;$env:Path"
elan --version
Get-Content C:\forge\lean4-projects\lean-toolchain

"=== MATHLIB CACHE GET ==="
Set-Location C:\forge\lean4-projects
$t0 = Get-Date
lake exe cache get 2>&1 | Select-Object -Last 5
"CACHE MINUTES: $([math]::Round(((Get-Date) - $t0).TotalMinutes, 1))"

"=== LAKE BUILD (16C) ==="
$t1 = Get-Date
lake build 2>&1 | Select-Object -Last 8
"BUILD EXIT: $LASTEXITCODE"
"BUILD MINUTES: $([math]::Round(((Get-Date) - $t1).TotalMinutes, 1))"
"=== PHASE34 COMPLETE ==="
Stop-Transcript
