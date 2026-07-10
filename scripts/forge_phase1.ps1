$ErrorActionPreference = 'Continue'
"=== PHASE1 START $(Get-Date) ==="
"--- git ---"
winget install --id Git.Git -e --accept-package-agreements --accept-source-agreements --silent 2>&1 | Select-Object -Last 3
"--- pwsh7 ---"
winget install --id Microsoft.PowerShell -e --accept-package-agreements --accept-source-agreements --silent 2>&1 | Select-Object -Last 3
"--- miniconda ---"
winget install --id Anaconda.Miniconda3 -e --scope user --accept-package-agreements --accept-source-agreements --silent 2>&1 | Select-Object -Last 3
"=== VERIFY ==="
& "C:\Program Files\Git\cmd\git.exe" --version
& "C:\Program Files\PowerShell\7\pwsh.exe" --version
& "$env:USERPROFILE\miniconda3\Scripts\conda.exe" --version
"=== PHASE1 DONE $(Get-Date) ==="
