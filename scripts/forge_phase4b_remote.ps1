Start-Transcript -Path C:\forge\runs\phase4b.log -Force
$env:Path = "$env:USERPROFILE\.elan\bin;$env:Path"
Set-Location C:\forge\lean4-projects
"=== FETCH UPDATED BUNDLE ==="
git fetch C:\forge\transfer\sgc-lean2.bundle cantor-layer-wip 2>&1 | Select-Object -Last 2
git reset --hard FETCH_HEAD 2>&1 | Select-Object -Last 1
git log --oneline -1
"=== LAKE BUILD (16C) ==="
$t1 = Get-Date
lake build 2>&1 | Select-Object -Last 8
"BUILD EXIT: $LASTEXITCODE"
"BUILD MINUTES: $([math]::Round(((Get-Date) - $t1).TotalMinutes, 1))"
"=== PHASE4B COMPLETE ==="
Stop-Transcript
