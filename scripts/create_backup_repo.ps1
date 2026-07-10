$ErrorActionPreference = 'Stop'
# 1. Pre-flight: any file >90MB would block GitHub push
$big = Get-ChildItem "C:\Users\Jason\sgc-second-brain" -Recurse -File -ErrorAction SilentlyContinue |
  Where-Object { $_.Length -gt 90MB -and $_.FullName -notmatch '\\\.git\\' }
if ($big) { "BLOCKERS (>90MB):"; $big | ForEach-Object { "$($_.FullName): $([math]::Round($_.Length/1MB,1)) MB" } } else { "No oversized files." }

# 2. Get stored GitHub credential via GCM (never printed)
$credInput = "protocol=https`nhost=github.com`n"
$credOutput = $credInput | git credential fill 2>$null
$user = ($credOutput | Select-String '^username=(.+)$').Matches.Groups[1].Value
$pat  = ($credOutput | Select-String '^password=(.+)$').Matches.Groups[1].Value
if (-not $pat) { throw "No stored GitHub credential found." }
"Credential found for user: $user"

# 3. Create private repo (idempotent: 422 if exists)
$headers = @{ Authorization = "token $pat"; Accept = "application/vnd.github+json"; "User-Agent" = "sgc-backup" }
$body = @{ name = "sgc-second-brain"; private = $true; description = "SGC second brain - experiments, insights, wiki (private backup)" } | ConvertTo-Json
try {
  $resp = Invoke-RestMethod -Method Post -Uri "https://api.github.com/user/repos" -Headers $headers -Body $body -ContentType "application/json"
  "CREATED: $($resp.full_name) (private: $($resp.private))"
} catch {
  $code = $_.Exception.Response.StatusCode.value__
  if ($code -eq 422) { "Repo already exists (422) - continuing." } else { throw "API error $code" }
}

# 4. Wire remote + push
Set-Location "C:\Users\Jason\sgc-second-brain"
$existing = git remote
if ($existing -notcontains 'origin') {
  git remote add origin "https://github.com/$user/sgc-second-brain.git"
  "Remote origin added."
} else {
  "Remote origin already present: $(git remote get-url origin)"
}
git push -u origin master 2>&1 | Select-Object -Last 5
"=== BACKUP DONE ==="
