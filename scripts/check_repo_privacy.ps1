$credOutput = "protocol=https`nhost=github.com`n" | git credential fill 2>$null
$pat = ($credOutput | Select-String '^password=(.+)$').Matches.Groups[1].Value
$r = Invoke-RestMethod -Uri 'https://api.github.com/repos/JasonShroyer/sgc-second-brain' -Headers @{ Authorization = "token $pat"; 'User-Agent' = 'sgc' }
"private: $($r.private)"
"visibility: $($r.visibility)"
"created: $($r.created_at)"
"pushed: $($r.pushed_at)"
"default_branch: $($r.default_branch)"
"size_kb: $($r.size)"
