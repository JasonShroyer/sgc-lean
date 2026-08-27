<#
  publish_formalization.ps1
  Refresh the public formalization-only archive branch (`formalization` on
  `origin` = github.com/JasonShroyer/sgc-lean) from the current working tree.

  The archive contains ONLY the Lean formalization:
    src/, test/, lakefile.lean, lean-toolchain, lake-manifest.json,
    LICENSE, README.md (branch-local), .gitignore (branch-local),
    scripts/AxiomAudit.lean, .github/workflows/build.yml (branch-local).
  Everything else (experiments, papers, reports, decisions, agentic infra)
  stays private by construction: files are copied into a clean worktree,
  never filtered out of it.

  Safety gates (run before publishing):
    1. lake build must be green.
    2. The headline axiom audit (scripts/AxiomAudit.lean) must pass.

  Usage:  powershell -File scripts/publish_formalization.ps1 -Message "..."
#>
param(
  [Parameter(Mandatory = $true)][string]$Message,
  [string]$Branch = 'formalization',
  [string]$Remote = 'origin'
)
$ErrorActionPreference = 'Stop'
$repo = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$wt = Join-Path $env:TEMP 'sgc-formalization-publish'

# Gate 1: green build
Push-Location $repo
try {
  & "$env:USERPROFILE\.elan\bin\lake.exe" build
  if ($LASTEXITCODE -ne 0) { throw 'lake build failed - not publishing.' }
  # Gate 2: headline axiom audit
  & "$env:USERPROFILE\.elan\bin\lake.exe" env lean scripts/AxiomAudit.lean
  if ($LASTEXITCODE -ne 0) { throw 'Headline axiom audit failed - not publishing.' }
} finally { Pop-Location }

# Fresh worktree on the archive branch
if (Test-Path $wt) { git -C $repo worktree remove --force $wt }
git -C $repo fetch $Remote $Branch
git -C $repo worktree add $wt $Branch

# Mirror the whitelisted formalization content (removes files deleted upstream)
robocopy "$repo\src"  "$wt\src"  /MIR /NFL /NDL /NJH /NJS | Out-Null
if ($LASTEXITCODE -ge 8) { throw "robocopy src failed" }
robocopy "$repo\test" "$wt\test" /MIR /NFL /NDL /NJH /NJS | Out-Null
if ($LASTEXITCODE -ge 8) { throw "robocopy test failed" }
foreach ($f in 'lakefile.lean', 'lean-toolchain', 'lake-manifest.json', 'LICENSE',
               'THEORY.md') {
  Copy-Item (Join-Path $repo $f) $wt -Force
}
Copy-Item (Join-Path $repo 'scripts\AxiomAudit.lean') (Join-Path $wt 'scripts\AxiomAudit.lean') -Force
# NOTE: README.md, .gitignore, .github/workflows/build.yml are branch-local
# and maintained on the archive branch itself - do not overwrite them here.

# Commit + push
git -C $wt add -A
$pending = git -C $wt status --short
if (-not $pending) { Write-Host 'Archive already up to date - nothing to publish.'; git -C $repo worktree remove $wt; exit 0 }
$src = git -C $repo rev-parse --short HEAD
git -C $wt commit -m "$Message" -m "Snapshot of local HEAD @ $src. Local verification: lake build green; headline axiom audit passed."
git -C $wt push $Remote $Branch
git -C $repo worktree remove $wt
Write-Host "Published formalization archive to $Remote/$Branch."
