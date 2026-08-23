# Restores the three soundness-repair files from the pinned checkpoint tag
# and verifies the repaired signatures are present. Safe to run anytime:
# it only touches these three files and only restores committed content.
$repo = Split-Path $PSScriptRoot -Parent
$files = @(
  "src/SGC/Bridge/Quantum.lean",
  "src/SGC/Bridge/Recovery.lean",
  "src/SGC/Axioms/GeometryGeneral.lean"
)
git -C $repo checkout checkpoint-2026-08-22-soundness -- $files
$ok = $true
$checks = @{
  "src/SGC/Bridge/Quantum.lean"        = "inner_adjoint_self \(pi_dist : V .+ \(h"
  "src/SGC/Bridge/Recovery.lean"       = "PetzRecoveryMap_spec \(pi_dist : V .+ \(h"
  "src/SGC/Axioms/GeometryGeneral.lean" = "axiom adjoint_pi_spec \(pi_dist : V"
}
foreach ($f in $files) {
  $hit = Select-String -Path (Join-Path $repo $f) -Pattern $checks[$f] -Quiet
  if ($hit) { Write-Output "OK      $f" } else { Write-Output "MISSING $f"; $ok = $false }
}
if ($ok) { Write-Output "All soundness-repair files verified." }
else { Write-Output "VERIFICATION FAILED - inspect manually."; exit 1 }
