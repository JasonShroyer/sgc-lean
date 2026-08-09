/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Contributors
-/

/-!
# Phase 9: The Quantum Bridge (Non-Hermitian Hamiltonian Map)

This module implements the **Quantum-Classical Isomorphism** at the heart of SGC theory.

## The Insight

Our "Metabolic Core" TCA cycle was a **Normal operator** ([L, L†] = 0) because it was a
perfect ring with uniform steady-state. To see genuine SGC effects (transient growth,
pseudo-criticality), we map to the **Non-Hermitian Hamiltonian** picture.

## The Mapping

Given a stochastic generator L with steady-state distribution π, define:
  - S = diag(√π)
  - H_eff = S⁻¹ L S

**Key Result:**
- If L satisfies **Detailed Balance** → H_eff is **Hermitian** (real eigenvalues)
- If L is **NESS** (non-equilibrium) → H_eff is **Non-Hermitian** (complex eigenvalues)

## The Skin Effect

For non-Hermitian systems, eigenstates are sensitive to boundary conditions.
We test this by comparing:
- **Periodic** (ring): Standard TCA cycle
- **Open** (chain): Cut one link

The spectral shift reveals the **topological content** of the driven system.

## References

- Hatano-Nelson model (1996): Non-Hermitian localization
- SGC "Quantum Extensions" paper: Classical-quantum bridge via similarity transform
-/

namespace SGC.Quantum.HatanoNelson

/-! ## 1. Float-Based Matrix Infrastructure (6×6) -/

abbrev Matrix6x6 := Fin 6 → Fin 6 → Float

def matZero : Matrix6x6 := fun _ _ => 0.0

def matAdd (A B : Matrix6x6) : Matrix6x6 := fun i j => A i j + B i j

def matSub (A B : Matrix6x6) : Matrix6x6 := fun i j => A i j - B i j

def matMul (A B : Matrix6x6) : Matrix6x6 := fun i j =>
  (List.finRange 6).foldl (fun acc k => acc + A i k * B k j) 0.0

def matTranspose (A : Matrix6x6) : Matrix6x6 := fun i j => A j i

def matScale (c : Float) (A : Matrix6x6) : Matrix6x6 := fun i j => c * A i j

def diagMat (v : Fin 6 → Float) : Matrix6x6 := fun i j =>
  if i == j then v i else 0.0

def floatAbs (x : Float) : Float := if x < 0.0 then -x else x

def floatSqrt (x : Float) : Float := x.sqrt

/-! ## 2. Steady-State Distribution -/

def uniformPi : Fin 6 → Float := fun _ => 1.0 / 6.0

def sqrtPi (pi_dist : Fin 6 → Float) : Fin 6 → Float := fun i => floatSqrt (pi_dist i)

def invSqrtPi (pi_dist : Fin 6 → Float) : Fin 6 → Float := fun i =>
  let s := floatSqrt (pi_dist i)
  if s > 1e-10 then 1.0 / s else 0.0

/-! ## 3. The Similarity Transform: L → H_eff -/

/-- Transform stochastic generator L to effective Hamiltonian H_eff = S⁻¹ L S
    where S = diag(√π). For detailed-balance systems, H_eff is symmetric (Hermitian). -/
def toEffectiveHamiltonian (L : Matrix6x6) (pi_dist : Fin 6 → Float) : Matrix6x6 :=
  let S := diagMat (sqrtPi pi_dist)
  let Sinv := diagMat (invSqrtPi pi_dist)
  matMul Sinv (matMul L S)

/-! ## 4. Hermiticity Diagnostic -/

/-- Measure the asymmetry of H_eff: ||H - H†||_F / ||H||_F
    If H is Hermitian (symmetric for real matrices), this is 0. -/
def asymmetryNorm (H : Matrix6x6) : Float :=
  let Ht := matTranspose H
  let diff := matSub H Ht
  let normDiff := (List.finRange 6).foldl (fun acc i =>
    (List.finRange 6).foldl (fun acc2 j =>
      let x := diff i j
      acc2 + x * x) acc) 0.0
  let normH := (List.finRange 6).foldl (fun acc i =>
    (List.finRange 6).foldl (fun acc2 j =>
      let x := H i j
      acc2 + x * x) acc) 0.0
  if normH > 1e-10 then floatSqrt normDiff / floatSqrt normH else 0.0

/-- Check if matrix is approximately symmetric (Hermitian for real) -/
def isApproxHermitian (H : Matrix6x6) (tol : Float := 1e-6) : Bool :=
  asymmetryNorm H < tol

/-! ## 5. TCA Cycle Generators -/

/-- Ring topology (Periodic Boundary Conditions): states 0→1→2→3→4→5→0 -/
def tcaGeneratorPeriodic (k_fwd k_bwd : Float) : Matrix6x6 := fun i j =>
  let i_val := i.val
  let j_val := j.val
  let next := (i_val + 1) % 6
  let prev := (i_val + 5) % 6
  if j_val == next then k_fwd
  else if j_val == prev then k_bwd
  else if i_val == j_val then -(k_fwd + k_bwd)
  else 0.0

/-- Chain topology (Open Boundary Conditions): Cut the 5→0 and 0→5 links -/
def tcaGeneratorOpen (k_fwd k_bwd : Float) : Matrix6x6 := fun i j =>
  let i_val := i.val
  let j_val := j.val
  if i_val == 5 && j_val == 0 then 0.0  -- Cut forward link
  else if i_val == 0 && j_val == 5 then 0.0  -- Cut backward link
  else
    let next := (i_val + 1) % 6
    let prev := (i_val + 5) % 6
    if j_val == next then k_fwd
    else if j_val == prev then k_bwd
    else if i_val == j_val then
      -- Adjust diagonal: endpoints have one fewer connection
      if i_val == 0 then -k_fwd  -- State 0: only forward to 1
      else if i_val == 5 then -k_bwd  -- State 5: only backward to 4
      else -(k_fwd + k_bwd)
    else 0.0

/-! ## 6. Spectral Analysis (Approximate) -/

/-- Trace of matrix -/
def matTrace (A : Matrix6x6) : Float :=
  (List.finRange 6).foldl (fun acc i => acc + A i i) 0.0

/-- Sum of absolute off-diagonal elements (Gershgorin bound indicator) -/
def offDiagonalSum (A : Matrix6x6) : Float :=
  (List.finRange 6).foldl (fun acc i =>
    (List.finRange 6).foldl (fun acc2 j =>
      if i == j then acc2 else acc2 + floatAbs (A i j)) acc) 0.0

/-- Gershgorin spectral bound: max_i |a_ii| + sum_{j≠i} |a_ij| -/
def gershgorinBound (A : Matrix6x6) : Float :=
  (List.finRange 6).foldl (fun maxVal i =>
    let diag := floatAbs (A i i)
    let offDiag := (List.finRange 6).foldl (fun acc j =>
      if i == j then acc else acc + floatAbs (A i j)) 0.0
    let bound := diag + offDiag
    if bound > maxVal then bound else maxVal) 0.0

/-! ## 7. Skin Effect Diagnostic -/

/-- The "Skin Effect" manifests as a spectral shift when changing boundary conditions.
    For Hermitian systems, the spectrum is robust. For Non-Hermitian NESS, it's sensitive. -/
structure SkinEffectResult where
  spectrumPeriodic : Float  -- Spectral radius estimate (periodic)
  spectrumOpen : Float      -- Spectral radius estimate (open)
  spectralShift : Float     -- |λ_periodic - λ_open| / |λ_periodic|
  asymmetryPeriodic : Float -- How non-Hermitian is H_eff (periodic)
  asymmetryOpen : Float     -- How non-Hermitian is H_eff (open)
  deriving Repr

def computeSkinEffect (k_fwd k_bwd : Float) (pi_dist : Fin 6 → Float) : SkinEffectResult :=
  let L_periodic := tcaGeneratorPeriodic k_fwd k_bwd
  let L_open := tcaGeneratorOpen k_fwd k_bwd
  let H_periodic := toEffectiveHamiltonian L_periodic pi_dist
  let H_open := toEffectiveHamiltonian L_open pi_dist
  let spec_p := gershgorinBound H_periodic
  let spec_o := gershgorinBound H_open
  let shift := if floatAbs spec_p > 1e-10 then floatAbs (spec_p - spec_o) / floatAbs spec_p else 0.0
  {
    spectrumPeriodic := spec_p
    spectrumOpen := spec_o
    spectralShift := shift
    asymmetryPeriodic := asymmetryNorm H_periodic
    asymmetryOpen := asymmetryNorm H_open
  }

/-! ## 8. Experiment Runner -/

structure QuantumBridgeResult where
  name : String
  k_fwd : Float
  k_bwd : Float
  fluxRatio : Float
  isDetailedBalance : Bool
  H_asymmetry : Float  -- ||H - H†|| / ||H||
  skinEffect : SkinEffectResult
  interpretation : String
  deriving Repr

def runQuantumExperiment (name : String) (k_fwd k_bwd : Float) : QuantumBridgeResult :=
  let pi_dist := uniformPi
  let isDB := floatAbs (k_fwd - k_bwd) < 1e-6
  let L := tcaGeneratorPeriodic k_fwd k_bwd
  let H := toEffectiveHamiltonian L pi_dist
  let asymm := asymmetryNorm H
  let skin := computeSkinEffect k_fwd k_bwd pi_dist
  let interp := if isDB then
    "DETAILED BALANCE: H_eff is Hermitian (symmetric). No skin effect expected."
  else if asymm < 0.01 then
    "WEAK NESS: H_eff nearly Hermitian. Minimal topological effects."
  else
    "STRONG NESS: H_eff is Non-Hermitian! Skin effect and spectral sensitivity expected."
  {
    name := name
    k_fwd := k_fwd
    k_bwd := k_bwd
    fluxRatio := k_fwd / k_bwd
    isDetailedBalance := isDB
    H_asymmetry := asymm
    skinEffect := skin
    interpretation := interp
  }

/-! ## 9. Display Functions -/

def formatFloat (x : Float) (decimals : Nat := 4) : String :=
  let scale := Float.pow 10.0 decimals.toFloat
  let rounded := Float.round (x * scale) / scale
  toString rounded

def resultToString (r : QuantumBridgeResult) : String :=
  s!"╔══════════════════════════════════════════════════════════════╗\n" ++
  s!"║  QUANTUM BRIDGE: {r.name}\n" ++
  s!"╠══════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Flux Parameters:\n" ++
  s!"║    k_fwd = {formatFloat r.k_fwd 1}  |  k_bwd = {formatFloat r.k_bwd 1}  |  ratio = {formatFloat r.fluxRatio 1}\n" ++
  s!"║\n" ++
  s!"║  Detailed Balance: {if r.isDetailedBalance then "YES (Equilibrium)" else "NO (NESS)"}\n" ++
  s!"║\n" ++
  s!"║  H_eff Asymmetry: ||H - H†||/||H|| = {formatFloat r.H_asymmetry}\n" ++
  s!"║    → {if r.H_asymmetry < 0.01 then "HERMITIAN (real eigenvalues)" else "NON-HERMITIAN (complex eigenvalues possible)"}\n" ++
  s!"║\n" ++
  s!"║  SKIN EFFECT DIAGNOSTIC:\n" ++
  s!"║    Spectral radius (Periodic): {formatFloat r.skinEffect.spectrumPeriodic}\n" ++
  s!"║    Spectral radius (Open):     {formatFloat r.skinEffect.spectrumOpen}\n" ++
  s!"║    Spectral Shift:             {formatFloat (r.skinEffect.spectralShift * 100.0 ) 2}%\n" ++
  s!"║    Asymmetry (Periodic):       {formatFloat r.skinEffect.asymmetryPeriodic}\n" ++
  s!"║    Asymmetry (Open):           {formatFloat r.skinEffect.asymmetryOpen}\n" ++
  s!"║\n" ++
  s!"║  INTERPRETATION:\n" ++
  s!"║    {r.interpretation}\n" ++
  s!"╚══════════════════════════════════════════════════════════════╝"

def showMatrix (name : String) (M : Matrix6x6) : String :=
  let rows := (List.finRange 6).map fun i =>
    let cols := (List.finRange 6).map fun j => formatFloat (M i j) 3
    String.intercalate "  " cols
  s!"{name}:\n" ++ String.intercalate "\n" rows

/-! ## 10. Run Experiments -/

def deadCase := runQuantumExperiment "DEAD (Detailed Balance)" 1.0 1.0
def moderateCase := runQuantumExperiment "MODERATE (Weak NESS)" 10.0 1.0
def aliveCase := runQuantumExperiment "ALIVE (Strong NESS)" 100.0 1.0

#eval resultToString deadCase
#eval resultToString moderateCase
#eval resultToString aliveCase

/-! ## 11. Matrix Inspection -/

def L_dead := tcaGeneratorPeriodic 1.0 1.0
def L_alive := tcaGeneratorPeriodic 100.0 1.0
def H_dead := toEffectiveHamiltonian L_dead uniformPi
def H_alive := toEffectiveHamiltonian L_alive uniformPi

#eval showMatrix "L (Dead - Stochastic Generator)" L_dead
#eval showMatrix "H_eff (Dead - Effective Hamiltonian)" H_dead
#eval s!"H_dead asymmetry: {formatFloat (asymmetryNorm H_dead)}"

#eval showMatrix "L (Alive - Stochastic Generator)" L_alive
#eval showMatrix "H_eff (Alive - Effective Hamiltonian)" H_alive
#eval s!"H_alive asymmetry: {formatFloat (asymmetryNorm H_alive)}"

/-! ## 12. Summary Table -/

def quantumBridgeSummary : String :=
  let header :=
    "╔════════════════════════════════════════════════════════════════════════════╗\n" ++
    "║                    QUANTUM BRIDGE SUMMARY                                   ║\n" ++
    "║                    SGC Phase 9: Hatano-Nelson Mapping                       ║\n" ++
    "╠════════════════════════════════════════════════════════════════════════════╣\n" ++
    "║  Case        │ Ratio │ H Asymmetry │ Spectral Shift │ Quantum Property      ║\n" ++
    "╠════════════════════════════════════════════════════════════════════════════╣\n"
  let deadRow :=
    s!"║  DEAD        │   1.0 │ {formatFloat deadCase.H_asymmetry 4}      │ {formatFloat (deadCase.skinEffect.spectralShift * 100) 2}%          │ HERMITIAN (Stable)    ║\n"
  let modRow :=
    s!"║  MODERATE    │  10.0 │ {formatFloat moderateCase.H_asymmetry 4}      │ {formatFloat (moderateCase.skinEffect.spectralShift * 100) 2}%          │ NON-HERMITIAN         ║\n"
  let aliveRow :=
    s!"║  ALIVE       │ 100.0 │ {formatFloat aliveCase.H_asymmetry 4}      │ {formatFloat (aliveCase.skinEffect.spectralShift * 100) 2}%          │ NON-HERMITIAN         ║\n"
  let footer :=
    "╠════════════════════════════════════════════════════════════════════════════╣\n" ++
    "║  CONCLUSION: Flux ratio controls the Non-Hermitian character of H_eff.     ║\n" ++
    "║  - Dead (r=1): H_eff symmetric → Hermitian → Real eigenvalues              ║\n" ++
    "║  - Alive (r≫1): H_eff asymmetric → Non-Hermitian → Complex eigenvalues     ║\n" ++
    "║  The Quantum Bridge is OPEN: Stochastic NESS ↔ Non-Hermitian Hamiltonian   ║\n" ++
    "╚════════════════════════════════════════════════════════════════════════════╝"
  header ++ deadRow ++ modRow ++ aliveRow ++ footer

#eval quantumBridgeSummary

end SGC.Quantum.HatanoNelson
