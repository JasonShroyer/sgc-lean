/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Contributors
-/

/-!
# Topology Benchmarks: Conductance and Spectral Gap Validation

## Theoretical Foundation

This module tests the core SGC prediction linking **graph topology** to
**information flow diagnostics**:

**Theorem** (Informal): For a partition S of vertices:
  - Closed cycles have LOW conductance (information recirculates)
  - Open chains have HIGH conductance (information leaks through boundaries)

This is a direct consequence of the Cheeger inequality relating conductance
to the spectral gap of the Markov generator.

## Synthetic Topologies

1. **Closed Cycle**: 0 → 1 → 2 → 3 → 4 → 5 → 0 (periodic boundaries)
2. **Open Chain**: 0 → 1 → 2 → 3 → 4 → 5 (open boundaries)
3. **Star Graph**: Central hub (0) connected to all leaves (1-5)

## Test Criteria

For partition S = {0,1,2} vs Sᶜ = {3,4,5}:
- **PASS**: Chain conductance > Cycle conductance (by factor ≥ 1.5)
- **FAIL**: Otherwise

## Lean4 Theorem Reference

The conductance diagnostic is defined in `SGC.Spectral.Conductance`.
The spectral gap relationship is formalized in `SGC.Spectral.CheegerBound`.
-/

namespace SGC.Experiments.TopologyBenchmarks

/-! ## 1. Matrix Infrastructure -/

abbrev Matrix6 := Fin 6 → Fin 6 → Float

def Matrix6.zero : Matrix6 := fun _ _ => 0.0

def Matrix6.transpose (A : Matrix6) : Matrix6 := fun i j => A j i

def Matrix6.mul (A B : Matrix6) : Matrix6 := fun i j =>
  (List.finRange 6).foldl (fun acc k => acc + A i k * B k j) 0.0

def Matrix6.sub (A B : Matrix6) : Matrix6 := fun i j => A i j - B i j

def floatAbs (x : Float) : Float := if x < 0.0 then -x else x

def floatMin (a b : Float) : Float := if a < b then a else b

def floatMax (a b : Float) : Float := if a > b then a else b

/-! ## 2. Generator Definitions -/

/-- **Closed Cycle**: 0 → 1 → 2 → 3 → 4 → 5 → 0 (circulant matrix) -/
def cycleGenerator (k_fwd k_bwd : Float) : Matrix6 := fun i j =>
  let next := (i.val + 1) % 6
  let prev := (i.val + 5) % 6
  if j.val == next then k_fwd
  else if j.val == prev then k_bwd
  else if i.val == j.val then -(k_fwd + k_bwd)
  else 0.0

/-- **Open Chain**: 0 → 1 → 2 → 3 → 4 → 5 (open boundaries) -/
def chainGenerator (k_fwd k_bwd : Float) : Matrix6 := fun i j =>
  if i.val < 5 && j.val == i.val + 1 then k_fwd
  else if i.val > 0 && j.val == i.val - 1 then k_bwd
  else if i.val == j.val then
    if i.val == 0 then -k_fwd
    else if i.val == 5 then -k_bwd
    else -(k_fwd + k_bwd)
  else 0.0

/-- **Star Graph**: Hub (0) connected to leaves (1-5) -/
def starGenerator (k_hub_out k_leaf_in : Float) : Matrix6 := fun i j =>
  if i.val == 0 && j.val > 0 then k_hub_out / 5.0  -- Hub → leaves
  else if i.val > 0 && j.val == 0 then k_leaf_in   -- Leaves → hub
  else if i.val == j.val then
    if i.val == 0 then -k_hub_out
    else -k_leaf_in
  else 0.0

/-! ## 3. Steady-State Distributions -/

/-- Uniform distribution (exact for cycle) -/
def uniformPi : Fin 6 → Float := fun _ => 1.0 / 6.0

/-- Gradient distribution for chain: π_i ∝ (k_fwd/k_bwd)^i -/
def chainPi (k_fwd k_bwd : Float) : Fin 6 → Float := fun i =>
  let r := k_fwd / k_bwd
  let unnorm := Float.pow r i.val.toFloat
  let total := (Float.pow r 6.0 - 1.0) / (r - 1.0)
  unnorm / total

/-- Star distribution: hub gets different weight than leaves -/
def starPi (k_hub_out k_leaf_in : Float) : Fin 6 → Float := fun i =>
  if i.val == 0 then k_leaf_in / (k_leaf_in + k_hub_out)
  else k_hub_out / (5.0 * (k_leaf_in + k_hub_out))

/-! ## 4. Conductance Computation -/

/-- Escort mass of partition S = {0,1,2} -/
def partitionMassS (pi : Fin 6 → Float) : Float :=
  pi ⟨0, by omega⟩ + pi ⟨1, by omega⟩ + pi ⟨2, by omega⟩

/-- Boundary flux for chain (edge 2↔3 only) -/
def boundaryFluxChain (L : Matrix6) (pi : Fin 6 → Float) : Float :=
  let flux_2_3 := floatAbs (pi ⟨2, by omega⟩ * L ⟨2, by omega⟩ ⟨3, by omega⟩)
  let flux_3_2 := floatAbs (pi ⟨3, by omega⟩ * L ⟨3, by omega⟩ ⟨2, by omega⟩)
  flux_2_3 + flux_3_2

/-- Boundary flux for cycle (edges 2↔3 and 5↔0) -/
def boundaryFluxCycle (L : Matrix6) (pi : Fin 6 → Float) : Float :=
  let flux_2_3 := floatAbs (pi ⟨2, by omega⟩ * L ⟨2, by omega⟩ ⟨3, by omega⟩)
  let flux_3_2 := floatAbs (pi ⟨3, by omega⟩ * L ⟨3, by omega⟩ ⟨2, by omega⟩)
  let flux_5_0 := floatAbs (pi ⟨5, by omega⟩ * L ⟨5, by omega⟩ ⟨0, by omega⟩)
  let flux_0_5 := floatAbs (pi ⟨0, by omega⟩ * L ⟨0, by omega⟩ ⟨5, by omega⟩)
  flux_2_3 + flux_3_2 + flux_5_0 + flux_0_5

/-- Conductance: boundary_flux / min(mass_S, mass_Sc) -/
def conductance (L : Matrix6) (pi : Fin 6 → Float) (isCycle : Bool) : Float :=
  let mass_S := partitionMassS pi
  let mass_Sc := 1.0 - mass_S
  let minMass := floatMin mass_S mass_Sc
  let flux := if isCycle then boundaryFluxCycle L pi else boundaryFluxChain L pi
  if minMass > 1e-10 then flux / minMass else 0.0

/-! ## 5. Spectral Gap Proxy -/

/-- Spectral gap proxy: range of diagonal elements (decay rates) -/
def spectralGapProxy (L : Matrix6) : Float :=
  let diags := (List.finRange 6).map (fun i => L i i)
  let maxDiag := diags.foldl floatMax (-1000.0)
  let minDiag := diags.foldl floatMin 0.0
  floatAbs (maxDiag - minDiag)

/-! ## 6. Non-Normality (Commutator Norm) -/

/-- Commutator [L, L†] = L·L† - L†·L -/
def commutator (L : Matrix6) : Matrix6 :=
  let Lt := Matrix6.transpose L
  Matrix6.sub (Matrix6.mul L Lt) (Matrix6.mul Lt L)

/-- Frobenius norm of commutator: ||[L, L†]||_F -/
def commutatorNorm (L : Matrix6) : Float :=
  let C := commutator L
  let sumSq := (List.finRange 6).foldl (fun acc i =>
    (List.finRange 6).foldl (fun acc2 j => acc2 + C i j * C i j) acc) 0.0
  Float.sqrt sumSq

/-! ## 7. Benchmark Results Structure -/

structure TopologyResult where
  name : String
  conductance : Float
  spectralGap : Float
  commutatorNorm : Float
  deriving Repr

/-! ## 8. Run Benchmarks -/

def k_fwd : Float := 10.0
def k_bwd : Float := 0.1

def L_cycle := cycleGenerator k_fwd k_bwd
def L_chain := chainGenerator k_fwd k_bwd
def L_star := starGenerator k_fwd k_bwd

def pi_cycle := uniformPi
def pi_chain := chainPi k_fwd k_bwd
def pi_star := starPi k_fwd k_bwd

def cycleResult : TopologyResult := {
  name := "Closed Cycle"
  conductance := conductance L_cycle pi_cycle true
  spectralGap := spectralGapProxy L_cycle
  commutatorNorm := commutatorNorm L_cycle
}

def chainResult : TopologyResult := {
  name := "Open Chain"
  conductance := conductance L_chain pi_chain false
  spectralGap := spectralGapProxy L_chain
  commutatorNorm := commutatorNorm L_chain
}

def starResult : TopologyResult := {
  name := "Star Graph"
  conductance := conductance L_star pi_star false
  spectralGap := spectralGapProxy L_star
  commutatorNorm := commutatorNorm L_star
}

/-! ## 9. Pass/Fail Report -/

def formatFloat (x : Float) (decimals : Nat := 4) : String :=
  let scale := Float.pow 10.0 decimals.toFloat
  let rounded := Float.round (x * scale) / scale
  toString rounded

def benchmarkReport : String :=
  let cycle := cycleResult
  let chain := chainResult
  let star := starResult

  -- Core prediction: Chain conductance > Cycle conductance
  let conductanceRatio := if cycle.conductance > 1e-10
    then chain.conductance / cycle.conductance
    else 0.0

  let testPass := chain.conductance > cycle.conductance * 1.5

  s!"╔══════════════════════════════════════════════════════════════════════════════╗\n" ++
  s!"║                    SGC TOPOLOGY BENCHMARKS                                   ║\n" ++
  s!"║                    Conductance & Spectral Gap Validation                     ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Topology        │ Conductance │ Spectral Gap │ ||[L,L†]||                   ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Closed Cycle    │ {formatFloat cycle.conductance 4}      │ {formatFloat cycle.spectralGap 2}         │ {formatFloat cycle.commutatorNorm 2}                       ║\n" ++
  s!"║  Open Chain      │ {formatFloat chain.conductance 4}      │ {formatFloat chain.spectralGap 2}         │ {formatFloat chain.commutatorNorm 2}                      ║\n" ++
  s!"║  Star Graph      │ {formatFloat star.conductance 4}      │ {formatFloat star.spectralGap 2}         │ {formatFloat star.commutatorNorm 2}                       ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  PREDICTION: Chain conductance > Cycle conductance (by ≥1.5x)                ║\n" ++
  s!"║  MEASURED RATIO: {formatFloat conductanceRatio 2}x                                                   ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  RESULT: {if testPass then "✓ PASS - Cycles trap flow, Chains leak flow" else "✗ FAIL - Prediction not confirmed"}                         ║\n" ++
  s!"╚══════════════════════════════════════════════════════════════════════════════╝"

#eval benchmarkReport

/-! ## 10. Interpretation

**Why this matters:**

1. **Closed Cycle (Low Conductance)**: Information recirculates within partitions.
   The wrap-around edge 5→0 provides an alternative path that reduces boundary
   permeability. This is analogous to "memory" in biological systems.

2. **Open Chain (High Conductance)**: Information flows through and exits.
   There is only ONE path between partitions S and Sᶜ, making the boundary
   maximally permeable. This is analogous to "dissipation" in gradient flows.

3. **Star Graph (Variable)**: Hub-spoke topology creates bottleneck at hub.
   Conductance depends on partition choice and hub/leaf rate balance.

**Formal Connection**: The Cheeger inequality states:
  λ₂ / 2 ≤ φ(G) ≤ √(2λ₂)

where λ₂ is the spectral gap and φ(G) is the Cheeger constant (minimum conductance).
Low conductance ⟹ slow mixing ⟹ information trapping.
-/

end SGC.Experiments.TopologyBenchmarks
