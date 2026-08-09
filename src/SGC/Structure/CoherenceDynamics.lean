/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Real.Sqrt

/-!
# Coherence Dynamics: the discrete Lyapunov layer

The active state `A_t` of a temporal system is fully plastic: the
consolidation boundary (`SGC.Structure.TemporalConsolidation`) already
guarantees that NOTHING the active dynamics does can corrupt certified
memory.  This module supplies the complementary invariant for the active
side: a **coherence energy** that never rises.

`CoherenceDynamics` is the minimal Lyapunov object:

* `energy : α → ℝ` — a nonnegative incoherence functional `E`;
* `update : α → α` — one tick of active evolution `U`;
* `descent : E(U(a)) ≤ E(a)` — a descent witness.

The theorems are deliberately modest and honest:

1. **`energy_antitone`** — along the orbit `A_{t+1} = U(A_t)`, the sequence
   `E(A_t)` is antitone: self-evolving activity may change the entire
   state, yet the coherence functional never rises.
2. **`energy_le_initial`** — `E(A_t) ≤ E(A_0)` for all `t`.
3. **`energy_tendsto`** — `E(A_t)` converges to a limit `L ≥ 0` (monotone
   and bounded below, hence convergent).

What is NOT claimed: descent alone does not prove that the STATES `A_t`
converge — only the scalar energy does.  Residual convergence needs a
quantified descent inequality (`SGC.Structure.ResidualDescent`), and state
convergence needs compactness/contraction hypotheses beyond this layer.

The energy is completely agnostic about where updates come from; in
particular `update` may be an attention-driven proposal wrapped in an
acceptance gate (`SGC.Structure.AttentionGate`), for which descent holds
by construction.
-/

namespace SGC.Coherence

open Filter

variable {α : Type*}

/-- An abstract coherence dynamics on an active-state space `α`:
    a nonnegative incoherence energy together with an update rule that
    weakly decreases it.  This is a discrete Lyapunov certificate: the
    dynamics carries its own proof of descent. -/
structure CoherenceDynamics (α : Type*) where
  /-- The incoherence energy `E` of an active state. -/
  energy : α → ℝ
  /-- One tick of active evolution `U`. -/
  update : α → α
  /-- Incoherence is nonnegative. -/
  nonneg : ∀ a, 0 ≤ energy a
  /-- The descent witness: every update weakly decreases incoherence. -/
  descent : ∀ a, energy (update a) ≤ energy a

namespace CoherenceDynamics

variable (D : CoherenceDynamics α)

/-- The orbit of the dynamics: `A_t = U^[t](A_0)`. -/
def orbit (a₀ : α) (t : ℕ) : α :=
  D.update^[t] a₀

@[simp] theorem orbit_zero (a₀ : α) : D.orbit a₀ 0 = a₀ :=
  rfl

theorem orbit_succ (a₀ : α) (t : ℕ) :
    D.orbit a₀ (t + 1) = D.update (D.orbit a₀ t) :=
  Function.iterate_succ_apply' D.update t a₀

/-- **Energy never rises**: along any orbit, the coherence energy is an
    antitone function of time.  Self-evolving activity may change the
    entire active state, yet the incoherence functional never increases. -/
theorem energy_antitone (a₀ : α) :
    Antitone fun t : ℕ => D.energy (D.orbit a₀ t) :=
  antitone_nat_of_succ_le fun t => by
    rw [D.orbit_succ]; exact D.descent _

/-- The energy at any time is bounded by the initial energy. -/
theorem energy_le_initial (a₀ : α) (t : ℕ) :
    D.energy (D.orbit a₀ t) ≤ D.energy a₀ :=
  D.energy_antitone a₀ (Nat.zero_le t)

/-- **Energy convergence** (Level 1): the energy sequence `E(A_t)` is
    antitone and bounded below by `0`, hence converges to a limit
    `L ≥ 0`.  This is the honest conclusion of descent alone: the SCALAR
    converges; state convergence requires further hypotheses. -/
theorem energy_tendsto (a₀ : α) :
    ∃ L, 0 ≤ L ∧
      Tendsto (fun t => D.energy (D.orbit a₀ t)) atTop (nhds L) := by
  refine ⟨⨅ t, D.energy (D.orbit a₀ t), le_ciInf fun t => D.nonneg _, ?_⟩
  refine tendsto_atTop_ciInf (D.energy_antitone a₀) ⟨0, ?_⟩
  rintro y ⟨t, rfl⟩
  exact D.nonneg _

end CoherenceDynamics

end SGC.Coherence
