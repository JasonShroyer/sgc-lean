/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Structure.TemporalConsolidation
import SGC.Structure.ResidualDescent
import SGC.Structure.AttentionGate

/-!
# Temporal Coherence: descent in the active state, no forgetting in memory

The product of the two invariant layers:

* the **consolidation boundary** (`SGC.Structure.TemporalConsolidation`) —
  arbitrary active dynamics cannot corrupt certified memory, which changes
  only through safe extension; and
* the **coherence layer** (`CoherenceDynamics` / `AttentionGate`) — any
  attention policy wrapped in a state-derived energy gate cannot raise the
  active incoherence.

## The theorems

1. **`active_eq_orbit`** — if the active component follows an update rule,
   its trajectory is the orbit of that rule.
2. **`safe_adaptive_consolidation`** — the capstone: an ARBITRARY
   attention-controlled dynamics, gated by energy acceptance, running
   above certified consolidation, yields SIMULTANEOUSLY
   (i)   nonincreasing active incoherence,
   (ii)  lifelong memory preservation, and
   (iii) exact composition of every certified expression at every time.

   arbitrary adaptive controller + energy gate + safe consolidation
     ⟹ coherence descent + lifelong no forgetting.

3. **`coherent_adaptive_consolidation`** — the quantified branch: if the
   active state follows a residual dynamics, the incoherence residual
   VANISHES (`R(A_t) → 0`) while memory is preserved and composition
   stays exact — the system approaches coherence and never forgets.
4. **`gated_system_correct`** — such a system EXISTS: a concrete witness
   whose active state runs any gated attention policy from any initial
   state, with certified memory computing every expression exactly,
   forever.
-/

namespace SGC.Sheaf

open SGC.Coherence Filter

variable {R : Type*} [Ring R] {α Att : Type*}

omit [Ring R] in
/-- If the active component follows an update rule step by step, the whole
    active trajectory is the orbit of that rule from the initial state. -/
theorem active_eq_orbit {D : CoherenceDynamics α}
    {traj : ℕ → TemporalState R α}
    (hactive : ∀ t, (traj (t + 1)).active = D.update ((traj t).active)) :
    ∀ t, (traj t).active = D.orbit ((traj 0).active) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [hactive t, ih, D.orbit_succ]

/-- **The Safe Adaptive Consolidation Theorem** (capstone).

    An arbitrary attention-controlled active dynamics proposes candidates;
    the system accepts only candidates that pass
    (1) the energy acceptance gate, and
    (2) a `Consolidation` safe-extension witness for any memory change.

    Then, for ANY energy `E`, ANY policy `P`, ANY trajectory, and ANY
    certified library installed at time zero:

    1. **coherence descent** — active incoherence never rises:
       `E(A_{t+1}) ≤ E(A_t)`;
    2. **no forgetting** — every stored value is invariant for all time:
       `σ_{M_t}(ι₀ₜ(v)) = σ_{M₀}(v)`;
    3. **exact lifelong composition** — every certified expression
       evaluates to its denotational semantics at every time.

    In compact form: arbitrary adaptive controller + energy gate + safe
    consolidation ⟹ coherence descent + lifelong no forgetting. -/
theorem safe_adaptive_consolidation (E : α → ℝ) (P : AttentionPolicy α Att)
    {traj : ℕ → TemporalState R α}
    (steps : ∀ t, TemporalStep (traj t) (traj (t + 1)))
    (hgate : ∀ t, (traj (t + 1)).active = gatedUpdate E P ((traj t).active))
    {C : CertifiedOps R} {n : ℕ} {ρ : Fin n → R}
    (L₀ : CertifiedLibrary C ρ (traj 0).memory) :
    (∀ t, E ((traj (t + 1)).active) ≤ E ((traj t).active)) ∧
    (∀ t v, (traj t).memory.stored (memEmbedUpTo steps t v) =
      (traj 0).memory.stored v) ∧
    (∀ t (e : Expr R n),
      (traj t).memory.stored ((L₀.upTo steps t).interp e) = evalRing ρ e) :=
  ⟨fun t => by rw [hgate t]; exact gated_descent E P _,
   lifelong_consolidation steps,
   temporal_exact_composition steps L₀⟩

/-- **Coherent adaptive consolidation** (the quantified branch): if the
    active state follows a residual dynamics — quantified descent
    `E(A_t) − E(A_{t+1}) ≥ c·R(A_t)²` — then simultaneously:

    1. the incoherence residual VANISHES: `R(A_t) → 0`;
    2. memory is preserved for all time; and
    3. every certified expression evaluates exactly at every time.

    The active trajectory approaches coherence; the memory never
    forgets. -/
theorem coherent_adaptive_consolidation (D : ResidualDynamics α)
    {traj : ℕ → TemporalState R α}
    (steps : ∀ t, TemporalStep (traj t) (traj (t + 1)))
    (hactive : ∀ t, (traj (t + 1)).active = D.update ((traj t).active))
    {C : CertifiedOps R} {n : ℕ} {ρ : Fin n → R}
    (L₀ : CertifiedLibrary C ρ (traj 0).memory) :
    Tendsto (fun t => D.residual ((traj t).active)) atTop (nhds 0) ∧
    (∀ t v, (traj t).memory.stored (memEmbedUpTo steps t v) =
      (traj 0).memory.stored v) ∧
    (∀ t (e : Expr R n),
      (traj t).memory.stored ((L₀.upTo steps t).interp e) = evalRing ρ e) := by
  refine ⟨?_, lifelong_consolidation steps,
    temporal_exact_composition steps L₀⟩
  have hfun : (fun t => D.residual ((traj t).active)) =
      fun t => D.residual (D.orbit ((traj 0).active) t) :=
    funext fun t => congrArg D.residual (active_eq_orbit hactive t)
  rw [hfun]
  exact D.residual_tendsto_zero ((traj 0).active)

/-! ### Such a system is possible: the gated witness -/

/-- A gated adaptive trajectory: attention proposes, the energy gate
    disposes, certified memory is retained. -/
noncomputable def gatedTrajectory (C : CertifiedOps R) {n : ℕ}
    (ρ : Fin n → R) (E : α → ℝ) (P : AttentionPolicy α Att) (a₀ : α) :
    ℕ → TemporalState R α :=
  plasticTrajectory C ρ fun t => (gatedUpdate E P)^[t] a₀

/-- Every tick of the gated trajectory is a valid temporal step. -/
noncomputable def gatedSteps (C : CertifiedOps R) {n : ℕ} (ρ : Fin n → R)
    (E : α → ℝ) (P : AttentionPolicy α Att) (a₀ : α) :
    ∀ t, TemporalStep (gatedTrajectory C ρ E P a₀ t)
      (gatedTrajectory C ρ E P a₀ (t + 1)) :=
  plasticSteps C ρ _

/-- **Such a system is formally possible**: a concrete continually
    learning system whose active state runs an ARBITRARY gated attention
    policy from an arbitrary initial state, whose active incoherence never
    rises, and whose certified memory computes the exact semantics of
    EVERY expression at EVERY time. -/
theorem gated_system_correct (C : CertifiedOps R) {n : ℕ} (ρ : Fin n → R)
    (E : α → ℝ) (P : AttentionPolicy α Att) (a₀ : α) :
    (∀ t, E ((gatedTrajectory C ρ E P a₀ (t + 1)).active) ≤
      E ((gatedTrajectory C ρ E P a₀ t).active)) ∧
    (∀ t (e : Expr R n),
      ((gatedTrajectory C ρ E P a₀ t).memory).stored
        (((exprLibrary C ρ).upTo (gatedSteps C ρ E P a₀) t).interp e) =
      evalRing ρ e) := by
  constructor
  · intro t
    show E ((gatedUpdate E P)^[t + 1] a₀) ≤ E ((gatedUpdate E P)^[t] a₀)
    rw [Function.iterate_succ_apply']
    exact gated_descent E P _
  · intro t e
    exact plastic_system_correct C ρ _ t e

end SGC.Sheaf
