/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Structure.CoherenceDynamics

/-!
# The Attention Gate: descent by construction, for ANY policy

Attention enters the formal system as a **proposal/controller, not as a
source of truth**.  An `AttentionPolicy` is completely arbitrary:

* `attend : α → Att` — compute an attention value from the current state
  (scores, precisions, saliency — any self-evolved, zero-parameter
  function of state and residual geometry);
* `propose : Att → α → α` — an attention-derived candidate update.

The **energy acceptance gate** wraps the proposal:

  `A_{t+1} = Â_{t+1}  if E(Â_{t+1}) ≤ E(A_t),  else  A_t`.

The point of this module is the quantifier order of `gated_descent`:

  **for EVERY energy `E` and EVERY policy `P`, descent holds.**

No assumption is made about where the attention came from, whether it is
learned, random, adversarial, or self-modifying.  The gate supplies the
cybernetic invariant; the policy is free.  `AttentionPolicy.gated`
packages any gated policy as a `CoherenceDynamics`, importing the whole
Lyapunov layer (energy antitone, convergence) for free.
-/

namespace SGC.Coherence

variable {α Att : Type*}

/-- An arbitrary attention policy: a state-derived attention value and an
    attention-derived proposal.  NO structural assumptions — this is the
    plastic, exploratory, self-tuning component. -/
structure AttentionPolicy (α Att : Type*) where
  /-- Compute attention from the current active state. -/
  attend : α → Att
  /-- Propose a candidate next state from attention and current state. -/
  propose : Att → α → α

namespace AttentionPolicy

/-- The raw (ungated) proposal `Â_{t+1} = U_{π(A_t)}(A_t)`. -/
def proposal (P : AttentionPolicy α Att) (a : α) : α :=
  P.propose (P.attend a) a

end AttentionPolicy

/-- The energy acceptance gate: accept the attention-derived proposal iff
    it does not increase the coherence energy; otherwise hold the current
    state. -/
noncomputable def gatedUpdate (E : α → ℝ) (P : AttentionPolicy α Att)
    (a : α) : α :=
  if E (P.proposal a) ≤ E a then P.proposal a else a

/-- An improving proposal is accepted. -/
theorem gatedUpdate_accepts {E : α → ℝ} {P : AttentionPolicy α Att} {a : α}
    (h : E (P.proposal a) ≤ E a) : gatedUpdate E P a = P.proposal a :=
  if_pos h

/-- A regressing proposal is rejected: the state holds. -/
theorem gatedUpdate_rejects {E : α → ℝ} {P : AttentionPolicy α Att} {a : α}
    (h : ¬ E (P.proposal a) ≤ E a) : gatedUpdate E P a = a :=
  if_neg h

/-- **Descent by construction**: for EVERY energy and EVERY attention
    policy — learned, random, adversarial, self-modifying — the gated
    update never increases the energy. -/
theorem gated_descent (E : α → ℝ) (P : AttentionPolicy α Att) (a : α) :
    E (gatedUpdate E P a) ≤ E a := by
  unfold gatedUpdate
  split_ifs with h
  · exact h
  · exact le_rfl

/-- Any attention policy, wrapped in the energy gate, IS a coherence
    dynamics: the entire Lyapunov layer applies to it. -/
noncomputable def AttentionPolicy.gated (P : AttentionPolicy α Att)
    (E : α → ℝ) (hE : ∀ a, 0 ≤ E a) : CoherenceDynamics α where
  energy := E
  update := gatedUpdate E P
  nonneg := hE
  descent := gated_descent E P

/-- **Gated attention never raises incoherence**: along the gated orbit of
    ANY attention policy, the energy sequence is antitone.  The attention
    process may evolve freely; the state-derived acceptance gate supplies
    the invariant. -/
theorem gated_energy_antitone (E : α → ℝ) (hE : ∀ a, 0 ≤ E a)
    (P : AttentionPolicy α Att) (a₀ : α) :
    Antitone fun t : ℕ => E ((gatedUpdate E P)^[t] a₀) :=
  (P.gated E hE).energy_antitone a₀

/-- The gated energy of ANY policy converges. -/
theorem gated_energy_tendsto (E : α → ℝ) (hE : ∀ a, 0 ≤ E a)
    (P : AttentionPolicy α Att) (a₀ : α) :
    ∃ L, 0 ≤ L ∧
      Filter.Tendsto (fun t => E ((gatedUpdate E P)^[t] a₀))
        Filter.atTop (nhds L) :=
  (P.gated E hE).energy_tendsto a₀

end SGC.Coherence
