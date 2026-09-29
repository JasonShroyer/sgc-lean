/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.GatedController

/-!
# Two-step refinement: lookahead dominates myopia, and exactly when it matters

A chain `q₀ = f₁ ∘ q₁`, `q₁ = f₂ ∘ q₂` with step costs `c₁, c₂ ≥ 0`. Two controllers:

* **myopic** — applies the one-step rule of `GatedController` at each stage: refine to
  `q₁` iff `voi₁ > c₁`; having done so, refine to `q₂` iff `voi₂ > c₂`.
* **lookahead** — plans over the chain: `max (V(q₀), V(q₁) − c₁, V(q₂) − c₁ − c₂)`.

## Results

* `lookahead_ge_myopic` — lookahead never does worse.
* `synergyTrap` := `voi₁ ≤ c₁ ∧ voi₁ + voi₂ > c₁ + c₂` — the first step does not pay on its
  own, but the two steps together do. By `voi_chain`, `voi₁ + voi₂ = voi(q₀ → q₂)`.
* `myopic_lt_lookahead_iff` — **myopia is strictly suboptimal iff the synergy trap holds.**
* `myopic_eq_lookahead_iff` — myopia is optimal iff no synergy trap.
* `regret_of_trap` — in the trap the loss is exactly `voi₁ + voi₂ − c₁ − c₂`.
* `noTrap_of_diminishing` — a sufficient condition for safety: if the second step is worth
  no more per unit cost than the first (`voi₂ · c₁ ≤ voi₁ · c₂`, with `c₁ > 0`), there is no
  trap. Diminishing returns make the one-step rule safe; synergy is exactly increasing returns.

The XOR instance (`voi₁ = 0`, `voi₂ = 1/2`) is the canonical trap for any `c₁ + c₂ < 1/2`.
This module is the formal statement of decision 0080, Part C: the one-step theorems of
`GatedController` are true and are one-step; value telescopes exactly along a chain
(`voi_chain`), which is precisely why a zero first term can hide a profitable second.
-/

noncomputable section

namespace SGC.InformationGeometry.ChainController

open Finset DecisionValue

set_option linter.unusedSectionVars false

variable {Ω β γ δ α : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype α] [Nonempty α]

/-- A two-step chain of refinements with costs. -/
structure Chain (Ω β γ δ : Type*) where
  q₂ : Ω → β
  f₂ : β → γ
  f₁ : γ → δ
  c₁ : ℝ
  c₂ : ℝ
  c₁_nonneg : 0 ≤ c₁
  c₂_nonneg : 0 ≤ c₂

variable (C : Chain Ω β γ δ) (w : Ω → ℝ) (u : α → Ω → ℝ)

def q₁ : Ω → γ := C.f₂ ∘ C.q₂
def q₀ : Ω → δ := C.f₁ ∘ q₁ C

def V₀ : ℝ := value (q₀ C) w u
def V₁ : ℝ := value (q₁ C) w u
def V₂ : ℝ := value C.q₂ w u

/-- Value of the first step. -/
def voi₁ : ℝ := V₁ C w u - V₀ C w u
/-- Value of the second step. -/
def voi₂ : ℝ := V₂ C w u - V₁ C w u

theorem voi₁_eq : voi₁ C w u = voi (q₁ C) C.f₁ w u := rfl
theorem voi₂_eq : voi₂ C w u = voi C.q₂ C.f₂ w u := rfl

/-- **Telescoping** (instance of `voi_chain`): the total value is the sum of the steps. -/
theorem voi_total : voi C.q₂ (C.f₁ ∘ C.f₂) w u = voi₁ C w u + voi₂ C w u := by
  unfold voi₁ voi₂ V₀ V₁ V₂ q₀ q₁ voi
  have h : (C.f₁ ∘ C.f₂) ∘ C.q₂ = C.f₁ ∘ C.f₂ ∘ C.q₂ := rfl
  rw [h]
  ring

theorem voi₁_nonneg : 0 ≤ voi₁ C w u := voi_nonneg (q₁ C) C.f₁ w u
theorem voi₂_nonneg : 0 ≤ voi₂ C w u := voi_nonneg C.q₂ C.f₂ w u

open Classical in
/-- The myopic controller: one-step rule at each stage. -/
def myopic : ℝ :=
  if C.c₁ < voi₁ C w u then max (V₁ C w u - C.c₁) (V₂ C w u - C.c₁ - C.c₂) else V₀ C w u

/-- The lookahead controller: plans over the whole chain. -/
def lookahead : ℝ := max (V₀ C w u) (max (V₁ C w u - C.c₁) (V₂ C w u - C.c₁ - C.c₂))

/-- **Lookahead dominates myopia.** -/
theorem lookahead_ge_myopic : myopic C w u ≤ lookahead C w u := by
  unfold myopic lookahead
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- The synergy trap: the first step does not pay alone, the pair pays together. -/
def synergyTrap : Prop := voi₁ C w u ≤ C.c₁ ∧ C.c₁ + C.c₂ < voi₁ C w u + voi₂ C w u

lemma myopic_of_not_first (h : voi₁ C w u ≤ C.c₁) : myopic C w u = V₀ C w u := by
  unfold myopic
  rw [if_neg (not_lt.mpr h)]

lemma myopic_of_first (h : C.c₁ < voi₁ C w u) :
    myopic C w u = max (V₁ C w u - C.c₁) (V₂ C w u - C.c₁ - C.c₂) := by
  unfold myopic
  rw [if_pos h]

/-- **Myopia is strictly suboptimal iff the synergy trap holds.** -/
theorem myopic_lt_lookahead_iff : myopic C w u < lookahead C w u ↔ synergyTrap C w u := by
  unfold synergyTrap
  by_cases h : C.c₁ < voi₁ C w u
  · rw [myopic_of_first C w u h]
    unfold lookahead
    constructor
    · intro hlt
      exfalso
      have hV : V₀ C w u ≤ max (V₁ C w u - C.c₁) (V₂ C w u - C.c₁ - C.c₂) := by
        have : V₀ C w u < V₁ C w u - C.c₁ := by unfold voi₁ at h; linarith
        exact this.le.trans (le_max_left _ _)
      rw [max_eq_right hV] at hlt
      exact lt_irrefl _ hlt
    · rintro ⟨h1, _⟩
      exact absurd h (not_lt.mpr h1)
  · have h' : voi₁ C w u ≤ C.c₁ := not_lt.mp h
    rw [myopic_of_not_first C w u h']
    unfold lookahead
    have hstep1 : V₁ C w u - C.c₁ ≤ V₀ C w u := by unfold voi₁ at h'; linarith
    constructor
    · intro hlt
      refine ⟨h', ?_⟩
      rcases lt_max_iff.mp hlt with h0 | h0
      · exact absurd h0 (lt_irrefl _)
      · rcases lt_max_iff.mp h0 with h1 | h2
        · exact absurd h1 (not_lt.mpr hstep1)
        · unfold voi₁ voi₂ at *; linarith
    · rintro ⟨_, hpair⟩
      refine lt_max_of_lt_right (lt_max_of_lt_right ?_)
      unfold voi₁ voi₂ at hpair
      linarith

/-- **Myopia is optimal iff there is no synergy trap.** -/
theorem myopic_eq_lookahead_iff : myopic C w u = lookahead C w u ↔ ¬ synergyTrap C w u := by
  rw [← myopic_lt_lookahead_iff]
  constructor
  · intro h; rw [h]; exact lt_irrefl _
  · intro h; exact le_antisymm (lookahead_ge_myopic C w u) (not_lt.mp h)

/-- **The regret in the trap is exactly the net value of the pair.** -/
theorem regret_of_trap (h : synergyTrap C w u) :
    lookahead C w u - myopic C w u = voi₁ C w u + voi₂ C w u - C.c₁ - C.c₂ := by
  obtain ⟨h1, hpair⟩ := h
  rw [myopic_of_not_first C w u h1]
  unfold lookahead
  have hstep1 : V₁ C w u - C.c₁ ≤ V₀ C w u := by unfold voi₁ at h1; linarith
  have hpair' : V₀ C w u < V₂ C w u - C.c₁ - C.c₂ := by unfold voi₁ voi₂ at hpair; linarith
  have hin : max (V₁ C w u - C.c₁) (V₂ C w u - C.c₁ - C.c₂) = V₂ C w u - C.c₁ - C.c₂ :=
    max_eq_right (hstep1.trans hpair'.le)
  rw [hin, max_eq_right hpair'.le]
  unfold voi₁ voi₂
  ring

/-- **Diminishing returns make the one-step rule safe.** If the second step yields no more
value per unit cost than the first, there is no trap. Synergy is increasing returns. -/
theorem noTrap_of_diminishing (hc : 0 < C.c₁)
    (hdim : voi₂ C w u * C.c₁ ≤ voi₁ C w u * C.c₂) : ¬ synergyTrap C w u := by
  rintro ⟨h1, hpair⟩
  -- from voi₁ ≤ c₁: voi₂ · c₁ ≤ voi₁ · c₂ ≤ c₁ · c₂, so voi₂ ≤ c₂; then voi₁ + voi₂ ≤ c₁ + c₂
  have h2 : voi₂ C w u * C.c₁ ≤ C.c₁ * C.c₂ := by
    calc voi₂ C w u * C.c₁ ≤ voi₁ C w u * C.c₂ := hdim
      _ ≤ C.c₁ * C.c₂ := mul_le_mul_of_nonneg_right h1 C.c₂_nonneg
  have h3 : voi₂ C w u ≤ C.c₂ := by
    by_contra hcon
    push_neg at hcon
    have : C.c₂ * C.c₁ < voi₂ C w u * C.c₁ := mul_lt_mul_of_pos_right hcon hc
    linarith
  linarith

end SGC.InformationGeometry.ChainController
