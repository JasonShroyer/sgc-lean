/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.CoarseContraction
import SGC.InformationGeometry.EstimatedDecision

/-!
# The decision horizon: certified decisions from a leaky coarse model

Two independent stacks meet here.

* **Coarse-graining** (`Bridge/CoarseContraction`): for a stationary rate generator `L`,
  a partition `P` with leakage `ε = ‖(I−Π)LΠ‖_π`, and block-constant initial density `f₀`,
  `‖e^{tL}f₀ − e^{tL̄}f₀‖_π ≤ t·ε·‖f₀‖_π`.
* **Decisions under estimation error** (`InformationGeometry/EstimatedDecision`): if the
  law an agent plans with is within L¹ distance `r` of the true law and utilities are bounded
  by `M`, a refinement whose estimated value of information clears `cost + 2Mr` is
  profitable under the truth, and one whose estimated VOI plus `2Mr` is below `cost` is not.

The bridge is one inequality: for laws `p = π·f`, `p̂ = π·f̂` with `Σπ = 1`,

  `‖p − p̂‖₁ = Σ π|f − f̂| ≤ ‖f − f̂‖_π`   (Cauchy–Schwarz),

so the coarse model's predicted law is within `t·ε·‖f₀‖_π` of the truth in L¹.

**Reading.** A *consolidated memory* is the stationary law conditioned on a macrostate:
`p₀ = π(·|B)`, with block-constant density `f₀ = 1_B/π̄(B)` and `‖f₀‖_π = 1/√π̄(B)`
(`norm_pi_blockDensity`). The agent evolves it with the quotient model. The theorems
below say exactly when a refine/stop decision taken from that prediction at horizon `t`
is certified under the true dynamics: the operator-norm radius is `t·ε/√π̄(B)`. (The
`1/√π̄(B)` penalty is a property of this worst-case bound, not of the actual error: the
orbit radius of §6 is essentially independent of `π̄(B)`.) The band between the two
certificates is *unresolved*, not "must refine".

**What is and is not assumed.** `ε` is a known upper bound on the leakage; the decision
model is the finite one of `DecisionValue` (observation `q`, coarsening `f`, bounded
utilities). Density evolution `p_t = π·e^{tL}f₀` is the forward Kolmogorov law for
reversible chains (`law_evolution_of_reversible`); for non-reversible chains the same
statements hold with the adjoint generator and the adjoint leakage `‖ΠL(I−Π)‖_π`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SGC.Bridge.DecisionHorizon

open Finset Matrix NormedSpace
open SGC.Approximate SGC.Bridge.DefectHorizonBridge SGC.Bridge.CoarseContraction
open SGC.InformationGeometry.DecisionValue SGC.InformationGeometry.EstimatedDecision
open SGC.InformationGeometry.ContinuousTimeKernel (IsGenerator)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)

/-! ## §1. Laws, densities, and the L¹ ↔ L²(π) bridge -/

/-- The law with density `f` relative to `π`. -/
def lawOf (f : V → ℝ) : V → ℝ := fun x => pi_dist x * f x

omit hπ in
/-- **Cauchy–Schwarz bridge**: `Σ π|g| ≤ ‖g‖_π` when `Σ π = 1`. -/
lemma sum_pi_abs_le_norm_pi (hπ0 : ∀ x, 0 ≤ pi_dist x) (hsum : ∑ x, pi_dist x = 1)
    (g : V → ℝ) : ∑ x, pi_dist x * |g x| ≤ norm_pi pi_dist g := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (pi_dist x)) (fun x => Real.sqrt (pi_dist x) * |g x|)
  have e1 : ∀ x, Real.sqrt (pi_dist x) * (Real.sqrt (pi_dist x) * |g x|) = pi_dist x * |g x| := by
    intro x; rw [← mul_assoc, Real.mul_self_sqrt (hπ0 x)]
  have e2 : ∀ x, Real.sqrt (pi_dist x) ^ 2 = pi_dist x := fun x => Real.sq_sqrt (hπ0 x)
  have e3 : ∀ x, (Real.sqrt (pi_dist x) * |g x|) ^ 2 = pi_dist x * g x * g x := by
    intro x; rw [mul_pow, Real.sq_sqrt (hπ0 x), sq_abs]; ring
  simp only [e1, e2, e3, hsum, one_mul] at hcs
  have hnn : 0 ≤ ∑ x, pi_dist x * |g x| :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hπ0 x) (abs_nonneg _)
  unfold norm_pi norm_sq_pi inner_pi
  calc ∑ x, pi_dist x * |g x| = Real.sqrt ((∑ x, pi_dist x * |g x|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (∑ x, pi_dist x * g x * g x) := Real.sqrt_le_sqrt hcs

omit hπ in
/-- The L¹ distance between two laws is at most the `π`-norm of the density difference. -/
lemma l1Error_lawOf_le (hπ0 : ∀ x, 0 ≤ pi_dist x) (hsum : ∑ x, pi_dist x = 1) (f g : V → ℝ) :
    l1Error (lawOf pi_dist f) (lawOf pi_dist g) ≤ norm_pi pi_dist (f - g) := by
  unfold l1Error lawOf
  have : ∀ x, |pi_dist x * f x - pi_dist x * g x| = pi_dist x * |(f - g) x| := by
    intro x
    rw [← mul_sub, abs_mul, abs_of_nonneg (hπ0 x)]
    rfl
  simp_rw [this]
  exact sum_pi_abs_le_norm_pi pi_dist hπ0 hsum (f - g)

/-! ## §2. Consolidated memory: the block-conditional density -/

variable (P : Partition V)

/-- Density of `π(·|B)` relative to `π`: `1_B / π̄(B)`. -/
def blockDensity (B : P.Quot) : V → ℝ :=
  fun x => if P.quot_map x = B then 1 / pi_bar P pi_dist B else 0

lemma blockDensity_blockConstant (B : P.Quot) :
    blockDensity pi_dist P B = CoarseProjector P pi_dist hπ (blockDensity pi_dist P B) := by
  symm
  apply CoarseProjector_fixes_block_constant
  intro x y hxy
  unfold blockDensity
  have : P.quot_map x = P.quot_map y := Quotient.eq'.mpr hxy
  rw [this]

include hπ in
/-- The consolidated law is a probability law: `Σ_x π(x)·1_B(x)/π̄(B) = 1`. -/
lemma lawOf_blockDensity_sum (B : P.Quot) : ∑ x, lawOf pi_dist (blockDensity pi_dist P B) x = 1 := by
  unfold lawOf blockDensity
  have hpos := pi_bar_pos P hπ B
  have : ∀ x, pi_dist x * (if P.quot_map x = B then 1 / pi_bar P pi_dist B else 0) =
      (if P.quot_map x = B then pi_dist x else 0) / pi_bar P pi_dist B := by
    intro x; split_ifs
    · rw [mul_one_div]
    · rw [mul_zero, zero_div]
  simp_rw [this, ← Finset.sum_div, ← pi_bar_eq_sum_class]
  exact div_self hpos.ne'

include hπ in
/-- **The price of a rare macrostate**: `‖1_B/π̄(B)‖²_π = 1/π̄(B)`. -/
lemma norm_sq_pi_blockDensity (B : P.Quot) :
    norm_sq_pi pi_dist (blockDensity pi_dist P B) = 1 / pi_bar P pi_dist B := by
  unfold norm_sq_pi inner_pi blockDensity
  have hpos := pi_bar_pos P hπ B
  have : ∀ x, pi_dist x * (if P.quot_map x = B then 1 / pi_bar P pi_dist B else 0) *
      (if P.quot_map x = B then 1 / pi_bar P pi_dist B else 0) =
      (if P.quot_map x = B then pi_dist x else 0) / (pi_bar P pi_dist B * pi_bar P pi_dist B) := by
    intro x; split_ifs
    · field_simp
    · simp
  simp_rw [this, ← Finset.sum_div, ← pi_bar_eq_sum_class]
  field_simp

include hπ in
lemma norm_pi_blockDensity (B : P.Quot) :
    norm_pi pi_dist (blockDensity pi_dist P B) = 1 / Real.sqrt (pi_bar P pi_dist B) := by
  unfold norm_pi
  rw [norm_sq_pi_blockDensity pi_dist hπ P B, Real.sqrt_div' _ (pi_bar_pos P hπ B).le, Real.sqrt_one]

/-! ## §3. The coarse model's law is L¹-close to the truth -/

variable [Nonempty V] (L : Matrix V V ℝ)

/-- The true law at horizon `t` from density `f₀` (reversible reading; see §5). -/
def trueLaw (t : ℝ) (f₀ : V → ℝ) : V → ℝ := lawOf pi_dist (HeatKernelMap L t f₀)

/-- The coarse model's predicted law at horizon `t`. -/
def coarseLaw (t : ℝ) (f₀ : V → ℝ) : V → ℝ :=
  lawOf pi_dist (HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)

/-- **L¹ decision radius of a leaky coarse model**:
`‖p_t − p̂_t‖₁ ≤ t · ε · ‖f₀‖_π` for block-constant `f₀`. -/
theorem l1Error_coarseLaw_le (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (hsum : ∑ x, pi_dist x = 1) (t : ℝ) (ht : 0 ≤ t)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    l1Error (trueLaw pi_dist L t f₀) (coarseLaw pi_dist hπ P L t f₀) ≤
      t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) * norm_pi pi_dist f₀ := by
  unfold trueLaw coarseLaw
  refine le_trans (l1Error_lawOf_le pi_dist (fun x => (hπ x).le) hsum _ _) ?_
  exact trajectory_closure_bound_stationary pi_dist hπ P L hL hstat t ht f₀ hf₀

/-- Consolidated-memory form: radius `t · ε / √π̄(B)`. -/
theorem l1Error_coarseLaw_block_le (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (hsum : ∑ x, pi_dist x = 1) (t : ℝ) (ht : 0 ≤ t) (B : P.Quot) :
    l1Error (trueLaw pi_dist L t (blockDensity pi_dist P B))
        (coarseLaw pi_dist hπ P L t (blockDensity pi_dist P B)) ≤
      t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) / Real.sqrt (pi_bar P pi_dist B) := by
  have h := l1Error_coarseLaw_le pi_dist hπ P L hL hstat hsum t ht _
    (blockDensity_blockConstant pi_dist hπ P B)
  rw [norm_pi_blockDensity pi_dist hπ P B] at h
  have e : t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) * (1 / Real.sqrt (pi_bar P pi_dist B))
      = t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) / Real.sqrt (pi_bar P pi_dist B) := by ring
  rw [e] at h
  exact h

/-! ## §4. The certificates -/

variable {β γ α : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
  [Fintype α] [Nonempty α]

/-- **Refine certificate.** If the coarse model's estimated value of information at
horizon `t` exceeds `cost + 2M·t·ε·‖f₀‖_π`, then under the **true** law the refined
observation, acted on by the policy optimal for the coarse prediction, beats even the
optimal coarse policy after paying `cost`. -/
theorem refine_certificate (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (hsum : ∑ x, pi_dist x = 1) (t : ℝ) (ht : 0 ≤ t)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀)
    (q : V → β) (f : β → γ) (rule : β → α) (u : α → V → ℝ)
    (hopt : ∀ b, blockUtility q (coarseLaw pi_dist hπ P L t f₀) u b (rule b) =
      blockValue q (coarseLaw pi_dist hπ P L t f₀) u b)
    {M cost : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ω, |u a ω| ≤ M)
    (hmargin : cost + 2 * M * (t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) *
      norm_pi pi_dist f₀) < voi q f (coarseLaw pi_dist hπ P L t f₀) u) :
    value (f ∘ q) (trueLaw pi_dist L t f₀) u <
      policyValue q (trueLaw pi_dist L t f₀) u rule - cost :=
  empirical_refinement_safe_of_radius q _ _ u f rule hopt hM0 hM
    (l1Error_coarseLaw_le pi_dist hπ P L hL hstat hsum t ht f₀ hf₀) hmargin

/-- **Stop certificate.** If the coarse model's estimated VOI plus `2M·t·ε·‖f₀‖_π` is at
most `cost`, refinement is not profitable under the true law. -/
theorem stop_certificate (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (hsum : ∑ x, pi_dist x = 1) (t : ℝ) (ht : 0 ≤ t)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀)
    (q : V → β) (f : β → γ) (u : α → V → ℝ)
    {M cost : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ω, |u a ω| ≤ M)
    (hmargin : voi q f (coarseLaw pi_dist hπ P L t f₀) u + 2 * M *
      (t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) * norm_pi pi_dist f₀) ≤ cost) :
    value q (trueLaw pi_dist L t f₀) u - cost ≤ value (f ∘ q) (trueLaw pi_dist L t f₀) u :=
  refinement_not_profitable_of_radius q _ _ u f hM0 hM
    (l1Error_coarseLaw_le pi_dist hπ P L hL hstat hsum t ht f₀ hf₀) hmargin

/-- **Consolidated-memory refine certificate**: the agent knows only its macrostate `B`;
radius `t·ε/√π̄(B)`. -/
theorem refine_certificate_block (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (hsum : ∑ x, pi_dist x = 1) (t : ℝ) (ht : 0 ≤ t) (B : P.Quot)
    (q : V → β) (f : β → γ) (rule : β → α) (u : α → V → ℝ)
    (hopt : ∀ b, blockUtility q (coarseLaw pi_dist hπ P L t (blockDensity pi_dist P B)) u b (rule b) =
      blockValue q (coarseLaw pi_dist hπ P L t (blockDensity pi_dist P B)) u b)
    {M cost : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ω, |u a ω| ≤ M)
    (hmargin : cost + 2 * M * (t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) /
      Real.sqrt (pi_bar P pi_dist B)) <
      voi q f (coarseLaw pi_dist hπ P L t (blockDensity pi_dist P B)) u) :
    value (f ∘ q) (trueLaw pi_dist L t (blockDensity pi_dist P B)) u <
      policyValue q (trueLaw pi_dist L t (blockDensity pi_dist P B)) u rule - cost :=
  empirical_refinement_safe_of_radius q _ _ u f rule hopt hM0 hM
    (l1Error_coarseLaw_block_le pi_dist hπ P L hL hstat hsum t ht B) hmargin

/-! ## §5. The reversible reading: `π·e^{tL}f` is the forward law -/

omit [Nonempty V] in
/-- Detailed balance `π_x L_xy = π_y L_yx` as a matrix identity `Lᵀ·D = D·L`, `D = diag π`. -/
lemma transpose_mul_diag_of_reversible (hrev : ∀ x y, pi_dist x * L x y = pi_dist y * L y x) :
    Lᵀ * Matrix.diagonal pi_dist = Matrix.diagonal pi_dist * L := by
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  rw [mul_comm (L y x) (pi_dist y)]
  exact (hrev x y).symm

omit [Nonempty V] in
lemma transpose_pow_mul_diag_of_reversible (hrev : ∀ x y, pi_dist x * L x y = pi_dist y * L y x)
    (n : ℕ) : (L ^ n)ᵀ * Matrix.diagonal pi_dist = Matrix.diagonal pi_dist * L ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
      transpose_mul_diag_of_reversible pi_dist L hrev, Matrix.mul_assoc, ← pow_succ', ← pow_succ]

/-- Left-multiplication by `D` and `M ↦ Mᵀ·D`, as linear maps out of the weighted algebra. -/
def diagMulLin : PiMat V pi_dist hπ →ₗ[ℝ] Matrix V V ℝ where
  toFun M := Matrix.diagonal pi_dist * toMat pi_dist hπ M
  map_add' M N := by show Matrix.diagonal pi_dist * (toMat pi_dist hπ M + toMat pi_dist hπ N) = _; rw [Matrix.mul_add]
  map_smul' c M := by show Matrix.diagonal pi_dist * (c • toMat pi_dist hπ M) = _; rw [Matrix.mul_smul]; rfl

def transposeMulDiagLin : PiMat V pi_dist hπ →ₗ[ℝ] Matrix V V ℝ where
  toFun M := (toMat pi_dist hπ M)ᵀ * Matrix.diagonal pi_dist
  map_add' M N := by
    show (toMat pi_dist hπ M + toMat pi_dist hπ N)ᵀ * _ = _
    rw [Matrix.transpose_add, Matrix.add_mul]
  map_smul' c M := by
    show (c • toMat pi_dist hπ M)ᵀ * _ = _
    rw [Matrix.transpose_smul, Matrix.smul_mul]; rfl

include hπ in
/-- **Detailed balance propagates to the heat kernel**: `(e^{tL})ᵀ·D = D·e^{tL}`. -/
theorem heatKernel_transpose_mul_diag (hrev : ∀ x y, pi_dist x * L x y = pi_dist y * L y x) (t : ℝ) :
    (exp ℝ (t • L))ᵀ * Matrix.diagonal pi_dist = Matrix.diagonal pi_dist * exp ℝ (t • L) := by
  have hrev' : ∀ x y, pi_dist x * (t • L) x y = pi_dist y * (t • L) y x := by
    intro x y; simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm (pi_dist x), hrev x y, mul_left_comm]
  set X := t • L with hX
  have h1 : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℝ) • (ofMat pi_dist hπ X) ^ n)
      (exp ℝ (ofMat pi_dist hπ X)) := by
    rw [exp_eq_tsum]
    exact (expSeries_summable' (𝕂 := ℝ) (ofMat pi_dist hπ X)).hasSum
  have hA := h1.map (transposeMulDiagLin (V := V) pi_dist hπ)
    (LinearMap.continuous_of_finiteDimensional _)
  have hB := h1.map (diagMulLin (V := V) pi_dist hπ) (LinearMap.continuous_of_finiteDimensional _)
  have hsame : (⇑(transposeMulDiagLin (V := V) pi_dist hπ) ∘ fun n : ℕ =>
      (n.factorial⁻¹ : ℝ) • (ofMat pi_dist hπ X) ^ n) =
      (⇑(diagMulLin (V := V) pi_dist hπ) ∘ fun n : ℕ => (n.factorial⁻¹ : ℝ) • (ofMat pi_dist hπ X) ^ n) := by
    funext n
    show ((n.factorial⁻¹ : ℝ) • X ^ n)ᵀ * Matrix.diagonal pi_dist =
      Matrix.diagonal pi_dist * ((n.factorial⁻¹ : ℝ) • X ^ n)
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      transpose_pow_mul_diag_of_reversible pi_dist X hrev' n]
  rw [hsame] at hA
  have := hA.unique hB
  have e := exp_piMat_eq pi_dist hπ X
  rw [← e]
  exact this

include hπ in
/-- **Forward law of a reversible chain**: evolving the law `π·f₀` by `e^{tL}` (as a row
vector) gives the law with density `e^{tL}f₀`. This identifies `trueLaw` with the forward
Kolmogorov evolution of the consolidated law. -/
theorem law_evolution_of_reversible (hrev : ∀ x y, pi_dist x * L x y = pi_dist y * L y x)
    (t : ℝ) (f₀ : V → ℝ) :
    lawOf pi_dist f₀ ᵥ* exp ℝ (t • L) = trueLaw pi_dist L t f₀ := by
  have h := heatKernel_transpose_mul_diag pi_dist hπ L hrev t
  have hlaw : lawOf pi_dist f₀ = Matrix.diagonal pi_dist *ᵥ f₀ := by
    funext x; simp [lawOf, Matrix.mulVec_diagonal]
  have hlaw' : lawOf pi_dist (HeatKernelMap L t f₀) = Matrix.diagonal pi_dist *ᵥ (exp ℝ (t • L) *ᵥ f₀) := by
    funext x; simp [lawOf, Matrix.mulVec_diagonal, HeatKernelMap, HeatKernel, matrixToLinearMap]
  unfold trueLaw
  rw [hlaw, hlaw', ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]

/-! ## §6. The orbit radius: a kernel-checked certificate radius that does not pay for rarity

The operator-norm radius `t·ε·‖f₀‖_π = t·ε/√π̄(B)` penalises rare macrostates. The
orbit-telescoping lemma gives, for every `n ≥ 1` and `h = t/n`,

  `‖p_t − p̂_t‖₁ ≤ Σ_{k<n} ‖(e^{hL} − e^{hL̄}) e^{khL̄} f₀‖_π`,

a radius computed from the coarse trajectory and the fine *generator* (not the fine state).
Numerically it is tight to a factor ≈ 1.4–1.9 in the gauge test bed and essentially
independent of `π̄(B)` (decision 0084). -/

/-- Orbit radius at resolution `n`. -/
def orbitRadius (t : ℝ) (f₀ : V → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, norm_pi pi_dist
    ((exp ℝ ((t / n) • L) - exp ℝ ((t / n) • CoarseGeneratorMatrix L P pi_dist hπ)) *ᵥ
      (exp ℝ ((t / n) • CoarseGeneratorMatrix L P pi_dist hπ) ^ k *ᵥ f₀))

/-- **Orbit-radius bound** on the L¹ distance between the true and coarse laws. -/
theorem l1Error_coarseLaw_le_orbitRadius (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (hsum : ∑ x, pi_dist x = 1) (t : ℝ) (ht : 0 ≤ t) (f₀ : V → ℝ) {n : ℕ} (hn : 0 < n) :
    l1Error (trueLaw pi_dist L t f₀) (coarseLaw pi_dist hπ P L t f₀) ≤
      orbitRadius pi_dist hπ P L t f₀ n := by
  unfold trueLaw coarseLaw orbitRadius
  refine le_trans (l1Error_lawOf_le pi_dist (fun x => (hπ x).le) hsum _ _) ?_
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set h : ℝ := t / n with hh
  have hh0 : 0 ≤ h := div_nonneg ht hn'.le
  have hpow : ∀ X : Matrix V V ℝ, exp ℝ (t • X) = exp ℝ (h • X) ^ n := by
    intro X
    have hPM := SGC.Bridge.ContractiveHorizon.exp_smul_eq_pow (ofMat pi_dist hπ X) t hn
    have e1 := exp_piMat_eq pi_dist hπ (t • X)
    have e2 := exp_piMat_eq pi_dist hπ (h • X)
    rw [← e1, ← e2]
    exact congrArg (toMat pi_dist hπ) hPM
  have hdiff : HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀ =
      (exp ℝ (h • L) ^ n - exp ℝ (h • CoarseGeneratorMatrix L P pi_dist hπ) ^ n) *ᵥ f₀ := by
    show exp ℝ (t • L) *ᵥ f₀ - exp ℝ (t • CoarseGeneratorMatrix L P pi_dist hπ) *ᵥ f₀ = _
    rw [Matrix.sub_mulVec, hpow L, hpow (CoarseGeneratorMatrix L P pi_dist hπ)]
  rw [hdiff]
  exact SGC.Bridge.ContractiveHorizon.norm_pi_pow_sub_pow_mulVec_le_sum pi_dist hπ _ _ f₀
    (SGC.Bridge.ContractiveHorizon.heatKernel_contractive_of_generator pi_dist hπ L hL hstat h hh0) n

/-- **Refine certificate with the orbit radius.** -/
theorem refine_certificate_orbit (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (hsum : ∑ x, pi_dist x = 1) (t : ℝ) (ht : 0 ≤ t) (f₀ : V → ℝ) {n : ℕ} (hn : 0 < n)
    (q : V → β) (f : β → γ) (rule : β → α) (u : α → V → ℝ)
    (hopt : ∀ b, blockUtility q (coarseLaw pi_dist hπ P L t f₀) u b (rule b) =
      blockValue q (coarseLaw pi_dist hπ P L t f₀) u b)
    {M cost : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ω, |u a ω| ≤ M)
    (hmargin : cost + 2 * M * orbitRadius pi_dist hπ P L t f₀ n <
      voi q f (coarseLaw pi_dist hπ P L t f₀) u) :
    value (f ∘ q) (trueLaw pi_dist L t f₀) u <
      policyValue q (trueLaw pi_dist L t f₀) u rule - cost :=
  empirical_refinement_safe_of_radius q _ _ u f rule hopt hM0 hM
    (l1Error_coarseLaw_le_orbitRadius pi_dist hπ P L hL hstat hsum t ht f₀ hn) hmargin

/-- **Stop certificate with the orbit radius.** -/
theorem stop_certificate_orbit (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (hsum : ∑ x, pi_dist x = 1) (t : ℝ) (ht : 0 ≤ t) (f₀ : V → ℝ) {n : ℕ} (hn : 0 < n)
    (q : V → β) (f : β → γ) (u : α → V → ℝ)
    {M cost : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ω, |u a ω| ≤ M)
    (hmargin : voi q f (coarseLaw pi_dist hπ P L t f₀) u + 2 * M *
      orbitRadius pi_dist hπ P L t f₀ n ≤ cost) :
    value q (trueLaw pi_dist L t f₀) u - cost ≤ value (f ∘ q) (trueLaw pi_dist L t f₀) u :=
  refinement_not_profitable_of_radius q _ _ u f hM0 hM
    (l1Error_coarseLaw_le_orbitRadius pi_dist hπ P L hL hstat hsum t ht f₀ hn) hmargin

end SGC.Bridge.DecisionHorizon
