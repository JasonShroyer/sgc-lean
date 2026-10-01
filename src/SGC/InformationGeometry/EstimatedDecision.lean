import SGC.InformationGeometry.GatedController

noncomputable section

namespace SGC.InformationGeometry.EstimatedDecision

open Finset DecisionValue

set_option linter.unusedSectionVars false

variable {Ω β γ α ι : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype α] [Nonempty α]

variable (q : Ω → β) (p pHat : Ω → ℝ) (u : α → Ω → ℝ)

def l1Error : ℝ := ∑ ω, |p ω - pHat ω|

lemma l1Error_nonneg : 0 ≤ l1Error p pHat :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma l1Error_comm : l1Error p pHat = l1Error pHat p := by
  unfold l1Error
  exact Finset.sum_congr rfl (fun ω _ => abs_sub_comm _ _)

lemma blockUtility_error_le {M : ℝ} (hM : ∀ a ω, |u a ω| ≤ M) (b : β) (a : α) :
    |blockUtility q p u b a - blockUtility q pHat u b a|
      ≤ M * ∑ ω ∈ univ.filter (fun ω => q ω = b), |p ω - pHat ω| := by
  unfold blockUtility
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ω _ => ?_))
  rw [← sub_mul, abs_mul]
  calc |p ω - pHat ω| * |u a ω| ≤ |p ω - pHat ω| * M :=
        mul_le_mul_of_nonneg_left (hM a ω) (abs_nonneg _)
    _ = M * |p ω - pHat ω| := mul_comm _ _

lemma value_le_add_error {M : ℝ} (hM : ∀ a ω, |u a ω| ≤ M) :
    value q p u ≤ value q pHat u + M * l1Error p pHat := by
  have hb : ∀ b, blockValue q p u b ≤ blockValue q pHat u b
      + M * ∑ ω ∈ univ.filter (fun ω => q ω = b), |p ω - pHat ω| := by
    intro b
    obtain ⟨a, ha⟩ := exists_optimal q p u b
    have he := (abs_le.mp (blockUtility_error_le q p pHat u hM b a)).2
    have hm := blockUtility_le_blockValue q pHat u b a
    linarith
  calc value q p u ≤ ∑ b, (blockValue q pHat u b
        + M * ∑ ω ∈ univ.filter (fun ω => q ω = b), |p ω - pHat ω|) :=
      Finset.sum_le_sum (fun b _ => hb b)
    _ = value q pHat u + M * l1Error p pHat := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← ScoreProjection.sum_fibers q (fun ω => |p ω - pHat ω|)]
      rfl

theorem value_error_le {M : ℝ} (hM : ∀ a ω, |u a ω| ≤ M) :
    |value q p u - value q pHat u| ≤ M * l1Error p pHat := by
  have h₁ := value_le_add_error q p pHat u hM
  have h₂ := value_le_add_error q pHat p u hM
  rw [l1Error_comm pHat p] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem voi_error_le (f : β → γ) {M : ℝ} (hM : ∀ a ω, |u a ω| ≤ M) :
    |voi q f p u - voi q f pHat u| ≤ 2 * (M * l1Error p pHat) := by
  have h₁ := abs_le.mp (value_error_le q p pHat u hM)
  have h₂ := abs_le.mp (value_error_le (f ∘ q) p pHat u hM)
  unfold voi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def policyValue (rule : β → α) : ℝ := ∑ ω, p ω * u (rule (q ω)) ω

lemma policyValue_eq_sum_blocks (rule : β → α) :
    policyValue q p u rule = ∑ b, blockUtility q p u b (rule b) := by
  unfold policyValue blockUtility
  rw [ScoreProjection.sum_fibers q]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun ω hω => ?_))
  rw [(Finset.mem_filter.mp hω).2]

theorem policyValue_le_value (rule : β → α) : policyValue q p u rule ≤ value q p u := by
  rw [policyValue_eq_sum_blocks]
  exact Finset.sum_le_sum (fun b _ => blockUtility_le_blockValue q p u b (rule b))

theorem policyValue_eq_value (rule : β → α)
    (hopt : ∀ b, blockUtility q p u b (rule b) = blockValue q p u b) :
    policyValue q p u rule = value q p u := by
  rw [policyValue_eq_sum_blocks]
  exact Finset.sum_congr rfl (fun b _ => hopt b)

theorem policyValue_error_le (rule : β → α) {M : ℝ} (hM : ∀ a ω, |u a ω| ≤ M) :
    |policyValue q p u rule - policyValue q pHat u rule| ≤ M * l1Error p pHat := by
  unfold policyValue l1Error
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ω _ => ?_))
  rw [← sub_mul, abs_mul]
  calc |p ω - pHat ω| * |u (rule (q ω)) ω| ≤ |p ω - pHat ω| * M :=
        mul_le_mul_of_nonneg_left (hM _ _) (abs_nonneg _)
    _ = M * |p ω - pHat ω| := mul_comm _ _

def optimalRule (b : β) : α := Classical.choose (exists_optimal q p u b)

theorem optimalRule_spec (b : β) :
    blockUtility q p u b (optimalRule q p u b) = blockValue q p u b :=
  Classical.choose_spec (exists_optimal q p u b)

theorem empirical_policy_regret_le (rule : β → α)
    (hopt : ∀ b, blockUtility q pHat u b (rule b) = blockValue q pHat u b)
    {M : ℝ} (hM : ∀ a ω, |u a ω| ≤ M) :
    value q p u - policyValue q p u rule ≤ 2 * (M * l1Error p pHat) := by
  have hv := (abs_le.mp (value_error_le q p pHat u hM)).2
  have hp := (abs_le.mp (policyValue_error_le q p pHat u rule hM)).1
  have he := policyValue_eq_value q pHat u rule hopt
  linarith

theorem empirical_refinement_safe (f : β → γ) (rule : β → α)
    (hopt : ∀ b, blockUtility q pHat u b (rule b) = blockValue q pHat u b)
    {M cost : ℝ} (hM : ∀ a ω, |u a ω| ≤ M)
    (hmargin : cost + 2 * (M * l1Error p pHat) < voi q f pHat u) :
    value (f ∘ q) p u < policyValue q p u rule - cost := by
  have hb := (abs_le.mp (value_error_le (f ∘ q) p pHat u hM)).2
  have hr := (abs_le.mp (policyValue_error_le q p pHat u rule hM)).1
  have he := policyValue_eq_value q pHat u rule hopt
  unfold voi at hmargin
  linarith

theorem refinement_not_profitable (f : β → γ) {M cost : ℝ}
    (hM : ∀ a ω, |u a ω| ≤ M)
    (hmargin : voi q f pHat u + 2 * (M * l1Error p pHat) ≤ cost) :
    value q p u - cost ≤ value (f ∘ q) p u := by
  have he := (abs_le.mp (voi_error_le q p pHat u f hM)).2
  unfold voi at *
  linarith

theorem empirical_refinement_safe_of_radius (f : β → γ) (rule : β → α)
    (hopt : ∀ b, blockUtility q pHat u b (rule b) = blockValue q pHat u b)
    {M radius cost : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ω, |u a ω| ≤ M)
    (herror : l1Error p pHat ≤ radius)
    (hmargin : cost + 2 * M * radius < voi q f pHat u) :
    value (f ∘ q) p u < policyValue q p u rule - cost := by
  apply empirical_refinement_safe q p pHat u f rule hopt hM
  have h := mul_le_mul_of_nonneg_left herror hM0
  nlinarith

theorem refinement_not_profitable_of_radius (f : β → γ) {M radius cost : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ a ω, |u a ω| ≤ M) (herror : l1Error p pHat ≤ radius)
    (hmargin : voi q f pHat u + 2 * M * radius ≤ cost) :
    value q p u - cost ≤ value (f ∘ q) p u := by
  apply refinement_not_profitable q p pHat u f hM
  have h := mul_le_mul_of_nonneg_left herror hM0
  nlinarith

section Selection

variable {I : Type*} (truth estimate radius : I → ℝ)

theorem selected_regret_le (herror : ∀ i, |truth i - estimate i| ≤ radius i)
    (chosen : I) (hchosen : ∀ i, estimate i ≤ estimate chosen) (i : I) :
    truth i - truth chosen ≤ radius i + radius chosen := by
  have hi := (abs_le.mp (herror i)).2
  have hc := (abs_le.mp (herror chosen)).1
  linarith [hchosen i]

theorem safe_switch {base candidate : I}
    (herror : ∀ i, |truth i - estimate i| ≤ radius i)
    (hmargin : estimate base + radius base < estimate candidate - radius candidate) :
    truth base < truth candidate := by
  have hb := (abs_le.mp (herror base)).2
  have hc := (abs_le.mp (herror candidate)).1
  linarith

theorem prune_candidate {base candidate : I}
    (herror : ∀ i, |truth i - estimate i| ≤ radius i)
    (hmargin : estimate candidate + radius candidate ≤ estimate base - radius base) :
    truth candidate ≤ truth base := by
  have hb := (abs_le.mp (herror base)).1
  have hc := (abs_le.mp (herror candidate)).2
  linarith

end Selection

section Menu

variable [Fintype ι] [Nonempty ι]
variable (menu : GatedController.Menu Ω β γ ι)

theorem menu_net_error_le {M : ℝ} (hM : ∀ a ω, |u a ω| ≤ M) :
    |GatedController.net menu p u - GatedController.net menu pHat u| ≤ M * l1Error p pHat := by
  have oneWay : ∀ (p₁ p₂ : Ω → ℝ), GatedController.net menu p₁ u ≤
      GatedController.net menu p₂ u + M * l1Error p₁ p₂ := by
    intro p₁ p₂
    unfold GatedController.net
    refine max_le ?_ ?_
    · have h := value_le_add_error menu.q₀ p₁ p₂ u hM
      exact h.trans (add_le_add_right (le_max_left _ _) _)
    · unfold GatedController.bestRefine
      refine Finset.sup'_le _ _ (fun i _ => ?_)
      have h := value_le_add_error (menu.q i) p₁ p₂ u hM
      have hi := GatedController.net_ge_refine menu p₂ u i
      simp only [GatedController.net, GatedController.bestRefine, GatedController.refineNet] at hi
      unfold GatedController.refineNet
      linarith
  have h₁ := oneWay p pHat
  have h₂ := oneWay pHat p
  rw [l1Error_comm pHat p] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem selected_refinement_policy_regret_le (chosen : ι) (rule : β → α)
    (hopt : ∀ b, blockUtility (menu.q chosen) pHat u b (rule b) = blockValue (menu.q chosen) pHat u b)
    (hchosen : GatedController.net menu pHat u = value (menu.q chosen) pHat u - menu.cost chosen)
    {M : ℝ} (hM : ∀ a ω, |u a ω| ≤ M) :
    GatedController.net menu p u - (policyValue (menu.q chosen) p u rule - menu.cost chosen)
      ≤ 2 * (M * l1Error p pHat) := by
  have hn := (abs_le.mp (menu_net_error_le p pHat u menu hM)).2
  have hp := (abs_le.mp (policyValue_error_le (menu.q chosen) p pHat u rule hM)).1
  have he := policyValue_eq_value (menu.q chosen) pHat u rule hopt
  linarith

theorem selected_base_policy_regret_le (rule : γ → α)
    (hopt : ∀ b, blockUtility menu.q₀ pHat u b (rule b) = blockValue menu.q₀ pHat u b)
    (hchosen : GatedController.net menu pHat u = value menu.q₀ pHat u)
    {M : ℝ} (hM : ∀ a ω, |u a ω| ≤ M) :
    GatedController.net menu p u - policyValue menu.q₀ p u rule
      ≤ 2 * (M * l1Error p pHat) := by
  have hn := (abs_le.mp (menu_net_error_le p pHat u menu hM)).2
  have hp := (abs_le.mp (policyValue_error_le menu.q₀ p pHat u rule hM)).1
  have he := policyValue_eq_value menu.q₀ pHat u rule hopt
  linarith

end Menu

end SGC.InformationGeometry.EstimatedDecision
