/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.HaltingCompiler
import SGC.Bridge.DeterministicKernels
import SGC.Bridge.TerminalDecoding

/-!
# Block renormalization of a deterministic computation is exact

The 2025 manuscript *The Physical Basis of Computational Complexity* read the
Williams / Cook-Mertz tree-evaluation simulation (`TIME[t] ⊆ SPACE[√(t log t)]`) as a
renormalization-group flow: a time block of `b` steps is one coarse-graining step, the
`b`-step simulation is the RG transformation rule, and the TEP tree is the dependency
graph of the flow. That reading was labelled a "formal isomorphism"; by the discipline of
*Two Horizons* it is a dictionary. This module isolates the part of it that is a theorem:

**temporal blocking of a deterministic dynamics is an exact (`ε = 0`) coarse-graining.**

Two settings, one statement.

## 1. Finite deterministic dynamics as a kernel

For `f : V → V` on a finite `V`, `detKernel f x y = [f x = y]` is a row-stochastic kernel
and `(detKernel f) ^ b = detKernel (f^[b])` (`detKernel_pow`). The `b`-step block map is
therefore *literally* the `b`-th power of the one-step kernel: the block-level Markov law
is exact, with zero closure error, for every `b`. Consequently the Kernel Horizon and the
terminal decoding certificate applied to blocked deterministic dynamics have **zero
approximation budget** (`blocked_terminal_tv_zero`): whatever a Williams-style block
simulation costs, it is not paying for approximation error between levels. The cost is
elsewhere - in what state must be retained - which is the open lower-bound question and
is *not* addressed here.

## 2. Mathlib's Turing machines

For a partial step function `f : σ → Option σ` (Mathlib's `TM0.step M` is one), the
fuel-indexed run `multistep f a n` from `HaltingCompiler` satisfies the block composition
law `multistep_add` and hence `multistep_mul`: running `h` blocks of `b` steps *is*
running `b * h` steps. The TEP tree's node function (simulate `b` steps) composes exactly,
and the tower is **halting-faithful**: for `b ≥ 1`, the machine halts iff some block
count yields `none` (`halts_iff_block_halts`), which by `evalDom_iff_multistep` is
Mathlib's own halting predicate `(TM0.eval M w).Dom`.

## What is and is not claimed

PROVEN: the exactness statements above. They are elementary; their value is that they
pin down, on Mathlib's machine model, exactly which part of the "TEP is RG" reading is a
theorem (composition of blocks; zero closure error) and which is not.

NOT CLAIMED: any space lower bound (`S ≥ Ω(1/λ_gap + ...)` in the 2025 manuscript is a
[CONJECTURE]: `O(b)` is Cook-Mertz's *upper* bound on block-simulation space, and a lower
bound needs an adversary or information argument); any identification of `1/λ_gap` with
a coherence cost; any statement about Markov-blanket integrity. Those belong to the
constraint ladder of *Certificates, Not Slogans*, Stage 3.
-/

noncomputable section

namespace SGC.Bridge.BlockRenormalization

open Finset Matrix
open SGC.Bridge.HaltingCompiler
open SGC.Renormalization.KernelHorizon

/-! ## 1. Finite deterministic dynamics -/

section Finite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The one-step deterministic kernel `[f x = y]`. -/
def detKernel (f : V → V) : Matrix V V ℝ := fun x y => if f x = y then 1 else 0

lemma detKernel_isStochastic (f : V → V) : IsStochastic (detKernel f) where
  nonneg x y := by unfold detKernel; split_ifs <;> norm_num
  row_sum_one x := by simp [detKernel]

/-- Kernels of deterministic maps compose contravariantly: `T_f * T_g = T_{g ∘ f}`
(first `f`, then `g`, in row-vector evolution). -/
lemma detKernel_mul (f g : V → V) : detKernel f * detKernel g = detKernel (g ∘ f) := by
  ext x z
  simp only [Matrix.mul_apply, detKernel, Function.comp]
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- **Temporal blocking is exact**: the `b`-step block map is the `b`-th kernel power. -/
theorem detKernel_pow (f : V → V) (b : ℕ) : (detKernel f) ^ b = detKernel (f^[b]) := by
  induction b with
  | zero =>
    ext x y
    simp [detKernel, Matrix.one_apply]
  | succ b ih =>
    rw [pow_succ, ih, detKernel_mul, Function.iterate_succ']

/-- Running `h` blocks of `b` steps is running `b * h` steps, at the kernel level. -/
theorem detKernel_block_pow (f : V → V) (b h : ℕ) :
    (detKernel (f^[b])) ^ h = (detKernel f) ^ (b * h) := by
  rw [detKernel_pow, detKernel_pow, Function.iterate_mul]

/-- The block-level dynamics has **zero closure error** against any partition and any
positive reference weights, whenever the coarse observation is the identity partition of
time: the block chain *is* the one-step chain's power. Stated as: the terminal error
matrix of the blocked kernel at `h` blocks equals that of the one-step kernel at `b * h`
steps. -/
theorem blocked_terminalError_eq (f : V → V) (P : SGC.Partition V) (pi : V → ℝ) (b h : ℕ) :
    SGC.Bridge.TerminalDecoding.terminalError (detKernel (f^[b])) P pi h =
      (detKernel f) ^ (b * h) * SGC.lift_matrix P -
        SGC.lift_matrix P *
          (SGC.Thermodynamics.CoarseGenerator (detKernel (f^[b])) P pi) ^ h := by
  unfold SGC.Bridge.TerminalDecoding.terminalError
  rw [detKernel_block_pow]

/-- Deterministic dynamics moves point masses to point masses: the actual law after `m`
steps from a point mass at `x` is the point mass at `f^[m] x`. Hence for deterministic
dynamics observed exactly (discrete partition), the approximation budget of the terminal
decoding certificate is identically zero. -/
theorem detKernel_vecMul_point (f : V → V) (x : V) (m : ℕ) :
    (fun y => if y = x then (1 : ℝ) else 0) ᵥ* (detKernel f) ^ m =
      fun y => if y = f^[m] x then 1 else 0 := by
  rw [detKernel_pow]
  ext z
  simp only [Matrix.vecMul, dotProduct, detKernel]
  rw [Finset.sum_eq_single x]
  · simp [eq_comm]
  · intro y _ hy
    simp [hy]
  · simp

end Finite

/-! ## 2. Mathlib's Turing machines -/

section Machines

variable {σ : Type*}

/-- Block composition: running `m + n` steps is running `m` steps then `n` steps. -/
theorem multistep_add (f : σ → Option σ) (a : σ) (m n : ℕ) :
    multistep f a (m + n) = (multistep f a m).bind (fun a' => multistep f a' n) := by
  induction n with
  | zero => simp [multistep]
  | succ n ih =>
    rw [← Nat.add_assoc, multistep_succ, ih]
    cases multistep f a m with
    | none => rfl
    | some a' => simp [multistep_succ]

/-- The TEP node function: simulate one block of `b` steps (partial). -/
def blockStep (f : σ → Option σ) (b : ℕ) (a : σ) : Option σ := multistep f a b

/-- **The TEP tower evaluates the machine exactly**: `h` blocks of `b` steps is `b * h`
steps. This is the composition law that makes the Cook-Mertz node function well defined
across levels. -/
theorem multistep_mul (f : σ → Option σ) (a : σ) (b h : ℕ) :
    multistep (blockStep f b) a h = multistep f a (b * h) := by
  induction h with
  | zero => simp [multistep]
  | succ h ih =>
    rw [multistep_succ, ih, Nat.mul_succ, multistep_add]
    rfl

/-- **The block tower is halting-faithful** (for a positive block size): the machine
halts iff some number of blocks yields `none`. Via `evalDom_iff_multistep` the left side is
Mathlib's `(Turing.eval f a).Dom`. -/
theorem halts_iff_block_halts (f : σ → Option σ) (a : σ) {b : ℕ} (hb : 0 < b) :
    (∃ n, multistep f a n = none) ↔ ∃ h, multistep (blockStep f b) a h = none := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [multistep_mul]
    exact multistep_none_mono (Nat.le_mul_of_pos_left n hb) hn
  · rintro ⟨h, hh⟩
    rw [multistep_mul] at hh
    exact ⟨b * h, hh⟩

/-- Restated against Mathlib's halting predicate. -/
theorem evalDom_iff_block_halts (f : σ → Option σ) (a : σ) {b : ℕ} (hb : 0 < b) :
    (Turing.eval f a).Dom ↔ ∃ h, multistep (blockStep f b) a h = none :=
  evalDom_iff_multistep.trans (halts_iff_block_halts f a hb)

end Machines

end SGC.Bridge.BlockRenormalization

end
