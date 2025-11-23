# FHDT: Formal Verification of the Functorial Heat Dominance Theorem

This repository contains a `sorry-free` Lean 4 formalization of the Functorial Heat Dominance Theorem (FHDT). The main theorem provides an exponential envelope bound on a stability flow $\beta(t)$ for non-reversible Markov chains.

The main result is `FHDT.Defs.FunctorialHeatDominanceTheorem`.

## Quick Start

1.  Ensure `elan` and `lake` are installed.
2.  Clone this repository.
3.  Navigate into the repository directory and run `lake build`.
4.  (Optional) Run tests with `lake build test`.

## Module Map

*   `Core/Assumptions.lean`: Defines the $L^2(\pi)$ geometry and proves **Pillar 1** (`gap_pos_iff_ker_eq_span_one`), establishing the equivalence between a positive spectral gap and the kernel of the Hermitian part.
*   `Core/Projector.lean`: Defines the $L^2(\pi)$ operator norm `opNorm_pi` (via the isometry `iso_L2_to_std`) and the canonical projector `P_ortho_pi`.
*   `FHDT/Envelope.lean`: Defines the `EnvelopeSpec` class and the `HeatKernel`.
*   `FHDT/Envelope/Sector.lean`: Proves **Pillar 2** (`sector_envelope_bound_canonical`), the purely contractive envelope $\Vert K(t) \circ P \Vert_{\pi} \le e^{-\lambda_{\text{gap}} t}$ using an energy method and Grönwall's inequality.
*   `FHDT/Diagonal.lean`: Proves the **Pillar 3** calculus lemmas, including the diagonal operator norm bound `sum_abs_diag_le_card_opNorm`.
*   `FHDT/Defs.lean`: Defines the core observables (`K_norm`, `beta_t`) and assembles the pillars to prove the final **`FunctorialHeatDominanceTheorem`**.

## Main Theorems (Formal Names)

*   `FHDT.Defs.FunctorialHeatDominanceTheorem`: The main theorem, $|\beta(t)| \le C e^{-\lambda_{\text{gap}} t}$.
*   `FHDT.Core.Assumptions.gap_pos_iff_ker_eq_span_one`: Pillar 1.
*   `FHDT.Envelope.Sector.sector_envelope_bound_canonical`: Pillar 2.
