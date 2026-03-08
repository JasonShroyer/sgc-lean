# Experimental Record: Thermodynamic Intelligence Engine

**Repository:** thermodynamic-intelligence-engine (private)  
**Branch:** wip-quantum-bridge  
**Date:** March 8, 2026

---

## Purpose

This directory consolidates the critical experimental artifacts from the SGC research program
that led to the V2 Thermodynamic Intelligence Architecture. Each file represents a milestone
in the journey from theoretical formalization to empirical breakthrough.

---

## Contents

### Phase 1: Grokking as a Physical Phase Transition

| File | Significance |
|------|-------------|
| `functional_grokking_detector.py` | Detects grokking via functional defect collapse (eps -> 0). The instrument that measures the Lifshitz transition in real-time. |
| `lifshitz_transition_experiment.py` | The experiment that observed the 2.5-order Lifshitz transition: FD 1.01 -> 0.000, CS 0.01 -> 182,697,227. Validated grokking = topological phase transition. |
| `grokking_manifold_surgery.py` | Full manifold diagnostics: Hessian eigenvalues, Ridge Ratio, Gauss curvature. Proved the manifold is a FLAT TORUS (K ~ 10^-8). |
| `grokking_manifold_surgery_fast.py` | Fast version with correct hyperparameters. 5.6x Kramers speedup validated (epoch 2200 -> 390). |

### Phase 2: Cellular Sheaf Networks

| File | Significance |
|------|-------------|
| `cellular_sheaf_network.py` | Achieved 100% compositional generalization by making the network architecture BE a sheaf. Key insight: compositionality requires architectural support. |
| `cellular_sheaf_engine.py` | The sheaf-native computation engine. Graph topology directly encodes algebraic structure. |

### Phase 3: The Topological Diagnosis (b1 = 0)

| File | Significance |
|------|-------------|
| `betti_autopsy.py` | **THE SMOKING GUN.** Computed b0 and b1 for all crystallized Laplacians. Found 34/34 had b1=0 (zero Markov blankets) despite 88-98% accuracy. Diagnosed L1 sparsity as "topological poison." |

### Phase 4: The V2 Thermodynamic Architecture

| File | Significance |
|------|-------------|
| `cascade_thought_experiment.py` | Phase 5 experiment: multi-step ARC puzzles. Showed b1 scales with compositional depth (b1=1 for chains, b1=2-3 for convergence tasks). First evidence of Yamabe neck cascade. |

### Phase 5: The Breakthrough Documents

| File | Significance |
|------|-------------|
| `functional_blanket_breakthrough.md` | Proved grokking is ALGEBRAIC (functional defect collapses) not GEOMETRIC (PCA closure increases). The Markov blanket is functional, not dimensional. |
| `sgc_grokking_phase6.py` | The Wavelet-Coupled Exploration Mass Controller. Implements HG spectral noise, coupling coefficient kappa, and effective exploration mass M_eff = sum(kappa_t * eta_t). |

---

## The Arc of Discovery

```
Lifshitz Transition (grokking = phase transition)
    |
    v
Functional Blanket (the blanket is algebraic, not geometric)
    |
    v
Cellular Sheaf (architecture must BE a sheaf)
    |
    v
Betti Autopsy (34/34 b1=0 -> L1 sparsity is topological poison)
    |
    v
Generalization Boundary Theorem (b1>=1 -> approx lumpability)
    |
    v
Forman-Ricci Flow + Fermi Quench (4/4 b1=1 -> 100% blankets)
    |
    v
JAX SGLD Engine (23.1% zero-shot transfer on ARC evaluation)
```

---

## Key Results

| Milestone | Metric | Source File |
|-----------|--------|------------|
| Lifshitz transition observed | CS: 0.01 -> 182,697,227 | `lifshitz_transition_experiment.py` |
| Flat torus geometry confirmed | Gauss K ~ 10^-8 | `grokking_manifold_surgery.py` |
| Kramers speedup validated | 5.6x (epoch 2200 -> 390) | `grokking_manifold_surgery_fast.py` |
| Topological diagnosis | 34/34 b1=0 | `betti_autopsy.py` |
| Blanket formation achieved | 4/4 b1>=1 (100%) | `betti_autopsy.py` (post-V2) |
| ARC zero-shot transfer | 23.1% (12/52) | `jax_arc_runner.py` |
| Atlas hits = solves | 12/12 (100%) | `jax_arc_runner.py` |
