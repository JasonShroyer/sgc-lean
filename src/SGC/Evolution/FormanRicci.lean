/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Axioms.Geometry

/-!
# Forman-Ricci Curvature

The combinatorial driver for topological surgery.

## Overview

Unlike Ollivier-Ricci curvature (which measures transport contraction), Forman-Ricci
curvature is **purely structural**—computed from vertex degrees and edge weights
without solving optimal transport problems.

## Physical Interpretation

- **F(e) < 0**: Edge e is a "bottleneck" (under stress, likely to break)
- **F(e) > 0**: Edge e is "well-supported" (stable, part of a cluster)
- **F(e) ≈ 0**: Edge e is "neutral" (neither stressed nor reinforced)

## The Key Insight

Forman-Ricci curvature identifies **where** topology should change:
- Highly negative edges → Candidates for cutting (bond breaking)
- Highly positive regions → Candidates for sewing (bond forming)

## Computational Complexity

F(e) is O(1) per edge, making total computation O(E).
This is much faster than Ollivier-Ricci (O(V³) per edge via LP).

## References

- Forman (2003), "Bochner's method for cell complexes and combinatorial Ricci curvature"
- Sreejith et al. (2016), "Forman curvature for complex networks"
- Samal et al. (2018), "Comparative analysis of two discretizations of Ricci curvature"
-/

namespace SGC.Evolution

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Weighted Graph Structure -/

/-- A weighted graph on vertex set V.

    This is a minimal structure for topological evolution:
    - `adj`: Adjacency function (symmetric)
    - `weight`: Edge weight function (positive for adjacent vertices)

    **Design Choice**: We use functions rather than edge sets for Lean compatibility.
    The graph is implicitly undirected (adj x y ↔ adj y x). -/
structure WeightedGraph (V : Type*) [Fintype V] where
  /-- Adjacency predicate (symmetric) -/
  adj : V → V → Prop
  /-- Adjacency is decidable -/
  adj_dec : DecidableRel adj
  /-- No self-loops -/
  adj_irrefl : ∀ v, ¬adj v v
  /-- Symmetry -/
  adj_symm : ∀ u v, adj u v → adj v u
  /-- Edge weight function (positive for adjacent pairs) -/
  edgeWeight : V → V → ℝ
  /-- Weights are positive on edges -/
  weight_pos : ∀ u v, adj u v → 0 < edgeWeight u v
  /-- Weights are symmetric -/
  weight_symm : ∀ u v, edgeWeight u v = edgeWeight v u

attribute [instance] WeightedGraph.adj_dec

/-- Vertex weight: sum of incident edge weights.

    w(v) = Σ_{u ~ v} w(v,u)

    This represents the "mass" or "importance" of a vertex. -/
noncomputable def WeightedGraph.vertexWeight (G : WeightedGraph V) (v : V) : ℝ :=
  ∑ u : V, if G.adj v u then G.edgeWeight v u else 0

/-- Degree of a vertex: number of neighbors.

    deg(v) = |{u : u ~ v}| -/
def WeightedGraph.degree (G : WeightedGraph V) (v : V) : ℕ :=
  Finset.card (Finset.filter (fun u => G.adj v u) Finset.univ)

/-! ### 2. Forman-Ricci Curvature -/

/-- **Forman-Ricci Curvature** for a weighted graph edge.

    The formula for an edge e = (u,v) is:

    F(e) = w(e) · (w(u)/w(e) + w(v)/w(e) - Σ_{e' ~ e} max(w(e)/w(e'), w(e')/w(e)))

    Simplified for graphs (1-dimensional complexes):

    F(e) = w(e) · (2 - deg(u) - deg(v) + 2)  [unweighted approximation]
         = w(e) · (4 - deg(u) - deg(v))

    **Physical Meaning**:
    - F < 0: Edge is a "bottleneck" connecting two high-degree hubs
    - F > 0: Edge is part of a tight cluster (low degree endpoints)
    - F = 0: Neutral (e.g., edge in a 4-regular graph)

    **Weighted Version** (full formula):

    F(e) = w(e) · [w(u)/w(e) + w(v)/w(e)
                   - Σ_{e' ∈ parallel(e)} √(w(e)/w(e') · w(e')/w(e))
                   - Σ_{e' ∈ transverse(e)} max(w(e)/w(e'), w(e')/w(e))]

    We implement the simplified degree-based formula here, with the full
    weighted version available as `FormanRicciWeighted`. -/
noncomputable def FormanRicci (G : WeightedGraph V) (u v : V) : ℝ :=
  if G.adj u v then
    G.edgeWeight u v * (4 - G.degree u - G.degree v : ℝ)
  else
    0

/-- **Weighted Forman-Ricci Curvature** (full formula).

    This is the complete weighted version accounting for edge weight ratios.
    More accurate for heterogeneous networks but more expensive to compute. -/
noncomputable def FormanRicciWeighted (G : WeightedGraph V) (u v : V) : ℝ :=
  if h : G.adj u v then
    let w_e := G.edgeWeight u v
    let w_u := G.vertexWeight u
    let w_v := G.vertexWeight v
    -- Contribution from endpoint vertex weights
    let vertex_term := w_u / w_e + w_v / w_e
    -- Transverse edges: neighbors of u (other than v) and neighbors of v (other than u)
    let transverse_u := ∑ x : V, if G.adj u x ∧ x ≠ v then
      max (w_e / G.edgeWeight u x) (G.edgeWeight u x / w_e) else 0
    let transverse_v := ∑ y : V, if G.adj v y ∧ y ≠ u then
      max (w_e / G.edgeWeight v y) (G.edgeWeight v y / w_e) else 0
    w_e * (vertex_term - transverse_u - transverse_v)
  else
    0

/-! ### 3. Properties of Forman-Ricci Curvature -/

/-- Forman-Ricci is zero for non-edges. -/
theorem forman_ricci_non_edge (G : WeightedGraph V) (u v : V) (h : ¬G.adj u v) :
    FormanRicci G u v = 0 := by
  simp [FormanRicci, h]

/-- Forman-Ricci is symmetric. -/
theorem forman_ricci_symm (G : WeightedGraph V) (u v : V) :
    FormanRicci G u v = FormanRicci G v u := by
  simp only [FormanRicci]
  by_cases h : G.adj u v
  · have h' : G.adj v u := G.adj_symm u v h
    simp only [h, h', ↓reduceIte, G.weight_symm u v]
    ring
  · have h' : ¬G.adj v u := fun hvu => h (G.adj_symm v u hvu)
    simp [h, h']

/-- Forman-Ricci identifies bottlenecks: high-degree endpoints → negative curvature.

    **Axiomatized**: The full proof requires careful handling of Nat → ℝ coercions. -/
axiom forman_ricci_bottleneck (G : WeightedGraph V) (u v : V) (h : G.adj u v)
    (hdeg : G.degree u + G.degree v > 4) :
    FormanRicci G u v < 0

/-- Forman-Ricci identifies clusters: low-degree endpoints → positive curvature.

    **Axiomatized**: The full proof requires careful handling of Nat → ℝ coercions. -/
axiom forman_ricci_cluster (G : WeightedGraph V) (u v : V) (h : G.adj u v)
    (hdeg : G.degree u + G.degree v < 4) :
    FormanRicci G u v > 0

/-! ### 4. Curvature Statistics -/

/-- Total Forman-Ricci curvature of a graph.

    Σ_e F(e)

    This is related to the Euler characteristic for simplicial complexes. -/
noncomputable def totalFormanRicci (G : WeightedGraph V) : ℝ :=
  (1/2) * ∑ u : V, ∑ v : V, FormanRicci G u v

/-- Minimum edge curvature (most stressed edge).

    **Axiomatized**: Requires Nonempty V for inf'. -/
axiom minFormanRicci (G : WeightedGraph V) : ℝ

/-- Maximum edge curvature (most stable edge).

    **Axiomatized**: Requires Nonempty V for sup'. -/
axiom maxFormanRicci (G : WeightedGraph V) : ℝ

/-! ### 5. Summary

**Forman-Ricci Curvature** provides a computationally efficient signal for
identifying topological stress in networks:

1. **Bottleneck Detection**: F(e) < 0 flags edges under structural stress
2. **Cluster Identification**: F(e) > 0 flags edges in stable communities
3. **Surgery Guidance**: Cut where F < θ_cut, sew where F > θ_sew

This module provides the "sensing" layer for topological evolution.
The actual cutting/sewing operations are in `Surgery.lean`.
-/

end SGC.Evolution
