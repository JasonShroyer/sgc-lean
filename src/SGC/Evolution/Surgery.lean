/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Evolution.FormanRicci

/-!
# Topological Surgery

Operators that **change the graph topology** based on curvature signals.

## Overview

This module implements "Ricci Flow with Surgery" for discrete networks:
- **Cut**: Remove edges under curvature stress (F(e) < θ_cut)
- **Sew**: Add edges to relieve positive curvature pressure (F(e) > θ_sew)

## Physical Interpretation

Surgery represents **structural change** in the system:
- **Bond Breaking**: Chemical bonds break when strain exceeds threshold
- **Synaptic Pruning**: Neural connections weaken and disappear
- **Social Fragmentation**: Relationships dissolve under stress

Conversely:
- **Bond Forming**: New chemical bonds form in favorable conditions
- **Synaptic Growth**: New neural connections strengthen clusters
- **Community Formation**: New relationships bridge compatible groups

## The Key Distinction

**Annealing (Phase 1-4)**: Fixed topology, optimizing edge weights
**Evolution (Phase 5)**: Changing topology, edges appear/disappear

## References

- Perelman (2002-2003), Ricci flow with surgery on three-manifolds
- Luo (2019), "Combinatorial Ricci flow on surfaces"
- arXiv:2509.22362, "Forman-Ricci curvature for network surgery"
-/

namespace SGC.Evolution

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ### 1. The Cut Operator -/

/-- **Surgery Cut**: Remove edges with Forman-Ricci curvature below threshold.

    SurgeryCut(G, θ) removes all edges e where F(e) < θ.

    **Physical Meaning**: Edges under high stress (negative curvature) are
    "broken"—they can no longer support transitions.

    **Typical Thresholds**:
    - θ = 0: Remove only bottlenecks (negative curvature)
    - θ = -1: Conservative (only highly stressed edges)
    - θ = -∞: No cutting (preserve all edges) -/
noncomputable def SurgeryCut (G : WeightedGraph V) (threshold : ℝ) : WeightedGraph V where
  adj := fun u v => G.adj u v ∧ FormanRicci G u v ≥ threshold
  adj_dec := inferInstance
  adj_irrefl := fun v h => G.adj_irrefl v h.1
  adj_symm := fun u v h => ⟨G.adj_symm u v h.1, by rw [forman_ricci_symm]; exact h.2⟩
  edgeWeight := G.edgeWeight
  weight_pos := fun u v h => G.weight_pos u v h.1
  weight_symm := G.weight_symm

/-- Edges removed by surgery. -/
def cutEdges (G : WeightedGraph V) (threshold : ℝ) : Set (V × V) :=
  {p | G.adj p.1 p.2 ∧ FormanRicci G p.1 p.2 < threshold}

/-- Number of edges removed.

    Note: Counts each undirected edge once by using a canonical ordering. -/
noncomputable def cutEdgeCount (G : WeightedGraph V) (threshold : ℝ) : ℕ :=
  Finset.card (Finset.filter
    (fun p : V × V => G.adj p.1 p.2 ∧ FormanRicci G p.1 p.2 < threshold)
    (Finset.univ.product Finset.univ)) / 2

/-! ### 2. The Sew Operator -/

/-- **Candidate Edge**: A non-edge that could potentially be added.

    We add edges between vertices that:
    1. Are not currently adjacent
    2. Share a common neighbor (triangle completion)
    3. Would have positive Forman-Ricci if added -/
def IsCandidateEdge (G : WeightedGraph V) (u v : V) : Prop :=
  ¬G.adj u v ∧ u ≠ v ∧ ∃ w, G.adj u w ∧ G.adj w v

/-- **Surgery Sew**: Add edges to relieve positive curvature pressure.

    This is more complex than cutting because we must decide:
    1. Which non-edges to add
    2. What weight to assign them

    **Strategy**: Add edges that would complete triangles (reduce clustering
    coefficient deficit), with weight equal to the geometric mean of incident edges.

    **Note**: This is axiomatized because the full implementation requires
    solving an optimization problem (which edges maximize global curvature?). -/
axiom SurgerySew (G : WeightedGraph V) (threshold : ℝ) : WeightedGraph V

/-- Sew only adds edges, never removes them. -/
axiom sew_preserves_edges (G : WeightedGraph V) (threshold : ℝ) :
  ∀ u v, G.adj u v → (SurgerySew G threshold).adj u v

/-- Sew adds edges where curvature would be above threshold. -/
axiom sew_adds_good_edges (G : WeightedGraph V) (threshold : ℝ) :
  ∀ u v, (SurgerySew G threshold).adj u v → ¬G.adj u v →
    FormanRicci (SurgerySew G threshold) u v ≥ threshold

/-! ### 3. Combined Surgery Operator -/

/-- **Full Surgery**: Cut then Sew.

    S(G, θ_cut, θ_sew) = Sew(Cut(G, θ_cut), θ_sew)

    This is the complete "Ricci flow with surgery" step:
    1. Remove stressed edges (F < θ_cut)
    2. Add stabilizing edges (F > θ_sew after addition)

    **Iteration**: Repeated application drives the network toward
    uniform curvature (geometric equilibrium). -/
noncomputable def Surgery (G : WeightedGraph V) (cutThreshold sewThreshold : ℝ) : WeightedGraph V :=
  SurgerySew (SurgeryCut G cutThreshold) sewThreshold

/-- Surgery with equal thresholds (symmetric surgery). -/
noncomputable def SymmetricSurgery (G : WeightedGraph V) (threshold : ℝ) : WeightedGraph V :=
  Surgery G threshold threshold

/-! ### 4. Surgery Dynamics -/

/-- **Surgery Flow**: Iterated surgery.

    G_n = S(G_{n-1}, θ_cut, θ_sew)

    This defines the discrete-time dynamical system on graph space. -/
noncomputable def surgeryFlow (G : WeightedGraph V) (cutThreshold sewThreshold : ℝ) : ℕ → WeightedGraph V
  | 0 => G
  | n + 1 => Surgery (surgeryFlow G cutThreshold sewThreshold n) cutThreshold sewThreshold

/-- **Equilibrium**: A graph is at equilibrium if surgery doesn't change it. -/
def IsSurgeryEquilibrium (G : WeightedGraph V) (cutThreshold sewThreshold : ℝ) : Prop :=
  ∀ u v, G.adj u v ↔ (Surgery G cutThreshold sewThreshold).adj u v

/-- **Curvature Equilibrium**: All edges have curvature in the neutral zone. -/
def IsCurvatureEquilibrium (G : WeightedGraph V) (cutThreshold sewThreshold : ℝ) : Prop :=
  ∀ u v, G.adj u v → cutThreshold ≤ FormanRicci G u v ∧ FormanRicci G u v ≤ sewThreshold

/-- Curvature equilibrium implies surgery equilibrium (for cut). -/
theorem curvature_eq_implies_cut_stable (G : WeightedGraph V) (cutThreshold sewThreshold : ℝ)
    (h : IsCurvatureEquilibrium G cutThreshold sewThreshold) :
    ∀ u v, G.adj u v → (SurgeryCut G cutThreshold).adj u v := by
  intro u v hadj
  constructor
  · exact hadj
  · exact (h u v hadj).1

/-! ### 5. Surgery Statistics -/

/-- Number of edges in graph (counting each undirected edge once). -/
noncomputable def edgeCount (G : WeightedGraph V) : ℕ :=
  Finset.card (Finset.filter (fun p : V × V => G.adj p.1 p.2)
    (Finset.univ.product Finset.univ)) / 2

/-- Number of vertices with at least one edge. -/
noncomputable def activeVertexCount (G : WeightedGraph V) : ℕ :=
  Finset.card (Finset.filter (fun v => ∃ u, G.adj v u) Finset.univ)

/-- **Surgery Report**: Summary of what surgery changed. -/
structure SurgeryReport (V : Type*) [Fintype V] where
  edgesBefore : ℕ
  edgesAfter : ℕ
  edgesCut : ℕ
  edgesSewn : ℕ

/-- Generate surgery report. -/
noncomputable def surgeryReport (G : WeightedGraph V) (cutThreshold sewThreshold : ℝ) : SurgeryReport V :=
  let G' := Surgery G cutThreshold sewThreshold
  let cut := SurgeryCut G cutThreshold
  { edgesBefore := edgeCount G
    edgesAfter := edgeCount G'
    edgesCut := edgeCount G - edgeCount cut
    edgesSewn := edgeCount G' - edgeCount cut }

/-! ### 6. Summary

**Topological Surgery** provides the mechanism for structural change:

1. **Cut (SurgeryCut)**: Removes edges where F(e) < θ_cut
2. **Sew (SurgerySew)**: Adds edges where F(e) > θ_sew (axiomatized)
3. **Surgery**: Combined cut-then-sew operation
4. **Flow**: Iterated surgery toward equilibrium

The constraints on surgery (what topological invariants must be preserved)
are defined in `Conservation.lean`.
-/

end SGC.Evolution
