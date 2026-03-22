"""
ARC-SGC Phase 21-31: Spectral Dynamics (Lie Group Actions on Clusters)

THEORETICAL FOUNDATION:
Phase 20 was "binary" - Perfect vs. Fail.
Phase 21 treats truth as a SPECTRUM on a statistical manifold.
Phase 22 refines NEAR-MISSES via gradient descent on the Lie group.
Phase 23 performs STRUCTURAL EXPANSION via Lie Bracket composition.
Phase 24 INDUCES missing generators from the difference field.
Phase 25 IMPLEMENTS the discovered physics (enclosures, shifts).
Phase 26 ITERATES: Multi-pass solving with physics propagation.
Phase 27 LIFTS reasoning from Pixel domain to Object domain.
Phase 28 DISCOVERS interactions: Objects are nodes, connections are edges.
Phase 29 GENERALIZES interactions: Graph Grammars (L -> R rewriting rules).
Phase 30 LEARNS logic: Spectral decomposition reveals hidden concept clusters.
Phase 31 MOVES clusters: Lie Group actions (translate, extend) on eigenvector sections.

THE SHIFT:
- Phase 20: Submit only if Energy < threshold (hard filter)
- Phase 21: Submit BEST candidate by geodesic distance (soft ranking)
- Phase 22: REFINE near-misses (0 < F < 0.1) via parameter perturbation
- Phase 23: EXPAND structure when gradients stall via operator composition
- Phase 24: INDUCE new operators from the residual delta (learn the generators)
- Phase 25: IMPLEMENT discovered physics (fill_holes, hollow, shift)
- Phase 26: ITERATE with multi-pass solving and contextual parameters
- Phase 27: OBJECT ABSTRACTION - per-object operations (Renormalization)

INFORMATION GEOMETRY PRINCIPLES:

1. FISHER-RAO METRIC:
   - The natural metric on the manifold of probability distributions
   - Measures "structural divergence" not just pixel differences
   - A 1-pixel shift is "close"; random scatter is "far"

2. WAVELET INVARIANCE (Hermite-Gaussian):
   - Eigenfunctions of the quantum harmonic oscillator
   - Optimal for detecting multi-scale structure
   - If Wavelet(Input) ≈ Wavelet(Output) after transform, that's the geodesic

3. GEODESIC SUBMISSION:
   - Always return the candidate with minimum Fisher-Rao distance
   - Even "imperfect" solutions contain information
   - Log the distance for empirical constant discovery

4. MANIFOLD GRADIENT DESCENT (Phase 22):
   - Near-miss = correct global symmetry, wrong local parameter
   - Perturb parameters: Stop conditions, boundary offsets, color variants
   - Flow down the energy landscape to the fixed point
   - Critical Distance (0.0071) = radius of basin of attraction

5. STRUCTURAL LIE ALGEBRA EXPANSION (Phase 23):
   - When MGD stalls (gradient flat), the solution requires a TOPOLOGY change
   - Apply Lie Bracket: [A, B] = A ∘ B - B ∘ A
   - Compose current candidate with group generators (Gravity, Crop, Color, Rotate)
   - This is "adding a term to the Hamiltonian" - structural, not parametric

6. OPERATOR INDUCTION (Phase 24):
   - The Inverse Problem: If f(x) ≠ y but D(f(x), y) is small, then y = (G ∘ f)(x)
   - Solve for G by analyzing the difference field: delta = target - candidate
   - Categorize delta: Spatial (tiling), Color (conditional), Topological (hollow/fill)
   - Promote frequently-induced operators to first-class generators
   - This is DICTIONARY LEARNING on the Lie group structure

SGC GROUNDING:
- Fisher-Rao ≈ Natural metric on statistical manifold (Amari)
- Hermite-Gaussian ≈ Coherent states in phase space
- Geodesic ≈ Shortest path in the symmetry group
- Empirical constants ≈ Coupling constants of the ARC "field theory"
- MGD ≈ Renormalization Group flow toward fixed point
- Lie Bracket ≈ Commutator generating new symmetries
- Operator Induction ≈ Sparse coding / dictionary learning on group structure

GOAL:
Discover the "constants of the ARC universe" by measuring distances
on the information manifold, not just counting errors.
Convert near-misses to perfect solves via gradient descent, structural expansion,
AND operator induction (learning missing generators from residuals).
"""

import torch
import torch.nn.functional as F
import numpy as np
import json
import os
import math
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Set, Any, Callable
from collections import Counter
from pathlib import Path
from scipy import ndimage
from scipy.fft import dct

import sys
sys.path.insert(0, str(Path(__file__).parent))

from arc_sgc_phase20 import (
    Phase20Solver, RuleRegistry, TaskSignatureExtractor,
    ARCGrid, ARCTask, ARCExample, ARCPhase83Config,
    Program, CandidateSolution, load_arc_tasks
)

from arc_sgc_phase19 import Phase19Solver, FractalDecomposer
from arc_sgc_phase15 import SelfImprovingSolver, CEGARLoop


# =============================================================================
# PHASE 22: THE THERMODYNAMIC AGENT
# =============================================================================
# Theory: Intelligence is not passive perception but active inference.
# We don't just measure distances - we FLOW down the energy landscape.
#
# Friston's FEP: Minimize Expected Free Energy by adapting sensory precision
# Vanchurin's Thermodynamics: Learning = annealing the metric tensor
# Aguera y Arcas: Intelligence = prediction + action in a compounding loop
# =============================================================================


# =============================================================================
# COMPONENT 1: ADAPTIVE FISHER-RAO METRIC
# =============================================================================

class AdaptiveFisherRaoMetric:
    """
    Phase 22: Dynamic Fisher-Rao metric with adaptive attention weights.
    
    The key insight from Friston/Vanchurin: The metric weights are not
    constants - they are DYNAMICAL VARIABLES that must evolve to match
    the task's symmetry group.
    
    This is "Active Perception" - the system tunes its sensory precision
    to maximize information gain for the specific task at hand.
    """
    
    def __init__(self):
        # Initial uniform weights - will be adapted per task
        self.weights = {
            'histogram': 0.25,
            'topology': 0.25,
            'gradient': 0.25,
            'spectral': 0.25
        }
        
        # Persistent weight evolution across tasks (Thermodynamic Memory)
        self.weight_history: List[Dict[str, float]] = []
        self.success_correlations: Dict[str, float] = {
            'histogram': 0.0,
            'topology': 0.0,
            'gradient': 0.0,
            'spectral': 0.0
        }
        
        # Temperature for weight annealing (high = explore, low = exploit)
        self.temperature = 1.0
    
    def adapt_to_task(self, task: ARCTask) -> Dict[str, float]:
        """
        Adapt metric weights based on task characteristics.
        
        This is Active Perception: probe training examples to determine
        which distance components are most discriminative for this task.
        """
        if not task.train_examples:
            return self.weights
        
        # Compute discriminability of each component
        discriminability = {k: 0.0 for k in self.weights}
        
        for ex in task.train_examples:
            inp, out = ex.input_grid, ex.output_grid
            
            if inp.shape != out.shape:
                # Shape change signals geometric transformation
                discriminability['topology'] += 0.4
                discriminability['spectral'] += 0.4
                discriminability['gradient'] += 0.1
                discriminability['histogram'] += 0.1
                continue
            
            # Measure each component's contribution to the transformation
            d_hist = self._histogram_distance(inp, out)
            d_topo = self._topological_distance(inp, out)
            d_grad = self._gradient_distance(inp, out)
            d_spec = self._spectral_distance(inp, out)
            
            # Higher distance = more information in this channel
            total = d_hist + d_topo + d_grad + d_spec + 1e-8
            discriminability['histogram'] += d_hist / total
            discriminability['topology'] += d_topo / total
            discriminability['gradient'] += d_grad / total
            discriminability['spectral'] += d_spec / total
        
        # Softmax with temperature to sharpen attention
        n = len(task.train_examples)
        if n > 0:
            scores = {k: v / n for k, v in discriminability.items()}
            exp_scores = {k: math.exp(v / self.temperature) for k, v in scores.items()}
            total_exp = sum(exp_scores.values())
            self.weights = {k: v / total_exp for k, v in exp_scores.items()}
        
        self.weight_history.append(self.weights.copy())
        return self.weights
    
    def compute(self, grid_a: ARCGrid, grid_b: ARCGrid) -> Dict[str, float]:
        """Compute weighted Fisher-Rao distance."""
        if grid_a.shape != grid_b.shape:
            shape_diff = self._shape_distance(grid_a.shape, grid_b.shape)
            return {
                'total': 0.5 + 0.5 * shape_diff,
                'histogram': 1.0, 'topology': 1.0,
                'gradient': 1.0, 'spectral': 1.0,
                'shape_mismatch': True
            }
        
        d_hist = self._histogram_distance(grid_a, grid_b)
        d_topo = self._topological_distance(grid_a, grid_b)
        d_grad = self._gradient_distance(grid_a, grid_b)
        d_spec = self._spectral_distance(grid_a, grid_b)
        
        total = (
            self.weights['histogram'] * d_hist +
            self.weights['topology'] * d_topo +
            self.weights['gradient'] * d_grad +
            self.weights['spectral'] * d_spec
        )
        
        return {
            'total': total,
            'histogram': d_hist, 'topology': d_topo,
            'gradient': d_grad, 'spectral': d_spec,
            'shape_mismatch': False
        }
    
    def anneal_from_result(self, was_perfect: bool, component_distances: Dict[str, float]):
        """
        Thermodynamic annealing: update weights based on solve success.
        
        If a component had low distance and we succeeded, boost it.
        If a component had low distance but we failed, it was misleading.
        """
        learning_rate = 0.1 if was_perfect else 0.05
        
        for comp in ['histogram', 'topology', 'gradient', 'spectral']:
            d = component_distances.get(comp, 0.5)
            
            if was_perfect:
                # Low distance components predicted success - boost them
                self.success_correlations[comp] += (1.0 - d) * learning_rate
            else:
                # Components with low distance were misleading
                self.success_correlations[comp] -= (1.0 - d) * learning_rate * 0.3
        
        # Gradually incorporate correlations into weights
        blend = 0.1
        for comp in self.weights:
            # Shift weight toward components with high success correlation
            target = 0.25 + 0.5 * max(0, self.success_correlations[comp])
            self.weights[comp] = (1 - blend) * self.weights[comp] + blend * target
        
        # Renormalize
        total = sum(self.weights.values())
        self.weights = {k: v / total for k, v in self.weights.items()}
        
        # Anneal temperature (cool down over time)
        self.temperature = max(0.3, self.temperature * 0.99)
    
    def _shape_distance(self, s1: Tuple[int, int], s2: Tuple[int, int]) -> float:
        h_diff = abs(s1[0] - s2[0]) / max(s1[0], s2[0])
        w_diff = abs(s1[1] - s2[1]) / max(s1[1], s2[1])
        return (h_diff + w_diff) / 2
    
    def _histogram_distance(self, g1: ARCGrid, g2: ARCGrid) -> float:
        """Jensen-Shannon divergence between color histograms."""
        h1 = torch.bincount(g1.data.flatten().long(), minlength=10).float()
        h2 = torch.bincount(g2.data.flatten().long(), minlength=10).float()
        h1 = h1 / (h1.sum() + 1e-8)
        h2 = h2 / (h2.sum() + 1e-8)
        m = 0.5 * (h1 + h2)
        eps = 1e-8
        kl1 = torch.sum(h1 * torch.log((h1 + eps) / (m + eps)))
        kl2 = torch.sum(h2 * torch.log((h2 + eps) / (m + eps)))
        return min(1.0, (0.5 * (kl1 + kl2)).item() / math.log(2))
    
    def _topological_distance(self, g1: ARCGrid, g2: ARCGrid) -> float:
        """Distance based on connected component structure."""
        def count_objects(g):
            data = g.data.numpy()
            counts = {}
            for c in range(10):
                mask = (data == c).astype(np.int32)
                if mask.sum() > 0:
                    _, n = ndimage.label(mask)
                    counts[c] = n
            return counts
        
        c1, c2 = count_objects(g1), count_objects(g2)
        all_colors = set(c1.keys()) | set(c2.keys())
        if not all_colors:
            return 0.0
        
        diff = sum(abs(c1.get(c, 0) - c2.get(c, 0)) / (c1.get(c, 0) + c2.get(c, 0) + 1e-8)
                   for c in all_colors)
        return min(1.0, diff / len(all_colors))
    
    def _gradient_distance(self, g1: ARCGrid, g2: ARCGrid) -> float:
        """Distance based on edge structure."""
        d1 = g1.data.float().unsqueeze(0).unsqueeze(0)
        d2 = g2.data.float().unsqueeze(0).unsqueeze(0)
        
        sobel_h = torch.tensor([[-1., 0., 1.], [-2., 0., 2.], [-1., 0., 1.]]).view(1,1,3,3)
        sobel_v = torch.tensor([[-1., -2., -1.], [0., 0., 0.], [1., 2., 1.]]).view(1,1,3,3)
        
        try:
            g1h, g1v = F.conv2d(d1, sobel_h, padding=1), F.conv2d(d1, sobel_v, padding=1)
            g2h, g2v = F.conv2d(d2, sobel_h, padding=1), F.conv2d(d2, sobel_v, padding=1)
            m1 = torch.sqrt(g1h**2 + g1v**2)
            m2 = torch.sqrt(g2h**2 + g2v**2)
            m1 = m1 / (m1.max() + 1e-8)
            m2 = m2 / (m2.max() + 1e-8)
            return torch.mean(torch.abs(m1 - m2)).item()
        except:
            return float(torch.mean((d1 != d2).float()).item())
    
    def _spectral_distance(self, g1: ARCGrid, g2: ARCGrid) -> float:
        """Distance in DCT frequency domain."""
        d1 = g1.data.float().numpy()
        d2 = g2.data.float().numpy()
        try:
            dct1 = dct(dct(d1, axis=0, norm='ortho'), axis=1, norm='ortho')
            dct2 = dct(dct(d2, axis=0, norm='ortho'), axis=1, norm='ortho')
            h, w = d1.shape
            hh, wh = max(1, h//2), max(1, w//2)
            l1 = dct1[:hh, :wh].flatten()
            l2 = dct2[:hh, :wh].flatten()
            l1 = l1 / (np.linalg.norm(l1) + 1e-8)
            l2 = l2 / (np.linalg.norm(l2) + 1e-8)
            return 1.0 - max(0.0, min(1.0, np.dot(l1, l2)))
        except:
            return 0.5


# =============================================================================
# COMPONENT 2: LIE ALGEBRA DECOMPOSER
# =============================================================================

@dataclass
class LieGenerator:
    """A generator of the ARC transformation Lie algebra."""
    name: str
    category: str  # 'translation', 'rotation', 'color', 'topology'
    apply: Callable[[torch.Tensor, float], torch.Tensor]
    parameter_range: Tuple[float, float] = (-1.0, 1.0)


class LieAlgebraDecomposer:
    """
    Phase 22: Decompose residuals into Lie algebra generators.
    
    Instead of searching discrete rules, we find the continuous parameters
    θ such that: Output ≈ exp(Σ θ_j G_j) · Input
    
    The generators G_j form the basis of our transformation Lie algebra:
    - L_x, L_y: Translation generators
    - R: Rotation generator  
    - C_ij: Color permutation generators
    - S: Scaling/crop generator
    """
    
    def __init__(self):
        self.generators = self._build_generators()
        self.induced_generators: List[LieGenerator] = []
    
    def _build_generators(self) -> List[LieGenerator]:
        """Build the fundamental generators of ARC transformations."""
        generators = []
        
        # Translation generators (discrete shifts)
        def shift_right(grid: torch.Tensor, amount: float) -> torch.Tensor:
            n = int(round(amount))
            if n == 0: return grid
            result = torch.zeros_like(grid)
            if n > 0 and n < grid.shape[1]:
                result[:, n:] = grid[:, :-n]
            elif n < 0 and -n < grid.shape[1]:
                result[:, :n] = grid[:, -n:]
            return result
        
        def shift_down(grid: torch.Tensor, amount: float) -> torch.Tensor:
            n = int(round(amount))
            if n == 0: return grid
            result = torch.zeros_like(grid)
            if n > 0 and n < grid.shape[0]:
                result[n:, :] = grid[:-n, :]
            elif n < 0 and -n < grid.shape[0]:
                result[:n, :] = grid[-n:, :]
            return result
        
        generators.append(LieGenerator('L_x', 'translation', shift_right, (-5, 5)))
        generators.append(LieGenerator('L_y', 'translation', shift_down, (-5, 5)))
        
        # Rotation generator (discrete 90° steps)
        def rotate(grid: torch.Tensor, amount: float) -> torch.Tensor:
            k = int(round(amount)) % 4
            return torch.rot90(grid, k=k)
        
        generators.append(LieGenerator('R', 'rotation', rotate, (0, 3)))
        
        # Flip generators
        def flip_h(grid: torch.Tensor, amount: float) -> torch.Tensor:
            return torch.flip(grid, dims=[1]) if amount > 0.5 else grid
        
        def flip_v(grid: torch.Tensor, amount: float) -> torch.Tensor:
            return torch.flip(grid, dims=[0]) if amount > 0.5 else grid
        
        generators.append(LieGenerator('F_h', 'rotation', flip_h, (0, 1)))
        generators.append(LieGenerator('F_v', 'rotation', flip_v, (0, 1)))
        
        # Color swap generators
        for src in range(10):
            for dst in range(10):
                if src != dst:
                    def make_color_swap(s, d):
                        def swap(grid: torch.Tensor, amount: float) -> torch.Tensor:
                            if amount < 0.5: return grid
                            result = grid.clone()
                            result[grid == s] = d
                            return result
                        return swap
                    generators.append(LieGenerator(
                        f'C_{src}_{dst}', 'color', 
                        make_color_swap(src, dst), (0, 1)
                    ))
        
        return generators
    
    def decompose_residual(
        self, 
        input_grid: torch.Tensor, 
        target_grid: torch.Tensor,
        candidate_grid: torch.Tensor
    ) -> List[Tuple[LieGenerator, float]]:
        """
        Decompose the residual (target - candidate) into generator components.
        
        Returns list of (generator, coefficient) pairs that best explain
        how to transform the candidate into the target.
        """
        if candidate_grid.shape != target_grid.shape:
            return []
        
        residual = (target_grid != candidate_grid).float()
        if residual.sum() == 0:
            return []  # Already perfect
        
        # Try each generator and measure how well it explains the residual
        explanations = []
        
        for gen in self.generators[:20]:  # Limit to avoid explosion
            best_param = 0.0
            best_reduction = 0.0
            
            # Search parameter space
            low, high = gen.parameter_range
            for param in np.linspace(low, high, 7):
                try:
                    transformed = gen.apply(candidate_grid, param)
                    if transformed.shape != target_grid.shape:
                        continue
                    
                    new_residual = (target_grid != transformed).float()
                    reduction = residual.sum() - new_residual.sum()
                    
                    if reduction > best_reduction:
                        best_reduction = reduction
                        best_param = param
                except:
                    continue
            
            if best_reduction > 0:
                explanations.append((gen, best_param, best_reduction.item()))
        
        # Sort by reduction (best explanations first)
        explanations.sort(key=lambda x: -x[2])
        
        return [(gen, param) for gen, param, _ in explanations[:5]]
    
    def induce_generator(
        self, 
        input_grid: torch.Tensor,
        target_grid: torch.Tensor
    ) -> Optional[LieGenerator]:
        """
        Induce a new generator from the input→target transformation.
        
        This is Dictionary Learning on the Lie group structure.
        """
        if input_grid.shape != target_grid.shape:
            return None
        
        diff = (input_grid != target_grid)
        if not diff.any():
            return None
        
        # Analyze the difference pattern
        diff_coords = torch.where(diff)
        if len(diff_coords[0]) == 0:
            return None
        
        # Check for translation pattern
        input_vals = input_grid[diff].tolist()
        target_vals = target_grid[diff].tolist()
        
        # Simple color mapping?
        color_map = {}
        for i, t in zip(input_vals, target_vals):
            if i in color_map and color_map[i] != t:
                color_map = None
                break
            color_map[i] = t
        
        if color_map and len(color_map) <= 3:
            def make_induced_map(cmap):
                def apply_map(grid: torch.Tensor, _: float) -> torch.Tensor:
                    result = grid.clone()
                    for src, dst in cmap.items():
                        result[grid == src] = dst
                    return result
                return apply_map
            
            name = f"induced_color_{'_'.join(f'{k}to{v}' for k,v in color_map.items())}"
            gen = LieGenerator(name, 'color', make_induced_map(color_map), (0, 1))
            self.induced_generators.append(gen)
            return gen
        
        return None


# =============================================================================
# COMPONENT 3: MANIFOLD GRADIENT DESCENT
# =============================================================================

class ManifoldGradientDescent:
    """
    Phase 22: Flow down the energy landscape via continuous optimization.
    
    Instead of discrete rule search, we parameterize transformations
    and minimize the Fisher-Rao distance via gradient-like updates.
    
    This is the "Continuous Propagator" - we FLOW the input into the output.
    """
    
    NEAR_MISS_THRESHOLD = 0.15
    MAX_ITERATIONS = 10
    
    def __init__(self, metric: AdaptiveFisherRaoMetric, decomposer: LieAlgebraDecomposer):
        self.metric = metric
        self.decomposer = decomposer
        self.refinements_attempted = 0
        self.refinements_successful = 0
    
    def refine(
        self,
        candidate: torch.Tensor,
        target: ARCGrid,
        input_grid: torch.Tensor
    ) -> Optional[torch.Tensor]:
        """
        Refine a near-miss candidate by flowing down the energy landscape.
        
        Uses the Lie algebra decomposition to find the direction of steepest
        descent, then takes steps in that direction.
        """
        if candidate.shape != target.shape:
            return None
        
        # Check if this is a near-miss worth refining
        candidate_grid = ARCGrid(candidate)
        dist = self.metric.compute(candidate_grid, target)
        
        if dist['total'] <= 0 or dist['total'] >= self.NEAR_MISS_THRESHOLD:
            return None
        
        self.refinements_attempted += 1
        
        current = candidate.clone()
        best = candidate.clone()
        best_dist = dist['total']
        
        for iteration in range(self.MAX_ITERATIONS):
            # Decompose residual into generators
            explanations = self.decomposer.decompose_residual(
                input_grid, target.data, current
            )
            
            if not explanations:
                break
            
            # Apply the best generator
            gen, param = explanations[0]
            
            try:
                new_candidate = gen.apply(current, param)
                if new_candidate.shape != target.shape:
                    continue
                
                new_dist = self.metric.compute(ARCGrid(new_candidate), target)
                
                if new_dist['total'] < best_dist:
                    best = new_candidate.clone()
                    best_dist = new_dist['total']
                    current = new_candidate
                    
                    if best_dist < 0.001:  # Perfect
                        self.refinements_successful += 1
                        return best
                else:
                    # Try other generators
                    improved = False
                    for gen2, param2 in explanations[1:]:
                        try:
                            new_candidate = gen2.apply(current, param2)
                            if new_candidate.shape != target.shape:
                                continue
                            new_dist = self.metric.compute(ARCGrid(new_candidate), target)
                            if new_dist['total'] < best_dist:
                                best = new_candidate.clone()
                                best_dist = new_dist['total']
                                current = new_candidate
                                improved = True
                                break
                        except:
                            continue
                    
                    if not improved:
                        break
            except:
                continue
        
        # Check if we improved significantly
        original_dist = dist['total']
        if best_dist < original_dist * 0.8:
            if best_dist < 0.001:
                self.refinements_successful += 1
            return best
        
        return None
    
    def get_stats(self) -> Dict:
        return {
            'attempted': self.refinements_attempted,
            'successful': self.refinements_successful,
            'rate': self.refinements_successful / max(1, self.refinements_attempted)
        }


# =============================================================================
# COMPONENT 4: THERMODYNAMIC POLICY
# =============================================================================

class ThermodynamicPolicy:
    """
    Phase 22: Active Inference orchestration.
    
    This is the "brain" that coordinates:
    1. Metric adaptation (tune sensory precision)
    2. Candidate generation (explore action space)
    3. Manifold refinement (flow toward solution)
    4. Weight annealing (learn from outcomes)
    
    The policy minimizes Expected Free Energy, not just current error.
    """
    
    def __init__(self):
        self.metric = AdaptiveFisherRaoMetric()
        self.decomposer = LieAlgebraDecomposer()
        self.mgd = ManifoldGradientDescent(self.metric, self.decomposer)
        
        # Action prior over generator families
        self.action_prior = {
            'translation': 0.25,
            'rotation': 0.25,
            'color': 0.25,
            'topology': 0.25
        }
        
        # Memory of task outcomes
        self.task_history: List[Dict] = []
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """
        Solve a task using the Active Inference loop.
        
        1. Adapt metric to task (Active Perception)
        2. Generate candidates (Action)
        3. Refine near-misses (Manifold Flow)
        4. Anneal weights (Learning)
        """
        # Step 1: Adapt metric to this task's symmetry
        self.metric.adapt_to_task(task)
        
        if verbose:
            print(f"  [METRIC] Adapted weights: h={self.metric.weights['histogram']:.2f} "
                  f"t={self.metric.weights['topology']:.2f} "
                  f"g={self.metric.weights['gradient']:.2f} "
                  f"s={self.metric.weights['spectral']:.2f}", flush=True)
        
        # Step 2: Generate candidates
        candidates = self._generate_candidates(task)
        
        if not candidates:
            return self._make_result(task, None, 'no_candidates')
        
        # Step 3: Evaluate and rank by Fisher-Rao distance
        evaluated = []
        for method, pred in candidates:
            if task.train_examples:
                target = task.train_examples[0].output_grid
                dist = self.metric.compute(pred, target)
                evaluated.append((method, pred, dist))
        
        if not evaluated:
            return self._make_result(task, None, 'no_valid_candidates')
        
        # Sort by distance
        evaluated.sort(key=lambda x: x[2]['total'])
        best_method, best_pred, best_dist = evaluated[0]
        
        # Step 4: Attempt refinement if near-miss
        if 0 < best_dist['total'] < self.mgd.NEAR_MISS_THRESHOLD:
            if task.train_examples:
                inp = task.train_examples[0].input_grid.data
                target = task.train_examples[0].output_grid
                
                refined = self.mgd.refine(best_pred.data, target, inp)
                if refined is not None:
                    refined_dist = self.metric.compute(ARCGrid(refined), target)
                    if refined_dist['total'] < best_dist['total']:
                        best_pred = ARCGrid(refined)
                        best_dist = refined_dist
                        best_method = f"{best_method}+mgd"
                        if verbose:
                            print(f"  [MGD] Refined: {best_dist['total']:.4f}", flush=True)
        
        # Step 5: Check if perfect
        is_perfect = False
        if task.train_examples:
            target = task.train_examples[0].output_grid
            if best_pred.shape == target.shape:
                is_perfect = torch.equal(best_pred.data, target.data)
        
        # Step 6: Anneal weights based on outcome
        self.metric.anneal_from_result(is_perfect, best_dist)
        
        return self._make_result(task, best_pred, best_method, best_dist, is_perfect)
    
    def _generate_candidates(self, task: ARCTask) -> List[Tuple[str, ARCGrid]]:
        """Generate candidate transformations."""
        candidates = []
        
        if not task.train_examples:
            return candidates
        
        inp = task.train_examples[0].input_grid
        
        # Identity
        candidates.append(('identity', inp))
        
        # Rotations
        for k in [1, 2, 3]:
            candidates.append((f'rot{k*90}', ARCGrid(torch.rot90(inp.data, k=k))))
        
        # Flips
        candidates.append(('flip_h', ARCGrid(torch.flip(inp.data, dims=[1]))))
        candidates.append(('flip_v', ARCGrid(torch.flip(inp.data, dims=[0]))))
        
        # Shifts
        for dr in [-1, 0, 1]:
            for dc in [-1, 0, 1]:
                if dr == 0 and dc == 0:
                    continue
                shifted = torch.zeros_like(inp.data)
                h, w = inp.data.shape
                src_r = (max(0, -dr), min(h, h - dr))
                src_c = (max(0, -dc), min(w, w - dc))
                dst_r = (max(0, dr), min(h, h + dr))
                dst_c = (max(0, dc), min(w, w + dc))
                if src_r[1] > src_r[0] and src_c[1] > src_c[0]:
                    shifted[dst_r[0]:dst_r[1], dst_c[0]:dst_c[1]] = \
                        inp.data[src_r[0]:src_r[1], src_c[0]:src_c[1]]
                    candidates.append((f'shift({dr},{dc})', ARCGrid(shifted)))
        
        # Color mappings
        colors = inp.data.unique().tolist()
        for src in colors[:5]:
            for dst in range(10):
                if src != dst:
                    mapped = inp.data.clone()
                    mapped[inp.data == src] = dst
                    candidates.append((f'color({src}->{dst})', ARCGrid(mapped)))
        
        # Fill with each color
        for color in range(10):
            filled = torch.full_like(inp.data, color)
            candidates.append((f'fill({color})', ARCGrid(filled)))
        
        return candidates
    
    def _make_result(
        self, 
        task: ARCTask, 
        prediction: Optional[ARCGrid],
        method: str,
        dist: Optional[Dict] = None,
        is_perfect: bool = False
    ) -> Dict:
        return {
            'task_id': task.task_id,
            'method': method,
            'prediction': prediction,
            'fisher_distance': dist['total'] if dist else 1.0,
            'histogram_dist': dist.get('histogram', 1.0) if dist else 1.0,
            'topology_dist': dist.get('topology', 1.0) if dist else 1.0,
            'gradient_dist': dist.get('gradient', 1.0) if dist else 1.0,
            'spectral_dist': dist.get('spectral', 1.0) if dist else 1.0,
            'is_perfect': is_perfect,
            'metric_weights': self.metric.weights.copy()
        }


# =============================================================================
# PHASE 22 SOLVER
# =============================================================================

class Phase22Solver:
    """
    The Thermodynamic Agent: Active Inference on the Solution Manifold.
    
    This solver embodies the theoretical insights from:
    - Friston's Free Energy Principle (minimize expected surprise)
    - Vanchurin's Thermodynamics of Learning (anneal the metric)
    - Aguera y Arcas's compounding intelligence (learn from outcomes)
    """
    
    def __init__(self):
        self.policy = ThermodynamicPolicy()
        self.results: List[Dict] = []
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve a single task using thermodynamic policy."""
        result = self.policy.solve_task(task, verbose)
        self.results.append(result)
        return result
    
    def get_summary(self) -> Dict:
        """Summarize solver performance."""
        perfect = sum(1 for r in self.results if r['is_perfect'])
        near_miss = sum(1 for r in self.results 
                        if 0 < r['fisher_distance'] < 0.1 and not r['is_perfect'])
        
        return {
            'total_tasks': len(self.results),
            'perfect_solves': perfect,
            'near_misses': near_miss,
            'mgd_stats': self.policy.mgd.get_stats(),
            'final_weights': self.policy.metric.weights,
            'temperature': self.policy.metric.temperature
        }


# =============================================================================
# PHASE 23: THE ACTIVE SCIENTIST
# =============================================================================
# The agent doesn't just stare at training pairs - it PLAYS with them.
# By "bouncing" objects under symmetry transformations, it discovers
# the Conservation Laws (invariants) of the puzzle's physics.
# =============================================================================

class SymmetryOracle:
    """
    Phase 23: Test candidate programs for equivariance under symmetry groups.
    
    The D4 dihedral group (8 elements: 4 rotations + 4 reflections) acts
    on ARC grids. A "true" solution should commute with this action:
    
        P(T(x)) = T(P(x))  for all T in D4
    
    If a candidate breaks this equivariance, it's likely overfitting to
    accidental features of the training data.
    """
    
    @staticmethod
    def get_d4_transforms() -> List[Tuple[str, Callable[[torch.Tensor], torch.Tensor]]]:
        """Return the 8 elements of the D4 dihedral group."""
        return [
            ('identity', lambda x: x),
            ('rot90', lambda x: torch.rot90(x, k=1)),
            ('rot180', lambda x: torch.rot90(x, k=2)),
            ('rot270', lambda x: torch.rot90(x, k=3)),
            ('flip_h', lambda x: torch.flip(x, dims=[1])),
            ('flip_v', lambda x: torch.flip(x, dims=[0])),
            ('flip_d1', lambda x: x.T),  # Transpose (diagonal flip)
            ('flip_d2', lambda x: torch.flip(x.T, dims=[0, 1])),  # Anti-diagonal
        ]
    
    @staticmethod
    def test_equivariance(
        program: Callable[[torch.Tensor], torch.Tensor],
        input_grid: torch.Tensor,
        output_grid: torch.Tensor
    ) -> Dict[str, Any]:
        """
        Test if a program is equivariant under D4 transformations.
        
        Returns the equivariance score (0 = breaks all symmetries, 1 = fully equivariant)
        and the set of preserved symmetries.
        """
        transforms = SymmetryOracle.get_d4_transforms()
        preserved = []
        broken = []
        
        for name, T in transforms:
            try:
                # Transform input, apply program
                T_input = T(input_grid)
                P_of_T_input = program(T_input)
                
                # Apply program, transform output
                P_of_input = program(input_grid)
                T_of_P_input = T(P_of_input)
                
                # Check if they match
                if P_of_T_input.shape == T_of_P_input.shape:
                    if torch.equal(P_of_T_input, T_of_P_input):
                        preserved.append(name)
                    else:
                        broken.append(name)
                else:
                    broken.append(name)
            except:
                broken.append(name)
        
        return {
            'equivariance_score': len(preserved) / 8.0,
            'preserved_symmetries': preserved,
            'broken_symmetries': broken
        }
    
    @staticmethod
    def discover_task_symmetries(task: ARCTask) -> Dict[str, Any]:
        """
        Discover which symmetries are preserved in the training examples.
        
        This tells us the "Conservation Laws" of the puzzle:
        - If all examples preserve rotation: rotation symmetry is a law
        - If color histogram is preserved: mass conservation
        - If chirality flips: the puzzle involves reflection
        """
        if not task.train_examples:
            return {'symmetries': [], 'conservation_laws': []}
        
        transforms = SymmetryOracle.get_d4_transforms()
        symmetry_votes = {name: 0 for name, _ in transforms}
        
        for ex in task.train_examples:
            inp, out = ex.input_grid.data, ex.output_grid.data
            
            for name, T in transforms:
                try:
                    T_inp = T(inp)
                    T_out = T(out)
                    
                    # Check if T(input)->T(output) has the same "structure"
                    # as input->output (not exact equality, but same transformation type)
                    
                    # Simple check: shape preservation
                    if T_inp.shape == T_out.shape and inp.shape == out.shape:
                        # Check histogram preservation
                        h_inp = torch.bincount(inp.flatten().long(), minlength=10)
                        h_out = torch.bincount(out.flatten().long(), minlength=10)
                        h_T_inp = torch.bincount(T_inp.flatten().long(), minlength=10)
                        h_T_out = torch.bincount(T_out.flatten().long(), minlength=10)
                        
                        if torch.equal(h_inp, h_T_inp) and torch.equal(h_out, h_T_out):
                            symmetry_votes[name] += 1
                except:
                    pass
        
        n = len(task.train_examples)
        preserved = [name for name, votes in symmetry_votes.items() if votes == n]
        
        # Infer conservation laws
        conservation_laws = []
        
        # Check mass conservation (total non-background pixels)
        mass_conserved = True
        for ex in task.train_examples:
            inp_mass = (ex.input_grid.data != 0).sum().item()
            out_mass = (ex.output_grid.data != 0).sum().item()
            if inp_mass != out_mass:
                mass_conserved = False
                break
        if mass_conserved:
            conservation_laws.append('mass')
        
        # Check color conservation (same colors in/out)
        color_conserved = True
        for ex in task.train_examples:
            inp_colors = set(ex.input_grid.data.unique().tolist())
            out_colors = set(ex.output_grid.data.unique().tolist())
            if inp_colors != out_colors:
                color_conserved = False
                break
        if color_conserved:
            conservation_laws.append('color_palette')
        
        # Check shape conservation
        shape_conserved = all(
            ex.input_grid.shape == ex.output_grid.shape 
            for ex in task.train_examples
        )
        if shape_conserved:
            conservation_laws.append('shape')
        
        return {
            'preserved_symmetries': preserved,
            'conservation_laws': conservation_laws,
            'symmetry_votes': symmetry_votes
        }


class OperatorGenePool:
    """
    Phase 23: Evolutionary pool of operators (genes).
    
    Operators that solve tasks gain "energy" and persist.
    Operators that don't pay their rent are garbage-collected.
    
    This is Natural Selection for Code - Autopoietic Machinery.
    """
    
    def __init__(self):
        # Gene pool: operator_name -> {function, energy, usage_count, success_count}
        self.genes: Dict[str, Dict] = {}
        self.energy_threshold = 0.1  # Minimum energy to survive
        self.cooling_rate = 0.95  # Energy decay per generation
    
    def register_gene(self, name: str, func: Callable, complexity: float = 1.0):
        """Register a new operator gene."""
        self.genes[name] = {
            'function': func,
            'energy': 0.5,  # Start neutral
            'complexity': complexity,
            'usage_count': 0,
            'success_count': 0
        }
    
    def use_gene(self, name: str, success: bool):
        """Record usage of a gene and update its energy."""
        if name not in self.genes:
            return
        
        gene = self.genes[name]
        gene['usage_count'] += 1
        
        if success:
            gene['success_count'] += 1
            # Energy gain inversely proportional to complexity
            gene['energy'] += 0.2 / gene['complexity']
        else:
            # Small energy loss
            gene['energy'] -= 0.05
        
        # Clamp energy
        gene['energy'] = max(0, min(2.0, gene['energy']))
    
    def evolve(self):
        """Run one generation of evolution (cooling + selection)."""
        to_remove = []
        
        for name, gene in self.genes.items():
            # Cooling: all genes lose energy over time
            gene['energy'] *= self.cooling_rate
            
            # Selection: remove genes below threshold
            if gene['energy'] < self.energy_threshold and gene['usage_count'] > 5:
                to_remove.append(name)
        
        for name in to_remove:
            del self.genes[name]
    
    def get_hot_genes(self, top_k: int = 10) -> List[str]:
        """Return the highest-energy genes."""
        sorted_genes = sorted(
            self.genes.items(), 
            key=lambda x: x[1]['energy'], 
            reverse=True
        )
        return [name for name, _ in sorted_genes[:top_k]]
    
    def get_stats(self) -> Dict:
        """Return pool statistics."""
        if not self.genes:
            return {'total': 0, 'avg_energy': 0, 'hot_genes': []}
        
        energies = [g['energy'] for g in self.genes.values()]
        return {
            'total': len(self.genes),
            'avg_energy': sum(energies) / len(energies),
            'hot_genes': self.get_hot_genes(5),
            'success_rates': {
                name: g['success_count'] / max(1, g['usage_count'])
                for name, g in self.genes.items()
            }
        }


class ActiveScientist:
    """
    Phase 23: The agentic core that experiments before solving.
    
    Workflow:
    1. Analyze training data to discover conservation laws
    2. Generate hypotheses (candidate programs)
    3. Test hypotheses for equivariance
    4. Use conservation laws to prune invalid candidates
    5. Induce new operators from successful patterns
    """
    
    def __init__(self, metric: AdaptiveFisherRaoMetric):
        self.metric = metric
        self.oracle = SymmetryOracle()
        self.gene_pool = OperatorGenePool()
        self.discovered_laws: Dict[str, List[str]] = {}
        
        # Initialize gene pool with fundamental operators
        self._initialize_genes()
    
    def _initialize_genes(self):
        """Initialize the gene pool with fundamental operators."""
        # Rotations
        for k in [1, 2, 3]:
            self.gene_pool.register_gene(
                f'rot{k*90}',
                lambda x, k=k: torch.rot90(x, k=k),
                complexity=0.5
            )
        
        # Flips
        self.gene_pool.register_gene('flip_h', lambda x: torch.flip(x, dims=[1]), 0.5)
        self.gene_pool.register_gene('flip_v', lambda x: torch.flip(x, dims=[0]), 0.5)
        
        # Identity
        self.gene_pool.register_gene('identity', lambda x: x, 0.1)
    
    def analyze_task(self, task: ARCTask) -> Dict:
        """
        Analyze a task to discover its physics (conservation laws + symmetries).
        """
        symmetry_info = self.oracle.discover_task_symmetries(task)
        self.discovered_laws[task.task_id] = symmetry_info['conservation_laws']
        
        return {
            'task_id': task.task_id,
            'symmetries': symmetry_info['preserved_symmetries'],
            'conservation_laws': symmetry_info['conservation_laws'],
            'n_training': len(task.train_examples)
        }
    
    def filter_by_conservation(
        self, 
        candidates: List[Tuple[str, ARCGrid]], 
        task: ARCTask
    ) -> List[Tuple[str, ARCGrid]]:
        """
        Filter candidates that violate discovered conservation laws.
        """
        laws = self.discovered_laws.get(task.task_id, [])
        if not laws or not task.train_examples:
            return candidates
        
        target = task.train_examples[0].output_grid
        filtered = []
        
        for method, pred in candidates:
            valid = True
            
            if 'mass' in laws:
                target_mass = (target.data != 0).sum().item()
                pred_mass = (pred.data != 0).sum().item()
                if abs(target_mass - pred_mass) > target_mass * 0.1:
                    valid = False
            
            if 'color_palette' in laws and valid:
                target_colors = set(target.data.unique().tolist())
                pred_colors = set(pred.data.unique().tolist())
                if pred_colors - target_colors:  # New colors introduced
                    valid = False
            
            if 'shape' in laws and valid:
                if pred.shape != target.shape:
                    valid = False
            
            if valid:
                filtered.append((method, pred))
        
        return filtered if filtered else candidates  # Don't return empty
    
    def induce_operator(
        self, 
        input_grid: torch.Tensor, 
        output_grid: torch.Tensor,
        name_hint: str = "induced"
    ) -> Optional[str]:
        """
        Induce a new operator from an input->output transformation.
        
        If successful, adds it to the gene pool.
        """
        if input_grid.shape != output_grid.shape:
            return None
        
        diff = (input_grid != output_grid)
        if not diff.any():
            return None
        
        # Try to characterize the transformation
        input_vals = input_grid[diff].tolist()
        output_vals = output_grid[diff].tolist()
        
        # Simple color mapping?
        color_map = {}
        for i, o in zip(input_vals, output_vals):
            if i in color_map and color_map[i] != o:
                color_map = None
                break
            color_map[i] = o
        
        if color_map and len(color_map) <= 3:
            def make_map(cmap):
                def apply_map(grid: torch.Tensor) -> torch.Tensor:
                    result = grid.clone()
                    for src, dst in cmap.items():
                        result[grid == src] = dst
                    return result
                return apply_map
            
            name = f"{name_hint}_color_{'_'.join(f'{k}to{v}' for k,v in color_map.items())}"
            self.gene_pool.register_gene(name, make_map(color_map), complexity=len(color_map))
            return name
        
        return None


class Phase23Solver:
    """
    Phase 23: The Active Scientist Solver.
    
    Combines:
    - Phase 22's thermodynamic policy (adaptive metric, MGD)
    - Phase 23's symmetry oracle and conservation law discovery
    - Operator gene pool with thermodynamic selection
    """
    
    def __init__(self):
        self.metric = AdaptiveFisherRaoMetric()
        self.scientist = ActiveScientist(self.metric)
        self.decomposer = LieAlgebraDecomposer()
        self.mgd = ManifoldGradientDescent(self.metric, self.decomposer)
        self.results: List[Dict] = []
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve a task using the Active Scientist approach."""
        
        # Step 1: Analyze task physics
        analysis = self.scientist.analyze_task(task)
        if verbose and analysis['conservation_laws']:
            print(f"  [LAWS] {analysis['conservation_laws']}", flush=True)
        
        # Step 2: Adapt metric
        self.metric.adapt_to_task(task)
        
        # Step 3: Generate candidates
        candidates = self._generate_candidates(task)
        
        # Step 4: Filter by conservation laws
        candidates = self.scientist.filter_by_conservation(candidates, task)
        
        if not candidates:
            return self._make_result(task, None, 'no_candidates')
        
        # Step 5: Evaluate and rank
        evaluated = []
        for method, pred in candidates:
            if task.train_examples:
                target = task.train_examples[0].output_grid
                if pred.shape == target.shape:
                    dist = self.metric.compute(pred, target)
                    evaluated.append((method, pred, dist))
        
        if not evaluated:
            return self._make_result(task, None, 'no_valid_candidates')
        
        evaluated.sort(key=lambda x: x[2]['total'])
        best_method, best_pred, best_dist = evaluated[0]
        
        # Step 6: Attempt MGD refinement
        if 0 < best_dist['total'] < 0.15 and task.train_examples:
            inp = task.train_examples[0].input_grid.data
            target = task.train_examples[0].output_grid
            refined = self.mgd.refine(best_pred.data, target, inp)
            if refined is not None:
                refined_dist = self.metric.compute(ARCGrid(refined), target)
                if refined_dist['total'] < best_dist['total']:
                    best_pred = ARCGrid(refined)
                    best_dist = refined_dist
                    best_method = f"{best_method}+mgd"
        
        # Step 7: Check perfection and update gene pool
        is_perfect = False
        if task.train_examples:
            target = task.train_examples[0].output_grid
            if best_pred.shape == target.shape:
                is_perfect = torch.equal(best_pred.data, target.data)
        
        # Update gene pool
        base_method = best_method.split('+')[0]
        self.scientist.gene_pool.use_gene(base_method, is_perfect)
        
        # Step 8: Induce new operator if successful
        if is_perfect and task.train_examples:
            inp = task.train_examples[0].input_grid.data
            out = task.train_examples[0].output_grid.data
            induced = self.scientist.induce_operator(inp, out, task.task_id[:8])
            if induced and verbose:
                print(f"  [INDUCED] {induced}", flush=True)
        
        # Step 9: Anneal metric
        self.metric.anneal_from_result(is_perfect, best_dist)
        
        # Evolve gene pool periodically
        if len(self.results) % 20 == 0:
            self.scientist.gene_pool.evolve()
        
        result = self._make_result(task, best_pred, best_method, best_dist, is_perfect)
        self.results.append(result)
        return result
    
    def _generate_candidates(self, task: ARCTask) -> List[Tuple[str, ARCGrid]]:
        """Generate candidates using gene pool + comprehensive transforms."""
        candidates = []
        if not task.train_examples:
            return candidates
        
        inp = task.train_examples[0].input_grid
        out = task.train_examples[0].output_grid
        data = inp.data
        
        # Use hot genes first
        for gene_name in self.scientist.gene_pool.get_hot_genes(10):
            gene = self.scientist.gene_pool.genes.get(gene_name)
            if gene:
                try:
                    result = gene['function'](data)
                    candidates.append((gene_name, ARCGrid(result)))
                except:
                    pass
        
        # Standard transforms
        candidates.append(('identity', inp))
        for k in [1, 2, 3]:
            candidates.append((f'rot{k*90}', ARCGrid(torch.rot90(data, k=k))))
        candidates.append(('flip_h', ARCGrid(torch.flip(data, dims=[1]))))
        candidates.append(('flip_v', ARCGrid(torch.flip(data, dims=[0]))))
        candidates.append(('transpose', ARCGrid(data.T)))
        
        # Crop to content (non-background bounding box)
        for bg in [0]:
            mask = (data != bg)
            if mask.any():
                rows = mask.any(dim=1)
                cols = mask.any(dim=0)
                r_idx = torch.where(rows)[0]
                c_idx = torch.where(cols)[0]
                if len(r_idx) > 0 and len(c_idx) > 0:
                    r1, r2 = r_idx[0].item(), r_idx[-1].item() + 1
                    c1, c2 = c_idx[0].item(), c_idx[-1].item() + 1
                    cropped = data[r1:r2, c1:c2]
                    candidates.append((f'crop_content', ARCGrid(cropped)))
        
        # Crop to output size (if different)
        if out.shape != inp.shape:
            oh, ow = out.shape
            ih, iw = inp.shape
            # Try cropping from corners and center
            if oh <= ih and ow <= iw:
                candidates.append(('crop_tl', ARCGrid(data[:oh, :ow])))
                candidates.append(('crop_tr', ARCGrid(data[:oh, iw-ow:])))
                candidates.append(('crop_bl', ARCGrid(data[ih-oh:, :ow])))
                candidates.append(('crop_br', ARCGrid(data[ih-oh:, iw-ow:])))
                # Center crop
                r_start = (ih - oh) // 2
                c_start = (iw - ow) // 2
                candidates.append(('crop_center', ARCGrid(data[r_start:r_start+oh, c_start:c_start+ow])))
        
        # Extract connected components
        for color in data.unique().tolist():
            if color == 0:
                continue
            mask = (data == color).numpy().astype(np.int32)
            labeled, n_objs = ndimage.label(mask)
            if n_objs > 0:
                # Extract largest object
                sizes = [(labeled == i).sum() for i in range(1, n_objs + 1)]
                if sizes:
                    largest_id = np.argmax(sizes) + 1
                    obj_mask = (labeled == largest_id)
                    rows = np.any(obj_mask, axis=1)
                    cols = np.any(obj_mask, axis=0)
                    r_idx = np.where(rows)[0]
                    c_idx = np.where(cols)[0]
                    if len(r_idx) > 0 and len(c_idx) > 0:
                        r1, r2 = r_idx[0], r_idx[-1] + 1
                        c1, c2 = c_idx[0], c_idx[-1] + 1
                        obj_data = data[r1:r2, c1:c2].clone()
                        candidates.append((f'extract_obj_{color}', ARCGrid(obj_data)))
        
        # Color swaps and mappings
        colors = [c for c in data.unique().tolist() if c != 0]
        for src in colors[:5]:
            for dst in range(10):
                if src != dst:
                    mapped = data.clone()
                    mapped[data == src] = dst
                    candidates.append((f'color({src}->{dst})', ARCGrid(mapped)))
        
        # Two-color swap
        if len(colors) >= 2:
            c1, c2 = colors[0], colors[1]
            swapped = data.clone()
            mask1 = (data == c1)
            mask2 = (data == c2)
            swapped[mask1] = c2
            swapped[mask2] = c1
            candidates.append((f'swap({c1},{c2})', ARCGrid(swapped)))
        
        # Fill background with dominant color
        if len(colors) > 0:
            dom_color = colors[0]
            filled = data.clone()
            filled[data == 0] = dom_color
            candidates.append((f'fill_bg({dom_color})', ARCGrid(filled)))
        
        # Tile/repeat patterns
        h, w = data.shape
        if h > 1 and w > 1:
            # Take top-left quadrant and tile
            qh, qw = h // 2, w // 2
            if qh > 0 and qw > 0:
                quad = data[:qh, :qw]
                tiled = quad.repeat(2, 2)[:h, :w]
                candidates.append(('tile_quad', ARCGrid(tiled)))
        
        return candidates
    
    def _make_result(self, task, pred, method, dist=None, is_perfect=False):
        return {
            'task_id': task.task_id,
            'method': method,
            'prediction': pred,
            'fisher_distance': dist['total'] if dist else 1.0,
            'is_perfect': is_perfect,
            'conservation_laws': self.scientist.discovered_laws.get(task.task_id, [])
        }
    
    def get_summary(self) -> Dict:
        perfect = sum(1 for r in self.results if r['is_perfect'])
        near_miss = sum(1 for r in self.results 
                        if 0 < r['fisher_distance'] < 0.1 and not r['is_perfect'])
        return {
            'total_tasks': len(self.results),
            'perfect_solves': perfect,
            'near_misses': near_miss,
            'gene_pool': self.scientist.gene_pool.get_stats(),
            'mgd_stats': self.mgd.get_stats(),
            'final_weights': self.metric.weights
        }


# =============================================================================
# HYBRID AGENTIC SOLVER (Phase 20 + Phase 23)
# =============================================================================

class HybridAgenticSolver:
    """
    Combines Phase 20's powerful candidate generation (CEGAR rules, decomposition)
    with Phase 23's agentic infrastructure (conservation laws, gene pool, MGD).
    
    This is the "Full Stack Agent":
    1. Discover physics (conservation laws, symmetries)
    2. Generate candidates via Phase20Solver
    3. Filter by conservation laws
    4. Rank by adaptive Fisher-Rao metric
    5. Refine near-misses via MGD
    6. Induce successful operators into gene pool
    7. Anneal metric based on outcomes
    """
    
    def __init__(self):
        self.metric = AdaptiveFisherRaoMetric()
        self.scientist = ActiveScientist(self.metric)
        self.decomposer = LieAlgebraDecomposer()
        self.mgd = ManifoldGradientDescent(self.metric, self.decomposer)
        self.phase20 = Phase20Solver(ARCPhase83Config())
        self.results: List[Dict] = []
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve using hybrid approach."""
        
        # Step 1: Discover task physics
        analysis = self.scientist.analyze_task(task)
        if verbose and analysis['conservation_laws']:
            print(f"  [LAWS] {analysis['conservation_laws']}", flush=True)
        
        # Step 2: Adapt metric
        self.metric.adapt_to_task(task)
        
        # Step 3: Use Phase20Solver to generate candidates
        phase20_result = self.phase20.solve_task(task)
        
        # Collect all candidates from Phase 20's exploration
        candidates = []
        if phase20_result.get('prediction') is not None:
            pred = phase20_result['prediction']
            if isinstance(pred, list):
                pred_tensor = torch.tensor(pred, dtype=torch.int32)
            elif isinstance(pred, np.ndarray):
                pred_tensor = torch.from_numpy(pred).int()
            elif isinstance(pred, torch.Tensor):
                pred_tensor = pred
            else:
                pred_tensor = None
            
            if pred_tensor is not None:
                candidates.append((phase20_result.get('method', 'phase20'), ARCGrid(pred_tensor)))
        
        # Also add Phase 23's basic candidates
        candidates.extend(self._generate_basic_candidates(task))
        
        if not candidates:
            return self._make_result(task, None, 'no_candidates')
        
        # Step 4: Filter by conservation laws
        candidates = self.scientist.filter_by_conservation(candidates, task)
        
        # Step 5: Evaluate and rank by Fisher-Rao
        evaluated = []
        for method, pred in candidates:
            if task.train_examples:
                target = task.train_examples[0].output_grid
                if pred.shape == target.shape:
                    dist = self.metric.compute(pred, target)
                    evaluated.append((method, pred, dist))
        
        if not evaluated:
            return self._make_result(task, None, 'no_valid_candidates')
        
        evaluated.sort(key=lambda x: x[2]['total'])
        best_method, best_pred, best_dist = evaluated[0]
        
        # Step 6: Attempt MGD refinement for near-misses
        if 0 < best_dist['total'] < 0.15 and task.train_examples:
            inp = task.train_examples[0].input_grid.data
            target = task.train_examples[0].output_grid
            refined = self.mgd.refine(best_pred.data, target, inp)
            if refined is not None:
                refined_dist = self.metric.compute(ARCGrid(refined), target)
                if refined_dist['total'] < best_dist['total']:
                    best_pred = ARCGrid(refined)
                    best_dist = refined_dist
                    best_method = f"{best_method}+mgd"
                    if verbose:
                        print(f"  [MGD] Refined: {best_dist['total']:.4f}", flush=True)
        
        # Step 7: Check perfection
        is_perfect = False
        if task.train_examples:
            target = task.train_examples[0].output_grid
            if best_pred.shape == target.shape:
                is_perfect = torch.equal(best_pred.data, target.data)
        
        # Step 8: Update gene pool and induce operators
        base_method = best_method.split('+')[0]
        self.scientist.gene_pool.use_gene(base_method, is_perfect)
        
        if is_perfect and task.train_examples:
            inp = task.train_examples[0].input_grid.data
            out = task.train_examples[0].output_grid.data
            induced = self.scientist.induce_operator(inp, out, task.task_id[:8])
            if induced and verbose:
                print(f"  [INDUCED] {induced}", flush=True)
        
        # Step 9: Anneal metric
        self.metric.anneal_from_result(is_perfect, best_dist)
        
        # Evolve gene pool periodically
        if len(self.results) % 20 == 0:
            self.scientist.gene_pool.evolve()
        
        result = self._make_result(task, best_pred, best_method, best_dist, is_perfect)
        self.results.append(result)
        return result
    
    def _generate_basic_candidates(self, task: ARCTask) -> List[Tuple[str, ARCGrid]]:
        """Generate basic candidates as fallback."""
        candidates = []
        if not task.train_examples:
            return candidates
        
        inp = task.train_examples[0].input_grid
        
        # Use hot genes
        for gene_name in self.scientist.gene_pool.get_hot_genes(5):
            gene = self.scientist.gene_pool.genes.get(gene_name)
            if gene:
                try:
                    result = gene['function'](inp.data)
                    candidates.append((gene_name, ARCGrid(result)))
                except:
                    pass
        
        # Identity and rotations
        candidates.append(('identity', inp))
        for k in [1, 2, 3]:
            candidates.append((f'rot{k*90}', ARCGrid(torch.rot90(inp.data, k=k))))
        candidates.append(('flip_h', ARCGrid(torch.flip(inp.data, dims=[1]))))
        candidates.append(('flip_v', ARCGrid(torch.flip(inp.data, dims=[0]))))
        
        return candidates
    
    def _make_result(self, task, pred, method, dist=None, is_perfect=False):
        return {
            'task_id': task.task_id,
            'method': method,
            'prediction': pred,
            'fisher_distance': dist['total'] if dist else 1.0,
            'is_perfect': is_perfect,
            'conservation_laws': self.scientist.discovered_laws.get(task.task_id, [])
        }
    
    def get_summary(self) -> Dict:
        perfect = sum(1 for r in self.results if r['is_perfect'])
        near_miss = sum(1 for r in self.results 
                        if 0 < r['fisher_distance'] < 0.1 and not r['is_perfect'])
        return {
            'total_tasks': len(self.results),
            'perfect_solves': perfect,
            'near_misses': near_miss,
            'gene_pool': self.scientist.gene_pool.get_stats(),
            'mgd_stats': self.mgd.get_stats(),
            'final_weights': self.metric.weights
        }


# =============================================================================
# PHASE 29: GRAPH GRAMMAR ENGINE (System 2 - Slow Reasoning)
# =============================================================================

@dataclass
class SceneObject:
    """A node in the scene graph - represents a connected component."""
    obj_id: int
    color: int
    bbox: Tuple[int, int, int, int]  # (r1, c1, r2, c2)
    mask: np.ndarray
    centroid: Tuple[float, float]
    area: int
    
    @property
    def width(self) -> int:
        return self.bbox[3] - self.bbox[1]
    
    @property
    def height(self) -> int:
        return self.bbox[2] - self.bbox[0]


@dataclass 
class SceneEdge:
    """An edge in the scene graph - represents a relation between objects."""
    src_id: int
    dst_id: int
    relation: str  # 'aligned_x', 'aligned_y', 'adjacent', 'contains', 'same_color', etc.
    distance: float = 0.0


class SceneGraph:
    """
    Graph representation of an ARC grid.
    
    Nodes = Objects (connected components)
    Edges = Spatial/Color relations between objects
    
    This is the "Abstract Syntax Tree" for visual reasoning.
    """
    
    def __init__(self):
        self.objects: Dict[int, SceneObject] = {}
        self.edges: List[SceneEdge] = []
        self.background_color: int = 0
    
    def add_object(self, obj: SceneObject):
        self.objects[obj.obj_id] = obj
    
    def add_edge(self, edge: SceneEdge):
        self.edges.append(edge)
    
    def get_objects_by_color(self, color: int) -> List[SceneObject]:
        return [o for o in self.objects.values() if o.color == color]
    
    def get_edges_by_relation(self, relation: str) -> List[SceneEdge]:
        return [e for e in self.edges if e.relation == relation]
    
    def get_neighbors(self, obj_id: int) -> List[Tuple[int, str]]:
        """Get all neighbors of an object with their relation types."""
        neighbors = []
        for e in self.edges:
            if e.src_id == obj_id:
                neighbors.append((e.dst_id, e.relation))
            elif e.dst_id == obj_id:
                neighbors.append((e.src_id, e.relation))
        return neighbors
    
    def to_signature(self) -> str:
        """Create a hashable signature for graph matching."""
        obj_sig = sorted([(o.color, o.area) for o in self.objects.values()])
        edge_sig = sorted([(e.relation, e.src_id < e.dst_id) for e in self.edges])
        return f"O{obj_sig}E{edge_sig}"


class SceneGraphBuilder:
    """
    Converts an ARC grid into a Scene Graph.
    
    Step 1: Extract connected components (Objects)
    Step 2: Compute spatial relations (Edges)
    Step 3: Build the graph structure
    """
    
    def __init__(self, alignment_threshold: float = 2.0, adjacency_threshold: float = 3.0):
        self.alignment_threshold = alignment_threshold
        self.adjacency_threshold = adjacency_threshold
    
    def build(self, grid: ARCGrid) -> SceneGraph:
        """Build a scene graph from an ARC grid."""
        graph = SceneGraph()
        data = grid.data.numpy() if isinstance(grid.data, torch.Tensor) else grid.data
        
        # Find background (most common color, usually 0)
        colors, counts = np.unique(data, return_counts=True)
        graph.background_color = colors[np.argmax(counts)]
        
        # Extract objects (connected components for each non-background color)
        obj_id = 0
        for color in colors:
            if color == graph.background_color:
                continue
            
            mask = (data == color).astype(np.int32)
            labeled, n_components = ndimage.label(mask)
            
            for comp_id in range(1, n_components + 1):
                comp_mask = (labeled == comp_id)
                if comp_mask.sum() == 0:
                    continue
                
                # Compute bounding box
                rows = np.any(comp_mask, axis=1)
                cols = np.any(comp_mask, axis=0)
                r_idx = np.where(rows)[0]
                c_idx = np.where(cols)[0]
                
                if len(r_idx) == 0 or len(c_idx) == 0:
                    continue
                
                r1, r2 = r_idx[0], r_idx[-1] + 1
                c1, c2 = c_idx[0], c_idx[-1] + 1
                
                # Compute centroid
                ys, xs = np.where(comp_mask)
                centroid = (ys.mean(), xs.mean())
                
                obj = SceneObject(
                    obj_id=obj_id,
                    color=int(color),
                    bbox=(r1, c1, r2, c2),
                    mask=comp_mask,
                    centroid=centroid,
                    area=int(comp_mask.sum())
                )
                graph.add_object(obj)
                obj_id += 1
        
        # Compute edges (relations between objects)
        obj_list = list(graph.objects.values())
        for i, obj_a in enumerate(obj_list):
            for obj_b in obj_list[i+1:]:
                edges = self._compute_relations(obj_a, obj_b)
                for edge in edges:
                    graph.add_edge(edge)
        
        return graph
    
    def _compute_relations(self, a: SceneObject, b: SceneObject) -> List[SceneEdge]:
        """Compute all relations between two objects."""
        edges = []
        
        cy_a, cx_a = a.centroid
        cy_b, cx_b = b.centroid
        
        # Aligned X (same column, vertically aligned)
        if abs(cx_a - cx_b) < self.alignment_threshold:
            edges.append(SceneEdge(a.obj_id, b.obj_id, 'aligned_x', abs(cx_a - cx_b)))
        
        # Aligned Y (same row, horizontally aligned)
        if abs(cy_a - cy_b) < self.alignment_threshold:
            edges.append(SceneEdge(a.obj_id, b.obj_id, 'aligned_y', abs(cy_a - cy_b)))
        
        # Adjacent (close proximity)
        dist = np.sqrt((cx_a - cx_b)**2 + (cy_a - cy_b)**2)
        if dist < self.adjacency_threshold:
            edges.append(SceneEdge(a.obj_id, b.obj_id, 'adjacent', dist))
        
        # Same color
        if a.color == b.color:
            edges.append(SceneEdge(a.obj_id, b.obj_id, 'same_color', 0.0))
        
        # Same size (area within 20%)
        if min(a.area, b.area) / max(a.area, b.area) > 0.8:
            edges.append(SceneEdge(a.obj_id, b.obj_id, 'same_size', 0.0))
        
        # Contains (one bbox inside another)
        if (a.bbox[0] <= b.bbox[0] and a.bbox[1] <= b.bbox[1] and
            a.bbox[2] >= b.bbox[2] and a.bbox[3] >= b.bbox[3]):
            edges.append(SceneEdge(a.obj_id, b.obj_id, 'contains', 0.0))
        elif (b.bbox[0] <= a.bbox[0] and b.bbox[1] <= a.bbox[1] and
              b.bbox[2] >= a.bbox[2] and b.bbox[3] >= a.bbox[3]):
            edges.append(SceneEdge(b.obj_id, a.obj_id, 'contains', 0.0))
        
        return edges


@dataclass
class GraphGrammarRule:
    """
    A graph rewriting rule learned from training examples.
    
    Pattern: Condition on the input graph (e.g., "two objects aligned_x")
    Action: Transformation to apply (e.g., "draw line between them")
    """
    name: str
    pattern_relations: List[str]  # Required relations in input
    action_type: str  # 'connect', 'fill', 'copy', 'delete', 'recolor'
    action_params: Dict[str, Any]  # Parameters for the action
    confidence: float = 0.0
    usage_count: int = 0
    success_count: int = 0


class GraphGrammarEngine:
    """
    System 2 (Slow) Reasoning via Graph Grammar.
    
    When System 1 fails or produces a near-miss:
    1. Build Scene Graphs for input/output pairs
    2. Induce rules by comparing graph differences
    3. Apply rules to test input
    4. Render the transformed graph back to a grid
    
    This handles STRUCTURAL transformations that operators can't:
    - "Connect aligned objects with a line"
    - "Fill the region between two shapes"
    - "Copy pattern from one object to another"
    """
    
    def __init__(self):
        self.graph_builder = SceneGraphBuilder()
        self.rules: List[GraphGrammarRule] = []
        self.induced_rules: Dict[str, GraphGrammarRule] = {}
    
    def induce_rules(self, task: ARCTask) -> List[GraphGrammarRule]:
        """
        Learn graph rewriting rules from training examples.
        
        For each train pair:
        1. Build input graph and output graph
        2. Find structural differences
        3. Hypothesize rules that explain the transformation
        """
        rules = []
        
        for ex in task.train_examples:
            input_graph = self.graph_builder.build(ex.input_grid)
            output_graph = self.graph_builder.build(ex.output_grid)
            
            # Analyze differences
            new_rules = self._induce_from_pair(input_graph, output_graph, ex)
            rules.extend(new_rules)
        
        # Consolidate rules (keep those that appear in multiple examples)
        rule_counts = Counter([r.name for r in rules])
        consolidated = []
        for rule in rules:
            if rule_counts[rule.name] >= 1:  # Appears at least once
                rule.confidence = rule_counts[rule.name] / len(task.train_examples)
                consolidated.append(rule)
        
        self.rules = consolidated
        return consolidated
    
    def _induce_from_pair(self, inp_graph: SceneGraph, out_graph: SceneGraph, 
                          ex: ARCExample) -> List[GraphGrammarRule]:
        """Induce rules from a single input/output pair."""
        rules = []
        
        inp_data = ex.input_grid.data.numpy() if isinstance(ex.input_grid.data, torch.Tensor) else ex.input_grid.data
        out_data = ex.output_grid.data.numpy() if isinstance(ex.output_grid.data, torch.Tensor) else ex.output_grid.data
        
        # Check for new objects in output (something was added)
        inp_colors = set(o.color for o in inp_graph.objects.values())
        out_colors = set(o.color for o in out_graph.objects.values())
        new_colors = out_colors - inp_colors
        
        # Rule Type 1: CONNECTION (line drawn between aligned objects)
        aligned_pairs = inp_graph.get_edges_by_relation('aligned_x') + \
                       inp_graph.get_edges_by_relation('aligned_y')
        
        for edge in aligned_pairs:
            obj_a = inp_graph.objects.get(edge.src_id)
            obj_b = inp_graph.objects.get(edge.dst_id)
            if obj_a and obj_b:
                # Check if there's a new line/connection in output
                if self._has_connection(obj_a, obj_b, inp_data, out_data):
                    rules.append(GraphGrammarRule(
                        name=f"connect_{edge.relation}",
                        pattern_relations=[edge.relation],
                        action_type='connect',
                        action_params={'color': self._get_line_color(obj_a, obj_b, out_data)},
                        confidence=0.5
                    ))
        
        # Rule Type 2: FILL (region between objects filled)
        for edge in inp_graph.get_edges_by_relation('adjacent'):
            obj_a = inp_graph.objects.get(edge.src_id)
            obj_b = inp_graph.objects.get(edge.dst_id)
            if obj_a and obj_b:
                if self._has_fill_between(obj_a, obj_b, inp_data, out_data):
                    rules.append(GraphGrammarRule(
                        name=f"fill_between",
                        pattern_relations=['adjacent'],
                        action_type='fill',
                        action_params={'color': self._get_fill_color(obj_a, obj_b, out_data)},
                        confidence=0.5
                    ))
        
        # Rule Type 3: RECOLOR (object color changed)
        for obj_id, obj in inp_graph.objects.items():
            # Check if this object's region has different color in output
            mask = obj.mask
            if out_data.shape == inp_data.shape:
                out_colors_in_region = out_data[mask]
                if len(out_colors_in_region) > 0:
                    new_color = int(np.median(out_colors_in_region))
                    if new_color != obj.color:
                        # Find what predicts this recoloring
                        neighbors = inp_graph.get_neighbors(obj_id)
                        for neighbor_id, relation in neighbors:
                            rules.append(GraphGrammarRule(
                                name=f"recolor_by_{relation}",
                                pattern_relations=[relation],
                                action_type='recolor',
                                action_params={'from_color': obj.color, 'to_color': new_color},
                                confidence=0.5
                            ))
        
        return rules
    
    def _has_connection(self, a: SceneObject, b: SceneObject, 
                        inp: np.ndarray, out: np.ndarray) -> bool:
        """Check if there's a line connecting two objects in output but not input."""
        if inp.shape != out.shape:
            return False
        
        # Check pixels between the two objects
        cy_a, cx_a = int(a.centroid[0]), int(a.centroid[1])
        cy_b, cx_b = int(b.centroid[0]), int(b.centroid[1])
        
        # Sample points along the line between centroids
        n_points = max(abs(cy_b - cy_a), abs(cx_b - cx_a), 1)
        for i in range(1, n_points):
            t = i / n_points
            y = int(cy_a + t * (cy_b - cy_a))
            x = int(cx_a + t * (cx_b - cx_a))
            if 0 <= y < inp.shape[0] and 0 <= x < inp.shape[1]:
                # New non-background pixel in output
                if inp[y, x] == 0 and out[y, x] != 0:
                    return True
        return False
    
    def _get_line_color(self, a: SceneObject, b: SceneObject, out: np.ndarray) -> int:
        """Get the color of the line between two objects."""
        cy_a, cx_a = int(a.centroid[0]), int(a.centroid[1])
        cy_b, cx_b = int(b.centroid[0]), int(b.centroid[1])
        
        n_points = max(abs(cy_b - cy_a), abs(cx_b - cx_a), 1)
        for i in range(1, n_points):
            t = i / n_points
            y = int(cy_a + t * (cy_b - cy_a))
            x = int(cx_a + t * (cx_b - cx_a))
            if 0 <= y < out.shape[0] and 0 <= x < out.shape[1]:
                if out[y, x] != 0:
                    return int(out[y, x])
        return a.color  # Default to object color
    
    def _has_fill_between(self, a: SceneObject, b: SceneObject,
                          inp: np.ndarray, out: np.ndarray) -> bool:
        """Check if region between objects is filled in output."""
        if inp.shape != out.shape:
            return False
        
        # Check the bounding box between objects
        r1 = min(a.bbox[0], b.bbox[0])
        r2 = max(a.bbox[2], b.bbox[2])
        c1 = min(a.bbox[1], b.bbox[1])
        c2 = max(a.bbox[3], b.bbox[3])
        
        inp_region = inp[r1:r2, c1:c2]
        out_region = out[r1:r2, c1:c2]
        
        # More non-zero pixels in output
        return (out_region != 0).sum() > (inp_region != 0).sum() * 1.5
    
    def _get_fill_color(self, a: SceneObject, b: SceneObject, out: np.ndarray) -> int:
        """Get the fill color between objects."""
        r1 = min(a.bbox[0], b.bbox[0])
        r2 = max(a.bbox[2], b.bbox[2])
        c1 = min(a.bbox[1], b.bbox[1])
        c2 = max(a.bbox[3], b.bbox[3])
        
        region = out[r1:r2, c1:c2]
        colors, counts = np.unique(region[region != 0], return_counts=True)
        if len(colors) > 0:
            return int(colors[np.argmax(counts)])
        return a.color
    
    def apply_rules(self, task: ARCTask) -> Optional[ARCGrid]:
        """
        Apply induced rules to generate a prediction.
        
        1. Build scene graph for test input
        2. Apply matching rules
        3. Render result back to grid
        """
        if not self.rules or not task.train_examples:
            return None
        
        # Get test input (use first train input as proxy if no test)
        test_input = task.train_examples[0].input_grid
        test_graph = self.graph_builder.build(test_input)
        
        # Start with copy of input
        data = test_input.data.numpy().copy() if isinstance(test_input.data, torch.Tensor) else test_input.data.copy()
        
        applied_any = False
        
        for rule in sorted(self.rules, key=lambda r: -r.confidence):
            # Check if rule pattern matches
            if self._pattern_matches(test_graph, rule):
                # Apply the action
                data = self._apply_action(data, test_graph, rule)
                applied_any = True
        
        if applied_any:
            return ARCGrid(torch.tensor(data, dtype=torch.long))
        return None
    
    def _pattern_matches(self, graph: SceneGraph, rule: GraphGrammarRule) -> bool:
        """Check if rule pattern matches the graph."""
        for relation in rule.pattern_relations:
            if not graph.get_edges_by_relation(relation):
                return False
        return True
    
    def _apply_action(self, data: np.ndarray, graph: SceneGraph, 
                      rule: GraphGrammarRule) -> np.ndarray:
        """Apply a rule action to the grid."""
        result = data.copy()
        
        if rule.action_type == 'connect':
            # Draw lines between aligned objects
            for relation in rule.pattern_relations:
                for edge in graph.get_edges_by_relation(relation):
                    obj_a = graph.objects.get(edge.src_id)
                    obj_b = graph.objects.get(edge.dst_id)
                    if obj_a and obj_b:
                        result = self._draw_line(result, obj_a, obj_b, 
                                                 rule.action_params.get('color', obj_a.color))
        
        elif rule.action_type == 'fill':
            # Fill regions between adjacent objects
            for edge in graph.get_edges_by_relation('adjacent'):
                obj_a = graph.objects.get(edge.src_id)
                obj_b = graph.objects.get(edge.dst_id)
                if obj_a and obj_b:
                    result = self._fill_between(result, obj_a, obj_b,
                                                rule.action_params.get('color', obj_a.color))
        
        elif rule.action_type == 'recolor':
            # Change object colors
            from_c = rule.action_params.get('from_color', 0)
            to_c = rule.action_params.get('to_color', 0)
            result[result == from_c] = to_c
        
        return result
    
    def _draw_line(self, data: np.ndarray, a: SceneObject, b: SceneObject, 
                   color: int) -> np.ndarray:
        """Draw a line between two objects."""
        result = data.copy()
        cy_a, cx_a = int(a.centroid[0]), int(a.centroid[1])
        cy_b, cx_b = int(b.centroid[0]), int(b.centroid[1])
        
        n_points = max(abs(cy_b - cy_a), abs(cx_b - cx_a), 1)
        for i in range(n_points + 1):
            t = i / max(n_points, 1)
            y = int(cy_a + t * (cy_b - cy_a))
            x = int(cx_a + t * (cx_b - cx_a))
            if 0 <= y < result.shape[0] and 0 <= x < result.shape[1]:
                result[y, x] = color
        
        return result
    
    def _fill_between(self, data: np.ndarray, a: SceneObject, b: SceneObject,
                      color: int) -> np.ndarray:
        """Fill the region between two objects."""
        result = data.copy()
        
        r1 = min(a.bbox[0], b.bbox[0])
        r2 = max(a.bbox[2], b.bbox[2])
        c1 = min(a.bbox[1], b.bbox[1])
        c2 = max(a.bbox[3], b.bbox[3])
        
        # Fill background pixels in the region
        for r in range(r1, r2):
            for c in range(c1, c2):
                if result[r, c] == 0:
                    result[r, c] = color
        
        return result
    
    def refine_near_miss(self, task: ARCTask, candidate: ARCGrid, 
                         target: ARCGrid) -> Optional[ARCGrid]:
        """
        Use graph grammar to refine a near-miss candidate.
        
        This is the System 2 refinement when System 1 gets close but not perfect.
        """
        # Fast path: Skip if grids are too large (expensive)
        if candidate.shape[0] * candidate.shape[1] > 400:
            return None
        
        # Fast path: Skip if too many objects (expensive graph operations)
        try:
            test_graph = self.graph_builder.build(task.train_examples[0].input_grid)
            if len(test_graph.objects) > 20:
                return None
        except:
            return None
        
        # Induce rules from training
        rules = self.induce_rules(task)
        
        if not rules:
            return None
        
        # Apply rules to the candidate
        result = self.apply_rules(task)
        
        if result is not None:
            # Check if result is better than candidate
            if result.shape == target.shape:
                result_errors = (result.data != target.data).sum().item()
                cand_errors = (candidate.data != target.data).sum().item() if candidate.shape == target.shape else float('inf')
                if result_errors < cand_errors:
                    return result
        
        return None
    
    def compile_to_canonical_operators(self, task: ARCTask) -> List['CanonicalOperator']:
        """
        FIX 7: Compile GraphGrammar rules into CanonicalOperator IR.
        
        This bridges System 2 (scene-graph reasoning) with System 4 (composition).
        Each induced rule becomes a first-class operator with:
        - preconditions: required graph relations (aligned_x, adjacent, etc.)
        - apply: scene-graph-aware action (connect, fill, recolor)
        
        This allows A* to compose scene-graph-aware operators, not just pixel ops.
        """
        from dataclasses import dataclass
        
        rules = self.induce_rules(task)
        operators = []
        
        for rule in rules:
            # Convert pattern_relations to preconditions
            preconditions = {
                'requires_relations': rule.pattern_relations,
                'scene_graph': True,  # Marker: this op needs SceneGraph
            }
            
            # Convert action to postconditions
            postconditions = {
                'action_type': rule.action_type,
            }
            if rule.action_type == 'connect':
                postconditions['connectivity'] = 'increased'
            elif rule.action_type == 'fill':
                postconditions['mass'] = 'increased'
            elif rule.action_type == 'recolor':
                postconditions['color'] = 'changed'
            
            # Create canonical operator
            op = CanonicalOperator(
                op_type=f"graph_{rule.action_type}",
                params={
                    'rule_name': rule.name,
                    'pattern_relations': rule.pattern_relations,
                    **rule.action_params
                },
                preconditions=preconditions,
                postconditions=postconditions,
                cost=0.15,  # Slightly higher than primitives (0.1)
                source='graph_grammar',
                confidence=rule.confidence
            )
            operators.append(op)
        
        return operators


# =============================================================================
# PHASE 32: CANONICAL OPERATOR IR + RESIDUAL COMPILER
# =============================================================================
# Theory: Unify operator discovery, persistence, and composition under one IR.
# 
# The Residual Compiler turns Δ = y ⊖ ŷ into typed, hashable operators.
# This makes "discover new physics" concrete: the system graduates an operator
# only when it is a *global section candidate* consistent with the task's
# discovered restrictions (conservation/symmetry constraints).
#
# Canonical Operator IR: Op(type, params, preconditions, postconditions, cost)
# - All Systems (1-4) use the same representation
# - Content-addressed via hash for deduplication
# - Thermodynamic energy guides composition search
# =============================================================================

@dataclass
class CanonicalOperator:
    """
    The universal representation for all operators in the system.
    
    Theory (Category Theory):
    - Operators are Morphisms in the category of ARC grids
    - Preconditions define the source object
    - Postconditions define the target object
    - Cost is the complexity (Kolmogorov-like)
    
    PHASE 37 (Renormalization):
    - Operators have thermodynamic lifecycle: creation → reinforcement → decay → death
    - Energy increases with age if unused (entropy production)
    - Energy decreases with successful use (LTP)
    - High-energy operators are pruned (selectionism)
    
    This IR unifies:
    - System 1 primitives (rotate, flip, crop)
    - System 2 graph rules (connect, fill, recolor)
    - System 3 spectral discoveries (shift, expand)
    - System 4 compositions (chains of above)
    """
    op_type: str  # 'translate', 'color_map', 'crop', 'connect', 'fill', etc.
    params: Dict[str, Any]  # Type-specific parameters
    preconditions: Dict[str, Any]  # Required conservation laws, symmetries
    postconditions: Dict[str, Any]  # What the operator guarantees
    cost: float  # Complexity measure (lower = simpler)
    source: str  # Where this operator came from ('primitive', 'induced', 'compiled', 'adhoc', 'consolidated')
    confidence: float = 1.0  # How confident we are in this operator
    usage_count: int = 0
    success_count: int = 0
    # PHASE 37: Thermodynamic lifecycle fields
    creation_epoch: int = 0  # When this operator was created (task number)
    last_used_epoch: int = 0  # Last time this operator was used
    accumulated_decay: float = 0.0  # Entropy accumulated from disuse
    is_primitive: bool = False  # Primitives don't decay (they're axioms)
    generalized_from: List[str] = field(default_factory=list)  # Ad-hoc ops this was derived from
    
    def content_hash(self) -> str:
        """Content-addressed hash for deduplication."""
        content = f"{self.op_type}:{sorted(self.params.items())}"
        return f"{self.op_type}_{hash(content) % (10**10)}"
    
    def energy(self) -> float:
        """
        PHASE 37: Thermodynamic energy with decay.
        
        E = E_base * (1 - success_bonus) + decay_penalty
        
        - Base energy comes from complexity (cost)
        - Success reduces energy (LTP - Long Term Potentiation)
        - Disuse increases energy (entropy production)
        - Primitives don't accumulate decay
        """
        if self.usage_count == 0:
            base = self.cost + (0.0 if self.is_primitive else self.accumulated_decay)
            return base
        
        success_rate = self.success_count / self.usage_count
        # Energy = complexity * (1 - success_bonus) + decay
        base_energy = self.cost * (1.0 - 0.5 * success_rate)
        decay_penalty = 0.0 if self.is_primitive else self.accumulated_decay
        return base_energy + decay_penalty
    
    def utility(self) -> float:
        """
        PHASE 37: Utility score for consolidation decisions.
        
        High utility = used often AND successful
        """
        if self.usage_count == 0:
            return 0.0
        success_rate = self.success_count / self.usage_count
        # Utility combines frequency and success
        frequency_bonus = min(1.0, self.usage_count / 10.0)  # Saturates at 10 uses
        return success_rate * frequency_bonus
    
    def apply_decay(self, current_epoch: int, decay_rate: float = 0.05):
        """
        PHASE 37: Apply entropy-based decay.
        
        Operators that haven't been used recently accumulate decay.
        This implements "forgetting" - unused operators become expensive.
        """
        if self.is_primitive:
            return  # Axioms don't decay
        
        epochs_unused = current_epoch - self.last_used_epoch
        if epochs_unused > 0:
            # Decay is proportional to time unused
            self.accumulated_decay += decay_rate * epochs_unused
    
    def reinforce(self, current_epoch: int, reinforcement: float = 0.1):
        """
        PHASE 37: Reinforce operator after successful use (LTP).
        
        Reduces accumulated decay, making operator more likely to survive.
        """
        self.last_used_epoch = current_epoch
        # Reduce decay (but not below 0)
        self.accumulated_decay = max(0.0, self.accumulated_decay - reinforcement)
    
    def update_stats(self, success: bool):
        """Update usage statistics."""
        self.usage_count += 1
        if success:
            self.success_count += 1
    
    def should_prune(self, energy_threshold: float = 1.0) -> bool:
        """
        PHASE 37: Check if this operator should be pruned.
        
        Prune if:
        - Not a primitive (axioms survive)
        - High energy (expensive + unused)
        - Low utility (rarely successful)
        """
        if self.is_primitive:
            return False
        if self.source == 'primitive':
            return False  # Stock primitives survive
        
        return self.energy() > energy_threshold and self.utility() < 0.2


class ContentAddressedOperatorMemory:
    """
    The Operator Toolbox - content-addressed memory for discovered operators.
    
    Theory (Autopoiesis):
    - Operators are the "priors" the system discovers
    - Content-addressing prevents duplicates
    - Energy-based ranking guides composition search
    """
    
    def __init__(self):
        self.operators: Dict[str, CanonicalOperator] = {}
        self._init_primitives()
    
    def _init_primitives(self):
        """
        FIX 3: Stock toolbox with 42+ primitives (not just 7).
        
        Theory: The Lie Algebra generators span the transformation space.
        We need discrete realizations: Shift(dy,dx), Rotate(90), Color(i->j).
        """
        primitives = []
        
        # D4 Symmetry Group (8 elements)
        primitives.extend([
            CanonicalOperator('rotate90', {'angle': 90}, 
                            {'preserves_mass': True, 'preserves_color': True},
                            {'shape': 'may_change'}, 0.1, 'primitive'),
            CanonicalOperator('rotate180', {'angle': 180},
                            {'preserves_mass': True, 'preserves_color': True},
                            {'shape': 'preserved'}, 0.1, 'primitive'),
            CanonicalOperator('rotate270', {'angle': 270},
                            {'preserves_mass': True, 'preserves_color': True},
                            {'shape': 'may_change'}, 0.1, 'primitive'),
            CanonicalOperator('flip_h', {'axis': 'horizontal'},
                            {'preserves_mass': True, 'preserves_color': True},
                            {'shape': 'preserved'}, 0.1, 'primitive'),
            CanonicalOperator('flip_v', {'axis': 'vertical'},
                            {'preserves_mass': True, 'preserves_color': True},
                            {'shape': 'preserved'}, 0.1, 'primitive'),
            CanonicalOperator('transpose', {},
                            {'preserves_mass': True, 'preserves_color': True},
                            {'shape': 'may_change'}, 0.1, 'primitive'),
            CanonicalOperator('identity', {},
                            {'preserves_mass': True, 'preserves_color': True, 'preserves_shape': True},
                            {'all': 'preserved'}, 0.0, 'primitive'),
        ])
        
        # Translation generators: Shift(dy, dx) for small shifts
        for dy in range(-3, 4):
            for dx in range(-3, 4):
                if dy == 0 and dx == 0:
                    continue
                primitives.append(CanonicalOperator(
                    'translate', {'dy': dy, 'dx': dx},
                    {'preserves_mass': True, 'preserves_color': True},
                    {'position': 'shifted'}, 0.1, 'primitive'
                ))
        
        # Color swap generators: common single-color mappings
        # Background to foreground swaps
        for c in range(1, 10):
            primitives.append(CanonicalOperator(
                'color_map', {'mapping': {0: c}},
                {'preserves_mass': False, 'preserves_shape': True},
                {'color': 'changed'}, 0.1, 'primitive'
            ))
            primitives.append(CanonicalOperator(
                'color_map', {'mapping': {c: 0}},
                {'preserves_mass': False, 'preserves_shape': True},
                {'color': 'changed'}, 0.1, 'primitive'
            ))
        
        # Invert colors (swap two colors)
        for c1 in range(1, 5):
            for c2 in range(c1+1, 6):
                primitives.append(CanonicalOperator(
                    'color_map', {'mapping': {c1: c2, c2: c1}},
                    {'preserves_mass': True, 'preserves_shape': True},
                    {'color': 'swapped'}, 0.15, 'primitive'
                ))
        
        # Object-level operators (require SceneGraph analysis)
        # These are the missing operators for near-miss conversion
        primitives.extend([
            CanonicalOperator('extract_largest', {},
                {'preserves_color': True}, {'size': 'reduced'}, 0.2, 'primitive'),
            CanonicalOperator('extract_smallest', {},
                {'preserves_color': True}, {'size': 'reduced'}, 0.2, 'primitive'),
            CanonicalOperator('filter_by_majority_color', {},
                {'preserves_shape': True}, {'objects': 'filtered'}, 0.2, 'primitive'),
            CanonicalOperator('connect_aligned_h', {},
                {}, {'connectivity': 'increased'}, 0.2, 'primitive'),
            CanonicalOperator('connect_aligned_v', {},
                {}, {'connectivity': 'increased'}, 0.2, 'primitive'),
            CanonicalOperator('fill_enclosed', {},
                {}, {'holes': 'filled'}, 0.2, 'primitive'),
            CanonicalOperator('remove_background', {},
                {'preserves_shape': True}, {'background': 'removed'}, 0.15, 'primitive'),
            CanonicalOperator('crop_to_content', {},
                {}, {'size': 'reduced'}, 0.15, 'primitive'),
        ])
        
        # PHASE 34: Typed Predicate Templates (Small Basis)
        # Instead of enumerating all color combinations, define templates
        # that get instantiated during residual compilation based on task colors.
        # This keeps the generator set small but expressive.
        
        # Template: enclosed_by (any color) → paint with target color
        # Color=None means "infer from task context"
        primitives.append(CanonicalOperator(
            'relational_paint',
            {'predicate_type': 'enclosed_by', 
             'predicate_args': {'color': None, 'property': 'interior'},
             'paint_color': None},  # Inferred at application time
            {'relational': True, 'requires_scene_graph': True, 'template': True},
            {'fills_region': True},
            0.12, 'primitive_template'
        ))
        
        # Template: interior_of (any color) → paint interior
        primitives.append(CanonicalOperator(
            'relational_paint',
            {'predicate_type': 'interior_of',
             'predicate_args': {'color': None, 'property': 'interior'},
             'paint_color': None},
            {'relational': True, 'requires_scene_graph': True, 'template': True},
            {'fills_region': True},
            0.12, 'primitive_template'
        ))
        
        # Template: between_aligned → connect with line
        primitives.append(CanonicalOperator(
            'relational_paint',
            {'predicate_type': 'between_aligned',
             'predicate_args': {'color': None, 'property': 'line'},
             'paint_color': None},
            {'relational': True, 'requires_scene_graph': True, 'template': True},
            {'connects_objects': True},
            0.12, 'primitive_template'
        ))
        
        # Template: adjacent_to → expand/dilate
        primitives.append(CanonicalOperator(
            'relational_paint',
            {'predicate_type': 'adjacent_to',
             'predicate_args': {'color': None, 'property': 'border'},
             'paint_color': None},
            {'relational': True, 'requires_scene_graph': True, 'template': True},
            {'expands_region': True},
            0.12, 'primitive_template'
        ))
        
        for op in primitives:
            self.register(op)
    
    def register(self, op: CanonicalOperator) -> str:
        """Register an operator, return its hash."""
        h = op.content_hash()
        if h not in self.operators:
            self.operators[h] = op
        return h
    
    def get(self, op_hash: str) -> Optional[CanonicalOperator]:
        """Retrieve an operator by hash."""
        return self.operators.get(op_hash)
    
    def get_all(self) -> List[CanonicalOperator]:
        """Get all operators."""
        return list(self.operators.values())
    
    def get_by_energy(self, top_k: int = 10) -> List[CanonicalOperator]:
        """Get operators sorted by energy (lowest first = most promising)."""
        return sorted(self.operators.values(), key=lambda op: op.energy())[:top_k]
    
    def get_compatible(self, laws: List[str], state: np.ndarray = None, 
                        target: np.ndarray = None, top_k_bindings: int = 3) -> List[CanonicalOperator]:
        """
        Get operators compatible with given conservation laws.
        
        PHASE 35: Template Instantiation via MAP Inference
        Templates are morphism FAMILIES P_θ. At each A* node, we instantiate
        them with inferred parameters θ* = argmin E(P_θ(state), target).
        
        Returns concrete operators (templates get expanded into bindings).
        """
        result = []
        
        for op in self.operators.values():
            # Check if this is a template needing instantiation
            if op.preconditions.get('template', False):
                # Instantiate template with MAP-inferred bindings
                if state is not None and target is not None:
                    bindings = self._instantiate_template(op, state, target, top_k_bindings)
                    result.extend(bindings)
                # Skip templates if no state/target provided
                continue
            
            # Regular operator - include as-is
            result.append(op)
        
        # Sort by compatibility then energy
        def compatibility_score(op):
            score = 0
            if 'mass' in laws and op.preconditions.get('preserves_mass', False):
                score += 1
            if 'color_palette' in laws and op.preconditions.get('preserves_color', False):
                score += 1
            if 'shape' in laws and op.preconditions.get('preserves_shape', False):
                score += 1
            return -score
        
        return sorted(result, key=lambda op: (compatibility_score(op), op.energy()))
    
    def _instantiate_template(self, template: CanonicalOperator, state: np.ndarray,
                               target: np.ndarray, top_k: int = 3) -> List[CanonicalOperator]:
        """
        PHASE 35: MAP-style template instantiation.
        
        Theory: For template P_θ with latent θ = (predicate_color, paint_color, ...),
        find θ* = argmin_θ E_data(P_θ(state), target) + λE_sheaf + μE_laws
        
        In practice: enumerate candidate bindings from residual analysis,
        score each by how well P_θ(state) approaches target.
        """
        if template.op_type != 'relational_paint':
            return []
        
        predicate_type = template.params.get('predicate_type', 'interior_of')
        bindings = []
        
        # Analyze state and target to infer candidate bindings
        state_colors = set(np.unique(state)) - {0}
        target_colors = set(np.unique(target)) - {0}
        
        # Colors that appear in target but not state (need to be painted)
        new_colors = target_colors - state_colors
        # Colors that exist in both
        shared_colors = state_colors & target_colors
        
        # Build candidate θ values based on predicate type
        candidates = []
        
        if predicate_type == 'enclosed_by':
            # For enclosed_by: find enclosing objects, paint their interiors
            # Candidate: for each color that encloses something, paint with new/shared color
            for enclosing_color in shared_colors:
                for paint_color in (new_colors | shared_colors):
                    if paint_color != enclosing_color:
                        candidates.append({
                            'predicate_color': int(enclosing_color),
                            'paint_color': int(paint_color)
                        })
        
        elif predicate_type == 'interior_of':
            # For interior_of: fill inside of objects of a given color
            for obj_color in shared_colors:
                for paint_color in (new_colors | shared_colors):
                    if paint_color != obj_color:
                        candidates.append({
                            'predicate_color': int(obj_color),
                            'paint_color': int(paint_color)
                        })
        
        elif predicate_type == 'between_aligned':
            # For between_aligned: connect aligned objects with a line color
            for paint_color in (new_colors | shared_colors):
                candidates.append({
                    'predicate_color': None,  # Any aligned pair
                    'paint_color': int(paint_color)
                })
        
        elif predicate_type == 'adjacent_to':
            # For adjacent_to: expand borders of objects
            for obj_color in shared_colors:
                for paint_color in (new_colors | shared_colors):
                    candidates.append({
                        'predicate_color': int(obj_color),
                        'paint_color': int(paint_color)
                    })
        
        # Score candidates by how well they reduce E_data
        scored = []
        for θ in candidates[:20]:  # Limit candidates to avoid explosion
            # Create bound operator
            bound_params = template.params.copy()
            bound_params['paint_color'] = θ['paint_color']
            bound_params['predicate_args'] = template.params.get('predicate_args', {}).copy()
            bound_params['predicate_args']['color'] = θ.get('predicate_color')
            
            bound_op = CanonicalOperator(
                template.op_type,
                bound_params,
                {k: v for k, v in template.preconditions.items() if k != 'template'},
                template.postconditions,
                template.cost,
                'instantiated_template',
                template.confidence
            )
            
            # Score: try to apply and measure residual reduction
            # (Lightweight scoring - full E_sheaf is too expensive here)
            score = self._score_binding(bound_op, state, target)
            scored.append((score, bound_op))
        
        # Return top-K bindings
        scored.sort(key=lambda x: x[0])
        bindings = [op for score, op in scored[:top_k] if score < float('inf')]
        
        return bindings
    
    def _score_binding(self, op: CanonicalOperator, state: np.ndarray, 
                        target: np.ndarray) -> float:
        """
        Score a bound operator by E_data reduction potential.
        
        Returns: estimated energy after applying op (lower is better).
        """
        try:
            # Build scene graph and apply operator
            grid = ARCGrid(torch.tensor(state, dtype=torch.long))
            graph = SceneGraphBuilder().build(grid)
            
            # Get mask from predicate
            predicate_type = op.params.get('predicate_type', 'interior_of')
            predicate_args = op.params.get('predicate_args', {})
            paint_color = op.params.get('paint_color', 1)
            
            if paint_color is None:
                return float('inf')
            
            # Compute mask
            mask = self._evaluate_predicate_mask(state, graph, predicate_type, predicate_args)
            if mask is None or mask.sum() == 0:
                return float('inf')
            
            # Apply paint
            result = state.copy()
            result[mask] = paint_color
            
            if result.shape != target.shape:
                return float('inf')
            
            # E_data: fraction of pixels that differ from target
            E_data = (result != target).sum() / max(result.size, 1)
            
            # Bonus: if this reduces error vs original state
            E_orig = (state != target).sum() / max(state.size, 1)
            if E_data >= E_orig:
                return float('inf')  # No improvement
            
            return E_data
            
        except Exception:
            return float('inf')
    
    def _evaluate_predicate_mask(self, data: np.ndarray, graph: SceneGraph,
                                   predicate_type: str, predicate_args: Dict) -> Optional[np.ndarray]:
        """Evaluate a relational predicate to get a mask."""
        mask = np.zeros(data.shape, dtype=bool)
        pred_color = predicate_args.get('color')
        
        if predicate_type == 'interior_of':
            # Find interior of objects matching color
            for obj_id, obj in graph.objects.items():
                if pred_color is not None and obj.color != pred_color:
                    continue
                # Interior = bounding box minus the object pixels
                r_min, c_min = obj.position
                r_max = r_min + obj.height
                c_max = c_min + obj.width
                for r in range(r_min, min(r_max, data.shape[0])):
                    for c in range(c_min, min(c_max, data.shape[1])):
                        if data[r, c] == 0:  # Empty pixel inside bbox
                            mask[r, c] = True
        
        elif predicate_type == 'enclosed_by':
            # Similar to interior_of but specifically for enclosed regions
            for obj_id, obj in graph.objects.items():
                if pred_color is not None and obj.color != pred_color:
                    continue
                r_min, c_min = obj.position
                r_max = r_min + obj.height
                c_max = c_min + obj.width
                for r in range(r_min + 1, min(r_max - 1, data.shape[0])):
                    for c in range(c_min + 1, min(c_max - 1, data.shape[1])):
                        if data[r, c] == 0:
                            mask[r, c] = True
        
        elif predicate_type == 'between_aligned':
            # Connect horizontally or vertically aligned objects
            objs = list(graph.objects.values())
            for i, obj1 in enumerate(objs):
                for obj2 in objs[i+1:]:
                    c1 = obj1.centroid
                    c2 = obj2.centroid
                    # Horizontal alignment (same row)
                    if abs(c1[0] - c2[0]) < 2:
                        row = int((c1[0] + c2[0]) / 2)
                        c_min = int(min(c1[1], c2[1]))
                        c_max = int(max(c1[1], c2[1]))
                        if 0 <= row < data.shape[0]:
                            for c in range(c_min, min(c_max + 1, data.shape[1])):
                                if data[row, c] == 0:
                                    mask[row, c] = True
                    # Vertical alignment (same column)
                    if abs(c1[1] - c2[1]) < 2:
                        col = int((c1[1] + c2[1]) / 2)
                        r_min = int(min(c1[0], c2[0]))
                        r_max = int(max(c1[0], c2[0]))
                        if 0 <= col < data.shape[1]:
                            for r in range(r_min, min(r_max + 1, data.shape[0])):
                                if data[r, col] == 0:
                                    mask[r, col] = True
        
        elif predicate_type == 'adjacent_to':
            # Dilate: pixels adjacent to objects of given color
            for obj_id, obj in graph.objects.items():
                if pred_color is not None and obj.color != pred_color:
                    continue
                for r in range(data.shape[0]):
                    for c in range(data.shape[1]):
                        if data[r, c] == obj.color:
                            # Mark adjacent empty pixels
                            for dr, dc in [(-1,0),(1,0),(0,-1),(0,1)]:
                                nr, nc = r + dr, c + dc
                                if 0 <= nr < data.shape[0] and 0 <= nc < data.shape[1]:
                                    if data[nr, nc] == 0:
                                        mask[nr, nc] = True
        
        return mask if mask.sum() > 0 else None
    
    def update_operator(self, op_hash: str, success: bool):
        """Update operator statistics after use."""
        if op_hash in self.operators:
            self.operators[op_hash].update_stats(success)
    
    def get_stats(self) -> Dict:
        return {
            'total': len(self.operators),
            'by_source': Counter(op.source for op in self.operators.values()),
            'by_type': Counter(op.op_type for op in self.operators.values()),
            'top_energy': [(op.content_hash(), op.energy()) 
                          for op in self.get_by_energy(5)]
        }


# =============================================================================
# PHASE 36: TASK-SPECIFIC WORKING MEMORY
# =============================================================================
# Theory: The brain uses a Hippocampus (Working Memory) for task-specific
# context that shouldn't pollute long-term memory (Global Toolbox).
#
# Architecture:
#   Global Memory: Universal laws (Gravity, Symmetry, Translation)
#   Working Memory: Task-local ad-hoc rules (FixPixel(3,7), DeleteObj(3))
#
# Why separate?
#   - FixPixel(3,7)->Black is correct for Task A, wrong for Task B
#   - If promoted to Global, it pollutes the search space
#   - Working Memory is cleared between tasks
# =============================================================================

class WorkingMemory:
    """
    Phase 36: Task-scoped working memory (Hippocampus).
    
    Contains:
    1. Reference to Global Memory (read-only)
    2. Task-local ad-hoc operators (read-write)
    
    Ad-hoc operators are verified only against the current task and
    never promoted to Global Memory (unless they pass cross-task verification).
    """
    
    def __init__(self, global_memory: ContentAddressedOperatorMemory):
        self.global_memory = global_memory
        self.task_local: Dict[str, CanonicalOperator] = {}
        self.adhoc_stats = {'synthesized': 0, 'applied': 0, 'successful': 0}
    
    def add_adhoc(self, op: CanonicalOperator) -> str:
        """Add a task-local ad-hoc operator."""
        h = op.content_hash()
        if h not in self.task_local:
            self.task_local[h] = op
            self.adhoc_stats['synthesized'] += 1
        return h
    
    def get_all(self) -> List[CanonicalOperator]:
        """Get all operators: global + task-local."""
        # Global operators first (higher priority), then task-local
        global_ops = self.global_memory.get_all()
        local_ops = list(self.task_local.values())
        return global_ops + local_ops
    
    def get_compatible(self, laws: List[str], state: np.ndarray = None,
                       target: np.ndarray = None, top_k_bindings: int = 3) -> List[CanonicalOperator]:
        """
        Get operators compatible with laws, including task-local ad-hoc ops.
        
        Templates get instantiated. Ad-hoc ops are included as-is.
        """
        # Get global operators with template instantiation
        global_ops = self.global_memory.get_compatible(
            laws, state=state, target=target, top_k_bindings=top_k_bindings
        )
        
        # Add task-local ad-hoc operators (no instantiation needed - already bound)
        local_ops = list(self.task_local.values())
        
        # Sort: global first (by energy), then local (by energy)
        all_ops = global_ops + sorted(local_ops, key=lambda op: op.energy())
        return all_ops
    
    def get(self, op_hash: str) -> Optional[CanonicalOperator]:
        """Get operator by hash from either memory."""
        if op_hash in self.task_local:
            return self.task_local[op_hash]
        return self.global_memory.get(op_hash)
    
    def update_operator(self, op_hash: str, success: bool):
        """Update operator stats."""
        if op_hash in self.task_local:
            self.task_local[op_hash].update_stats(success)
            self.adhoc_stats['applied'] += 1
            if success:
                self.adhoc_stats['successful'] += 1
        else:
            self.global_memory.update_operator(op_hash, success)
    
    def clear(self):
        """Clear task-local memory (between tasks)."""
        self.task_local.clear()
    
    def get_stats(self) -> Dict:
        return {
            'global': self.global_memory.get_stats(),
            'task_local': len(self.task_local),
            'adhoc_stats': self.adhoc_stats,
            'adhoc_types': Counter(op.op_type for op in self.task_local.values())
        }
    
    def get_successful_adhoc(self) -> List[CanonicalOperator]:
        """Get all successful ad-hoc operators for consolidation."""
        return [op for op in self.task_local.values() 
                if op.success_count > 0]


# =============================================================================
# PHASE 37: THE CONSOLIDATION ENGINE (Sleep Cycle / Renormalization)
# =============================================================================
# Theory: Intelligence is COMPRESSION of ad-hoc fixes into persistent machinery.
#
# Inspired by:
# 1. SGC Sheaf Theory: Sections used often become part of the Structure Sheaf
# 2. Renormalization Group: Coarse-grain microscopic details into effective theories
# 3. Selectionism (Edelman): Generate variation, select what works, prune what doesn't
# 4. Sleep Consolidation: Memory replay strengthens important patterns
#
# The Dream Cycle:
# 1. Collect successful ad-hoc operators from the day
# 2. Detect patterns (coarse-graining)
# 3. Synthesize generalized operators (macro-ops)
# 4. Promote to Global Memory if they pass generality test
# 5. Prune high-energy, low-utility global operators
# =============================================================================

class ConsolidationEngine:
    """
    Phase 37: The Renormalization Cycle - consolidating Working Memory into Long-Term Memory.
    
    This implements the "Sleep" phase that complements the "Awake" phase (Phase 36).
    
    Key operations:
    1. coarse_grain(): Detect patterns in ad-hoc ops → synthesize macro-ops
    2. consolidate(): Promote high-utility generalized ops to Global Memory
    3. prune(): Kill high-energy low-utility operators (entropy death)
    4. dream_cycle(): Run full consolidation between tasks/batches
    """
    
    def __init__(self, global_memory: ContentAddressedOperatorMemory):
        self.global_memory = global_memory
        self.pending_consolidation: List[CanonicalOperator] = []
        self.current_epoch: int = 0
        self.consolidation_log: List[Dict] = []
        self.stats = {
            'coarse_grained': 0,
            'consolidated': 0,
            'pruned': 0,
            'dream_cycles': 0
        }
    
    def collect_from_working_memory(self, working_memory: WorkingMemory):
        """
        Collect successful ad-hoc operators from a task's working memory.
        
        These will be candidates for coarse-graining in the next dream cycle.
        """
        successful = working_memory.get_successful_adhoc()
        self.pending_consolidation.extend(successful)
    
    def coarse_grain_operators(self, ops: List[CanonicalOperator]) -> List[CanonicalOperator]:
        """
        PHASE 37: Detect patterns in ad-hoc operators and synthesize macro-ops.
        
        Examples:
        - FixPixel(0,0,Black), FixPixel(0,1,Black), FixPixel(0,2,Black) → SetRow(0, Black)
        - FixPixel(r,c,X) for many (r,c) in a region → FillRegion(bbox, X)
        - fix_color_swap(1→2) used 5x → color_map({1:2}) promoted
        
        This is "Renormalization" - coarse-graining micro-ops into macro-ops.
        """
        if len(ops) < 2:
            return []
        
        macro_ops = []
        
        # Group ops by type
        by_type = {}
        for op in ops:
            if op.op_type not in by_type:
                by_type[op.op_type] = []
            by_type[op.op_type].append(op)
        
        # Pattern 1: Multiple fix_pixel with same color → row/column/region fill
        if 'fix_pixel' in by_type and len(by_type['fix_pixel']) >= 3:
            macro = self._coarse_grain_fix_pixels(by_type['fix_pixel'])
            if macro:
                macro_ops.extend(macro)
        
        # Pattern 2: Multiple fix_region → larger region pattern
        if 'fix_region' in by_type and len(by_type['fix_region']) >= 2:
            macro = self._coarse_grain_fix_regions(by_type['fix_region'])
            if macro:
                macro_ops.extend(macro)
        
        # Pattern 3: Consistent fix_color_swap → promote to color_map
        if 'fix_color_swap' in by_type and len(by_type['fix_color_swap']) >= 2:
            macro = self._coarse_grain_color_swaps(by_type['fix_color_swap'])
            if macro:
                macro_ops.extend(macro)
        
        self.stats['coarse_grained'] += len(macro_ops)
        return macro_ops
    
    def _coarse_grain_fix_pixels(self, pixel_ops: List[CanonicalOperator]) -> List[CanonicalOperator]:
        """
        Detect row/column/region patterns in fix_pixel operations.
        
        If pixels are aligned in a row → SetRow(row, color)
        If pixels are aligned in a column → SetColumn(col, color)
        If pixels form a rectangular region → FillRect(bbox, color)
        """
        # Group by color
        by_color = {}
        for op in pixel_ops:
            color = op.params.get('color', 0)
            if color not in by_color:
                by_color[color] = []
            by_color[color].append((op.params.get('row', 0), op.params.get('col', 0)))
        
        macro_ops = []
        
        for color, positions in by_color.items():
            if len(positions) < 2:
                continue
            
            rows = [p[0] for p in positions]
            cols = [p[1] for p in positions]
            
            # Check for row pattern (all same row)
            if len(set(rows)) == 1 and len(cols) >= 2:
                row = rows[0]
                col_min, col_max = min(cols), max(cols)
                # If consecutive columns
                if col_max - col_min + 1 == len(cols):
                    macro_ops.append(CanonicalOperator(
                        op_type='set_row_segment',
                        params={'row': row, 'col_start': col_min, 'col_end': col_max, 'color': color},
                        preconditions={'consolidated': True},
                        postconditions={'row_painted': True},
                        cost=0.05,  # Lower cost than individual fix_pixels
                        source='consolidated',
                        confidence=0.9,
                        generalized_from=[f"fix_pixel_{p[0]}_{p[1]}" for p in positions]
                    ))
            
            # Check for column pattern (all same column)
            elif len(set(cols)) == 1 and len(rows) >= 2:
                col = cols[0]
                row_min, row_max = min(rows), max(rows)
                if row_max - row_min + 1 == len(rows):
                    macro_ops.append(CanonicalOperator(
                        op_type='set_col_segment',
                        params={'col': col, 'row_start': row_min, 'row_end': row_max, 'color': color},
                        preconditions={'consolidated': True},
                        postconditions={'col_painted': True},
                        cost=0.05,
                        source='consolidated',
                        confidence=0.9,
                        generalized_from=[f"fix_pixel_{p[0]}_{p[1]}" for p in positions]
                    ))
            
            # Check for rectangular region
            elif len(positions) >= 4:
                row_min, row_max = min(rows), max(rows)
                col_min, col_max = min(cols), max(cols)
                expected_size = (row_max - row_min + 1) * (col_max - col_min + 1)
                if len(positions) >= 0.8 * expected_size:  # At least 80% filled
                    macro_ops.append(CanonicalOperator(
                        op_type='fill_rect',
                        params={'bbox': (row_min, col_min, row_max, col_max), 'color': color},
                        preconditions={'consolidated': True},
                        postconditions={'region_filled': True},
                        cost=0.08,
                        source='consolidated',
                        confidence=0.85,
                        generalized_from=[f"fix_pixel_{p[0]}_{p[1]}" for p in positions]
                    ))
        
        return macro_ops
    
    def _coarse_grain_fix_regions(self, region_ops: List[CanonicalOperator]) -> List[CanonicalOperator]:
        """
        Detect patterns in fix_region operations.
        
        If multiple regions share color/shape properties → generalized region op
        """
        # Group by color
        by_color = {}
        for op in region_ops:
            color = op.params.get('color', 0)
            if color not in by_color:
                by_color[color] = []
            by_color[color].append(op)
        
        macro_ops = []
        
        for color, ops in by_color.items():
            if len(ops) >= 2:
                # Merge regions into a single macro-op
                macro_ops.append(CanonicalOperator(
                    op_type='multi_region_fill',
                    params={'color': color, 'region_count': len(ops)},
                    preconditions={'consolidated': True},
                    postconditions={'regions_filled': True},
                    cost=0.1,
                    source='consolidated',
                    confidence=0.8,
                    generalized_from=[op.content_hash() for op in ops]
                ))
        
        return macro_ops
    
    def _coarse_grain_color_swaps(self, swap_ops: List[CanonicalOperator]) -> List[CanonicalOperator]:
        """
        Promote consistent color swaps to global color_map operators.
        
        If fix_color_swap(1→2) appears in multiple tasks → color_map({1:2})
        """
        # Count swap frequencies
        swap_counts = Counter()
        for op in swap_ops:
            from_c = op.params.get('from_color', 0)
            to_c = op.params.get('to_color', 0)
            swap_counts[(from_c, to_c)] += 1
        
        macro_ops = []
        
        for (from_c, to_c), count in swap_counts.items():
            if count >= 2:  # Appeared at least twice
                macro_ops.append(CanonicalOperator(
                    op_type='color_map',
                    params={'mapping': {from_c: to_c}},
                    preconditions={'preserves_mass': False, 'preserves_shape': True, 'consolidated': True},
                    postconditions={'color': 'changed'},
                    cost=0.1,
                    source='consolidated',
                    confidence=min(1.0, 0.5 + count * 0.1),
                    generalized_from=[f"fix_color_swap_{from_c}_{to_c}"] * count
                ))
        
        return macro_ops
    
    def consolidate_to_global(self, macro_ops: List[CanonicalOperator]) -> int:
        """
        Promote generalized macro-ops to Global Memory.
        
        Only promotes if the operator passes the "Generality Test":
        - Not already in global memory (content-addressed check)
        - Improves compression (cost < sum of original micro-ops)
        """
        promoted = 0
        
        for op in macro_ops:
            op_hash = op.content_hash()
            
            # Skip if already exists
            if op_hash in self.global_memory.operators:
                continue
            
            # Register to global memory
            self.global_memory.register(op)
            promoted += 1
            
            self.consolidation_log.append({
                'action': 'consolidate',
                'op_type': op.op_type,
                'op_hash': op_hash,
                'epoch': self.current_epoch,
                'generalized_from': len(op.generalized_from)
            })
        
        self.stats['consolidated'] += promoted
        return promoted
    
    def prune_memory(self, energy_threshold: float = 1.0) -> int:
        """
        PHASE 37: Prune high-energy, low-utility operators.
        
        This implements "forgetting" - operators that aren't used decay
        and eventually die, freeing up cognitive resources.
        """
        to_prune = []
        
        for op_hash, op in list(self.global_memory.operators.items()):
            if op.should_prune(energy_threshold):
                to_prune.append(op_hash)
        
        for op_hash in to_prune:
            op = self.global_memory.operators.pop(op_hash)
            self.consolidation_log.append({
                'action': 'prune',
                'op_type': op.op_type,
                'op_hash': op_hash,
                'epoch': self.current_epoch,
                'final_energy': op.energy(),
                'final_utility': op.utility()
            })
        
        self.stats['pruned'] += len(to_prune)
        return len(to_prune)
    
    def apply_decay_to_all(self, decay_rate: float = 0.02):
        """
        Apply entropy-based decay to all non-primitive operators.
        
        This implements the "aging" of operators - those not reinforced
        become more expensive and eventually die.
        """
        for op in self.global_memory.operators.values():
            op.apply_decay(self.current_epoch, decay_rate)
    
    def dream_cycle(self, decay_rate: float = 0.02, prune_threshold: float = 1.0,
                    verbose: bool = False) -> Dict:
        """
        PHASE 37: The full Dream Cycle - run between tasks or batches.
        
        Steps:
        1. Apply decay to all operators (entropy production)
        2. Coarse-grain pending ad-hoc operators
        3. Consolidate high-utility macro-ops to Global Memory
        4. Prune high-energy low-utility operators
        5. Clear pending queue
        
        Returns statistics about the cycle.
        """
        self.current_epoch += 1
        cycle_stats = {'epoch': self.current_epoch}
        
        # Step 1: Apply decay
        self.apply_decay_to_all(decay_rate)
        
        # Step 2: Coarse-grain pending ad-hoc ops
        if self.pending_consolidation:
            macro_ops = self.coarse_grain_operators(self.pending_consolidation)
            cycle_stats['macro_ops_synthesized'] = len(macro_ops)
            
            if verbose and macro_ops:
                print(f"  [DREAM] Coarse-grained {len(self.pending_consolidation)} ad-hoc -> {len(macro_ops)} macro-ops")
            
            # Step 3: Consolidate to Global Memory
            promoted = self.consolidate_to_global(macro_ops)
            cycle_stats['promoted'] = promoted
            
            if verbose and promoted:
                print(f"  [DREAM] Promoted {promoted} macro-ops to Global Memory")
        else:
            cycle_stats['macro_ops_synthesized'] = 0
            cycle_stats['promoted'] = 0
        
        # Step 4: Prune
        pruned = self.prune_memory(prune_threshold)
        cycle_stats['pruned'] = pruned
        
        if verbose and pruned:
            print(f"  [DREAM] Pruned {pruned} high-energy operators")
        
        # Step 5: Clear pending
        self.pending_consolidation.clear()
        
        self.stats['dream_cycles'] += 1
        cycle_stats['global_memory_size'] = len(self.global_memory.operators)
        
        return cycle_stats
    
    def get_stats(self) -> Dict:
        return {
            **self.stats,
            'pending': len(self.pending_consolidation),
            'current_epoch': self.current_epoch,
            'global_memory_size': len(self.global_memory.operators)
        }


class ResidualCompiler:
    """
    Phase 32: The Residual Compiler - turns Δ = y ⊖ ŷ into typed operators.
    
    Theory (Information Geometry):
    - A residual encodes "what's missing" between prediction and target
    - By classifying residuals into physics families, we can synthesize operators
    - Verified operators become new priors (tools) for future use
    
    Pipeline:
    1. Compute Δ = target - prediction (pixel-wise difference)
    2. Extract delta descriptors (sufficient statistics)
    3. Classify into physics family (translate, recolor, fill, connect, etc.)
    4. Synthesize candidate operator
    5. Verify across all training examples
    6. If verified, promote to operator memory
    """
    
    # Physics families for residual classification
    FAMILIES = ['translate', 'color_map', 'boundary_fill', 'connect', 
                'crop_expand', 'pattern_tile', 'unknown']
    
    def __init__(self, memory: ContentAddressedOperatorMemory):
        self.memory = memory
        self.compilation_log: List[Dict] = []
    
    def compile(self, prediction: ARCGrid, target: ARCGrid, 
                task: ARCTask, laws: List[str]) -> Optional[CanonicalOperator]:
        """
        Compile a residual into a typed operator.
        
        Returns the operator if successfully verified, None otherwise.
        
        TRAINING-FIRST COMPILATION:
        Instead of deriving operators from test prediction→target (which doesn't
        generalize), derive from training input→output patterns and verify.
        """
        # TRY TRAINING-BASED COMPILATION FIRST
        # Derive operators from training examples directly
        candidate = self._compile_from_training(task, laws)
        if candidate is not None:
            return candidate
        
        # FALLBACK: Original residual-based compilation (test prediction→target)
        pred_data = prediction.data.numpy() if isinstance(prediction.data, torch.Tensor) else prediction.data
        target_data = target.data.numpy() if isinstance(target.data, torch.Tensor) else target.data
        
        # Step 1: Compute delta
        if pred_data.shape != target_data.shape:
            # Size mismatch - try crop/expand family
            return self._compile_size_change(prediction, target, task, laws)
        
        delta = (target_data != pred_data).astype(np.int32)
        if delta.sum() == 0:
            return None  # Already perfect
        
        # Step 2: Extract delta descriptors
        descriptors = self._extract_descriptors(pred_data, target_data, delta)
        
        # Step 3: Classify into physics family
        family = self._classify_family(descriptors, laws, pred_data, target_data)
        
        # Step 4: Synthesize candidate operator
        change_ratio = descriptors.get('change_ratio', 1.0)
        candidate = None
        
        if change_ratio < 0.20:
            candidate = self._synthesize_relational_operator(pred_data, target_data, task)
        
        if candidate is None:
            candidate = self._synthesize(family, descriptors, pred_data, target_data)
        
        if candidate is None:
            candidate = self._synthesize_relational_operator(pred_data, target_data, task)
        
        if candidate is None:
            return None
        
        # Step 5: Verify across training examples
        if not self._verify(candidate, task):
            self.compilation_log.append({'family': family, 'verified': False})
            return None
        
        # Step 6: Promote to memory
        op_hash = self.memory.register(candidate)
        self.compilation_log.append({
            'family': family, 
            'verified': True, 
            'hash': op_hash,
            'type': candidate.op_type
        })
        
        return candidate
    
    def _compile_from_training(self, task: ARCTask, laws: List[str]) -> Optional[CanonicalOperator]:
        """
        TRAINING-FIRST COMPILATION:
        Derive operators from training input→output patterns directly.
        This ensures the operator generalizes across examples.
        
        PARTIAL OPERATOR SUPPORT:
        Extract operators that explain part of the transformation, tagged
        as partial operators that can compose with others.
        """
        if len(task.train_examples) < 1:
            return None
        
        ex = task.train_examples[0]
        inp = ex.input_grid.data.numpy() if isinstance(ex.input_grid.data, torch.Tensor) else ex.input_grid.data
        out = ex.output_grid.data.numpy() if isinstance(ex.output_grid.data, torch.Tensor) else ex.output_grid.data
        
        # Try geometric transforms first (most transferable)
        if inp.shape == out.shape:
            geo_type = self._check_geometric(inp, out)
            if geo_type:
                candidate = self._synthesize(geo_type, {}, inp, out)
                if candidate and self._verify(candidate, task):
                    self.compilation_log.append({'family': geo_type, 'verified': True, 'type': geo_type})
                    return candidate
        
        # Try relational operators (context-dependent)
        if inp.shape == out.shape:
            candidate = self._synthesize_relational_operator(inp, out, task)
            if candidate and self._verify(candidate, task):
                self.compilation_log.append({'family': 'relational', 'verified': True, 'type': candidate.op_type})
                return candidate
        
        # Try PARTIAL color operators
        # Find the dominant color change pattern across ALL training examples
        if inp.shape == out.shape and len(task.train_examples) >= 2:
            candidate = self._compile_partial_color_op(task)
            if candidate:
                return candidate
        
        return None
    
    def _compile_partial_color_op(self, task: ARCTask) -> Optional[CanonicalOperator]:
        """
        Compile a partial color operator by finding consistent color changes
        across training examples.
        
        Key insight: Don't apply globally - find the COMMON pattern of change.
        """
        # Collect color change patterns from all examples
        all_changes = []
        
        for ex in task.train_examples:
            inp = ex.input_grid.data.numpy() if isinstance(ex.input_grid.data, torch.Tensor) else ex.input_grid.data
            out = ex.output_grid.data.numpy() if isinstance(ex.output_grid.data, torch.Tensor) else ex.output_grid.data
            
            if inp.shape != out.shape:
                continue
            
            delta_mask = (out != inp)
            if delta_mask.sum() == 0:
                continue
            
            # Get color changes
            from_colors = inp[delta_mask]
            to_colors = out[delta_mask]
            
            for fc, tc in zip(from_colors, to_colors):
                all_changes.append((int(fc), int(tc)))
        
        if not all_changes:
            return None
        
        # Find the most common color change
        from collections import Counter
        change_counts = Counter(all_changes)
        most_common, count = change_counts.most_common(1)[0]
        
        # Require the change to appear in multiple examples
        if count < 2:
            return None
        
        from_c, to_c = most_common
        
        # Create a GUARDED color operator
        # This operator only changes from_c to to_c (not a global recolor)
        candidate = CanonicalOperator(
            op_type='guarded_recolor',
            params={
                'from_color': from_c,
                'to_color': to_c,
                'guard': 'contextual',  # Applied contextually, not globally
            },
            preconditions={'partial': True},
            postconditions={'color': 'changed'},
            cost=0.15,
            source='compiled_partial',
            confidence=0.7
        )
        
        # Verify with relaxed criteria (at least one example improves)
        if self._verify(candidate, task):
            self.compilation_log.append({
                'family': 'guarded_recolor', 
                'verified': True, 
                'type': 'guarded_recolor',
                'params': candidate.params
            })
            return candidate
        
        return None
    
    def _extract_descriptors(self, pred: np.ndarray, target: np.ndarray, 
                            delta: np.ndarray) -> Dict[str, Any]:
        """Extract sufficient statistics from the delta."""
        # Find changed pixels
        changed_mask = delta > 0
        changed_positions = np.argwhere(changed_mask)
        
        if len(changed_positions) == 0:
            return {'empty': True}
        
        # Color changes
        pred_colors = pred[changed_mask]
        target_colors = target[changed_mask]
        color_changes = list(zip(pred_colors.tolist(), target_colors.tolist()))
        unique_changes = set(color_changes)
        
        # Spatial statistics
        centroid = changed_positions.mean(axis=0) if len(changed_positions) > 0 else [0, 0]
        
        # Check for translation pattern
        # If the non-zero pixels in pred match non-zero in target but shifted
        pred_nonzero = np.argwhere(pred > 0)
        target_nonzero = np.argwhere(target > 0)
        
        translation = None
        if len(pred_nonzero) > 0 and len(target_nonzero) > 0:
            pred_centroid = pred_nonzero.mean(axis=0)
            target_centroid = target_nonzero.mean(axis=0)
            shift = target_centroid - pred_centroid
            if np.abs(shift).max() < 10:  # Reasonable shift
                translation = tuple(shift.astype(int).tolist())
        
        # Check for color mapping
        color_map = {}
        if len(unique_changes) <= 5:  # Simple color mapping
            for from_c, to_c in unique_changes:
                if from_c not in color_map:
                    color_map[from_c] = to_c
                elif color_map[from_c] != to_c:
                    color_map = {}  # Inconsistent mapping
                    break
        
        # Boundary analysis
        boundary_fill = False
        if len(changed_positions) > 0:
            # Check if changes are at boundaries
            h, w = pred.shape
            at_boundary = (changed_positions[:, 0] == 0).any() or \
                         (changed_positions[:, 0] == h-1).any() or \
                         (changed_positions[:, 1] == 0).any() or \
                         (changed_positions[:, 1] == w-1).any()
            boundary_fill = at_boundary and len(unique_changes) == 1
        
        return {
            'empty': False,
            'num_changed': int(delta.sum()),
            'centroid': centroid.tolist(),
            'translation': translation,
            'color_map': color_map,
            'unique_changes': len(unique_changes),
            'boundary_fill': boundary_fill,
            'change_ratio': float(delta.sum()) / delta.size
        }
    
    def _classify_family(self, descriptors: Dict, laws: List[str],
                        pred: np.ndarray = None, target: np.ndarray = None) -> str:
        """
        FIX 4: Expanded classification to include geometric transformations.
        
        Classify the residual into a physics family.
        """
        if descriptors.get('empty', False):
            return 'unknown'
        
        # Check geometric transformations first (rotation, flip)
        if pred is not None and target is not None and pred.shape == target.shape:
            geom = self._check_geometric(pred, target)
            if geom:
                return geom
        
        # Translation: mass/shape preserved, centroid shifted
        if descriptors.get('translation') and 'mass' in laws:
            return 'translate'
        
        # Color mapping: simple 1-to-1 color changes
        if descriptors.get('color_map') and len(descriptors['color_map']) > 0:
            return 'color_map'
        
        # Boundary fill: changes at edges
        if descriptors.get('boundary_fill'):
            return 'boundary_fill'
        
        # Small localized changes might be connect/fill
        if descriptors.get('change_ratio', 1.0) < 0.3:
            return 'connect'
        
        return 'unknown'
    
    def _check_geometric(self, pred: np.ndarray, target: np.ndarray) -> Optional[str]:
        """FIX 4: Check if residual can be explained by geometric transformation."""
        # Check rotations
        if np.array_equal(np.rot90(pred, 1), target):
            return 'rotate90'
        if np.array_equal(np.rot90(pred, 2), target):
            return 'rotate180'
        if np.array_equal(np.rot90(pred, 3), target):
            return 'rotate270'
        
        # Check flips
        if np.array_equal(np.fliplr(pred), target):
            return 'flip_h'
        if np.array_equal(np.flipud(pred), target):
            return 'flip_v'
        
        # Check transpose
        if pred.shape[0] == pred.shape[1] and np.array_equal(pred.T, target):
            return 'transpose'
        
        return None
    
    def _synthesize(self, family: str, descriptors: Dict,
                   pred: np.ndarray, target: np.ndarray) -> Optional[CanonicalOperator]:
        """Synthesize an operator from the family and descriptors."""
        
        # FIX 4: Handle geometric transformations
        if family == 'rotate90':
            return CanonicalOperator('rotate90', {'angle': 90},
                {'preserves_mass': True, 'preserves_color': True},
                {'shape': 'may_change'}, 0.1, 'compiled', confidence=1.0)
        elif family == 'rotate180':
            return CanonicalOperator('rotate180', {'angle': 180},
                {'preserves_mass': True, 'preserves_color': True},
                {'shape': 'preserved'}, 0.1, 'compiled', confidence=1.0)
        elif family == 'rotate270':
            return CanonicalOperator('rotate270', {'angle': 270},
                {'preserves_mass': True, 'preserves_color': True},
                {'shape': 'may_change'}, 0.1, 'compiled', confidence=1.0)
        elif family == 'flip_h':
            return CanonicalOperator('flip_h', {'axis': 'horizontal'},
                {'preserves_mass': True, 'preserves_color': True},
                {'shape': 'preserved'}, 0.1, 'compiled', confidence=1.0)
        elif family == 'flip_v':
            return CanonicalOperator('flip_v', {'axis': 'vertical'},
                {'preserves_mass': True, 'preserves_color': True},
                {'shape': 'preserved'}, 0.1, 'compiled', confidence=1.0)
        elif family == 'transpose':
            return CanonicalOperator('transpose', {},
                {'preserves_mass': True, 'preserves_color': True},
                {'shape': 'may_change'}, 0.1, 'compiled', confidence=1.0)
        
        elif family == 'translate':
            dy, dx = descriptors['translation']
            return CanonicalOperator(
                op_type='translate',
                params={'dy': dy, 'dx': dx},
                preconditions={'preserves_mass': True, 'preserves_color': True},
                postconditions={'shape': 'preserved'},
                cost=0.1,  # Reduced cost for better A* balance
                source='compiled',
                confidence=0.9
            )
        
        elif family == 'color_map':
            mapping = descriptors['color_map']
            if not mapping:
                return None
            return CanonicalOperator(
                op_type='color_map',
                params={'mapping': mapping},
                preconditions={'preserves_mass': True, 'preserves_shape': True},
                postconditions={'color': 'changed'},
                cost=0.1 + 0.05 * len(mapping),
                source='compiled',
                confidence=0.95
            )
        
        elif family == 'boundary_fill':
            # Detect fill color
            target_at_boundary = target[0, :].tolist() + target[-1, :].tolist() + \
                               target[:, 0].tolist() + target[:, -1].tolist()
            fill_color = max(set(target_at_boundary), key=target_at_boundary.count)
            return CanonicalOperator(
                op_type='boundary_fill',
                params={'color': int(fill_color)},
                preconditions={},
                postconditions={'boundary': 'filled'},
                cost=0.3,
                source='compiled',
                confidence=0.7
            )
        
        elif family == 'connect':
            # Connect operator - fills gaps between aligned objects
            return CanonicalOperator(
                op_type='connect',
                params={},
                preconditions={},
                postconditions={'connectivity': 'increased'},
                cost=0.4,
                source='compiled',
                confidence=0.6
            )
        
        # FIX 8: Synthesize guarded local operators for localized changes
        elif family == 'guarded_local':
            mask_info = descriptors.get('mask_info', {})
            action_info = descriptors.get('action_info', {})
            return CanonicalOperator(
                op_type='guarded_paint',
                params={
                    'mask_predicate': mask_info.get('predicate', 'delta'),
                    'mask_coords': mask_info.get('coords', []),
                    'action': action_info.get('action', 'paint'),
                    'color': action_info.get('color', 1),
                },
                preconditions={'local': True, 'scene_graph': mask_info.get('uses_graph', False)},
                postconditions={'localized_change': True},
                cost=0.15,
                source='compiled',
                confidence=0.8
            )
        
        return None
    
    def synthesize_adhoc_operators(self, pred: np.ndarray, target: np.ndarray,
                                    working_memory: 'WorkingMemory') -> List[CanonicalOperator]:
        """
        PHASE 36: Synthesize Ad-Hoc operators for residual cleanup.
        
        Theory: Near-misses (F ≈ 0.02-0.08) need pixel-level or object-level fixes.
        These are TASK-LOCAL operators that shouldn't pollute Global Memory.
        
        Synthesizes:
        - FixPixel(r, c, color): For single-pixel errors
        - FixRegion(mask, color): For small contiguous regions  
        - FixObject(obj_id, action): For object-specific errors
        
        These go into WorkingMemory, not Global Memory.
        """
        if pred.shape != target.shape:
            return []
        
        delta_mask = (pred != target)
        if not delta_mask.any():
            return []
        
        adhoc_ops = []
        
        # Get changed pixel positions and their target colors
        changed_positions = np.argwhere(delta_mask)
        num_changed = len(changed_positions)
        
        # Strategy 1: Single-pixel fixes (for very small residuals)
        if num_changed <= 10:
            # Create FixPixel ops for each changed pixel
            for pos in changed_positions:
                r, c = int(pos[0]), int(pos[1])
                target_color = int(target[r, c])
                
                op = CanonicalOperator(
                    op_type='fix_pixel',
                    params={'row': r, 'col': c, 'color': target_color},
                    preconditions={'adhoc': True, 'local': True},
                    postconditions={'pixel_fixed': True},
                    cost=0.01,  # Very low cost - cleanup operation
                    source='adhoc',
                    confidence=1.0  # Deterministic fix
                )
                adhoc_ops.append(op)
                working_memory.add_adhoc(op)
        
        # Strategy 2: Contiguous region fixes (for small connected components)
        if num_changed <= 50:
            # Label connected components in the delta
            from scipy import ndimage as ndi
            labeled, num_features = ndi.label(delta_mask)
            
            for region_id in range(1, num_features + 1):
                region_mask = (labeled == region_id)
                region_size = region_mask.sum()
                
                if region_size <= 20:  # Small enough to fix as a unit
                    # Find the target color(s) for this region
                    region_colors = target[region_mask]
                    target_color = int(np.median(region_colors))
                    
                    # Get region bounding box
                    region_coords = np.argwhere(region_mask)
                    r_min, c_min = region_coords.min(axis=0)
                    r_max, c_max = region_coords.max(axis=0)
                    
                    # Store mask relative to bounding box
                    local_mask = region_mask[r_min:r_max+1, c_min:c_max+1]
                    
                    op = CanonicalOperator(
                        op_type='fix_region',
                        params={
                            'bbox': (int(r_min), int(c_min), int(r_max), int(c_max)),
                            'local_mask': local_mask.tolist(),
                            'color': target_color
                        },
                        preconditions={'adhoc': True, 'local': True},
                        postconditions={'region_fixed': True},
                        cost=0.02,  # Slightly higher than single pixel
                        source='adhoc',
                        confidence=1.0
                    )
                    adhoc_ops.append(op)
                    working_memory.add_adhoc(op)
        
        # Strategy 3: Color-based region fixes (all pixels of color X → color Y)
        # Useful when specific colors need swapping in residual
        pred_at_changed = pred[delta_mask]
        target_at_changed = target[delta_mask]
        
        color_swaps = {}
        for p_color, t_color in zip(pred_at_changed, target_at_changed):
            p_color, t_color = int(p_color), int(t_color)
            if p_color not in color_swaps:
                color_swaps[p_color] = Counter()
            color_swaps[p_color][t_color] += 1
        
        # Create color swap ops for consistent mappings
        for from_color, to_counts in color_swaps.items():
            to_color, count = to_counts.most_common(1)[0]
            # Only if this swap explains most of the changes for this color
            total_from = pred_at_changed[pred_at_changed == from_color].size
            if count >= 0.8 * total_from and count >= 2:
                op = CanonicalOperator(
                    op_type='fix_color_swap',
                    params={'from_color': from_color, 'to_color': to_color},
                    preconditions={'adhoc': True},
                    postconditions={'colors_swapped': True},
                    cost=0.03,
                    source='adhoc',
                    confidence=count / max(total_from, 1)
                )
                adhoc_ops.append(op)
                working_memory.add_adhoc(op)
        
        return adhoc_ops
    
    def _synthesize_relational_operator(self, pred: np.ndarray, target: np.ndarray,
                                         task: ARCTask) -> Optional[CanonicalOperator]:
        """
        PHASE 33: Synthesize Relational Predicate Operators.
        
        Theory (SGC First Principles):
        - Solutions are Global Sections of a Sheaf
        - Operators must be defined on Topology (SceneGraph), not Geometry (Coordinates)
        - A relational predicate like "interior_of(color=Red)" is Universally Quantified
        - A coordinate mask like "pixels[0:5, 0:5]" is Existentially Quantified
        
        This synthesizer:
        1. Builds SceneGraph from the prediction grid
        2. Finds which SceneGraph node(s) contain the residual
        3. Synthesizes a relational predicate (e.g., "fill_interior(filter_by_color(X))")
        4. The predicate can be evaluated on ANY grid's SceneGraph
        """
        if pred.shape != target.shape:
            return None
        
        # Compute the delta (residual)
        delta_mask = (pred != target)
        if not delta_mask.any():
            return None
        
        # Build SceneGraph for the prediction grid
        try:
            pred_grid = ARCGrid(torch.tensor(pred, dtype=torch.long))
            graph = SceneGraphBuilder().build(pred_grid)
        except Exception:
            return None
        
        if not graph.objects:
            return None
        
        # Find which object(s) contain the residual
        changed_rows, changed_cols = np.where(delta_mask)
        change_colors_from = pred[delta_mask]
        change_colors_to = target[delta_mask]
        
        # Analyze color changes
        unique_from = np.unique(change_colors_from)
        unique_to = np.unique(change_colors_to)
        
        # Find the object that best explains the residual location
        best_match = self._find_containing_object(graph, changed_rows, changed_cols, pred)
        
        if best_match is None:
            return None
        
        obj_id, obj, relation_type = best_match
        
        # Determine action type based on color change pattern
        if len(unique_from) == 1 and unique_from[0] == 0:
            # Paint: background -> color
            paint_color = int(np.bincount(change_colors_to).argmax())
            
            return CanonicalOperator(
                op_type='relational_paint',
                params={
                    'predicate_type': relation_type,
                    'predicate_args': {'color': obj.color, 'property': 'interior'},
                    'paint_color': paint_color,
                },
                preconditions={'relational': True, 'requires_scene_graph': True},
                postconditions={'fills_region': True},
                cost=0.12,
                source='compiled_relational',
                confidence=0.9
            )
        
        elif len(unique_from) == 1 and len(unique_to) == 1:
            # Recolor: color A -> color B in specific region
            from_color = int(unique_from[0])
            to_color = int(unique_to[0])
            
            return CanonicalOperator(
                op_type='relational_recolor',
                params={
                    'predicate_type': relation_type,
                    'predicate_args': {'color': obj.color, 'property': 'interior'},
                    'from_color': from_color,
                    'to_color': to_color,
                },
                preconditions={'relational': True, 'requires_scene_graph': True},
                postconditions={'recolors_region': True},
                cost=0.12,
                source='compiled_relational',
                confidence=0.9
            )
        
        return None
    
    def _find_containing_object(self, graph: SceneGraph, rows: np.ndarray, 
                                 cols: np.ndarray, pred: np.ndarray) -> Optional[Tuple]:
        """
        Find the SceneGraph object that best explains the residual location.
        
        Returns (obj_id, obj, relation_type) where relation_type is one of:
        - 'interior_of': residual is inside the object's bounding box
        - 'enclosed_by': residual is in a region enclosed by the object
        - 'adjacent_to': residual is adjacent to the object
        - 'between': residual is between two aligned objects
        """
        from scipy.ndimage import binary_fill_holes
        
        # Create mask of residual positions
        residual_mask = np.zeros(pred.shape, dtype=bool)
        residual_mask[rows, cols] = True
        
        best_obj = None
        best_score = 0
        best_relation = None
        
        for obj_id, obj in graph.objects.items():
            # Check 1: Is residual INTERIOR to this object's bounding box?
            r1, c1, r2, c2 = obj.bbox
            interior_mask = np.zeros_like(residual_mask)
            interior_mask[r1:r2, c1:c2] = True
            
            overlap = (residual_mask & interior_mask).sum()
            if overlap > 0:
                score = overlap / residual_mask.sum()
                if score > best_score:
                    best_score = score
                    best_obj = (obj_id, obj)
                    best_relation = 'interior_of'
            
            # Check 2: Is residual ENCLOSED by this object?
            # Fill holes in the object mask to find enclosed regions
            filled = binary_fill_holes(obj.mask)
            enclosed = filled & ~obj.mask  # The filled-in holes
            
            enclosed_overlap = (residual_mask & enclosed).sum()
            if enclosed_overlap > 0:
                score = enclosed_overlap / residual_mask.sum()
                if score > best_score:
                    best_score = score
                    best_obj = (obj_id, obj)
                    best_relation = 'enclosed_by'
        
        # Check 3: Is residual BETWEEN two aligned objects?
        aligned_edges = graph.get_edges_by_relation('aligned_x') + \
                       graph.get_edges_by_relation('aligned_y')
        
        for edge in aligned_edges:
            obj_a = graph.objects.get(edge.src_id)
            obj_b = graph.objects.get(edge.dst_id)
            if obj_a and obj_b:
                # Compute the region between the two objects
                cy_a, cx_a = obj_a.centroid
                cy_b, cx_b = obj_b.centroid
                
                between_mask = np.zeros_like(residual_mask)
                n = max(abs(int(cy_b - cy_a)), abs(int(cx_b - cx_a)), 1)
                for i in range(n + 1):
                    t = i / max(n, 1)
                    y = int(cy_a + t * (cy_b - cy_a))
                    x = int(cx_a + t * (cx_b - cx_a))
                    if 0 <= y < pred.shape[0] and 0 <= x < pred.shape[1]:
                        between_mask[y, x] = True
                
                between_overlap = (residual_mask & between_mask).sum()
                if between_overlap > 0:
                    score = between_overlap / residual_mask.sum()
                    if score > best_score:
                        best_score = score
                        best_obj = (edge.src_id, obj_a)
                        best_relation = 'between_aligned'
        
        if best_obj and best_score > 0.5:  # At least 50% overlap
            return (best_obj[0], best_obj[1], best_relation)
        
        return None
    
    def _compile_size_change(self, prediction: ARCGrid, target: ARCGrid,
                            task: ARCTask, laws: List[str]) -> Optional[CanonicalOperator]:
        """Handle size-changing operations like crop/expand."""
        pred_shape = prediction.shape
        target_shape = target.shape
        
        # Crop: target is smaller
        if target_shape[0] <= pred_shape[0] and target_shape[1] <= pred_shape[1]:
            return CanonicalOperator(
                op_type='crop',
                params={'target_shape': target_shape},
                preconditions={},
                postconditions={'size': 'reduced'},
                cost=0.3,
                source='compiled',
                confidence=0.7
            )
        
        # Expand: target is larger
        if target_shape[0] >= pred_shape[0] and target_shape[1] >= pred_shape[1]:
            factor_h = target_shape[0] / pred_shape[0]
            factor_w = target_shape[1] / pred_shape[1]
            return CanonicalOperator(
                op_type='expand',
                params={'factor_h': factor_h, 'factor_w': factor_w},
                preconditions={},
                postconditions={'size': 'increased'},
                cost=0.4,
                source='compiled',
                confidence=0.6
            )
        
        return None
    
    def _verify(self, candidate: CanonicalOperator, task: ARCTask,
                metric: 'AdaptiveFisherRaoMetric' = None) -> bool:
        """
        Verify operator across training examples.
        
        PHASE 34: Operator Promotion Criterion (SGC Theory)
        A local rule becomes a law if:
        1. Sheaf Consistent: reduces or maintains E_sheaf
        2. Symmetry Equivariant: P(T·x) ≈ T·P(x) for preserved symmetries T ∈ S_task
        3. Improves E_data on ALL examples (for relational) or ANY (for standard)
        
        INFORMATION GAIN RELAXATION:
        Accept "partial" operators that improve distance on at least one example
        without degrading others significantly. This transforms the compiler from
        a "Solution Finder" to a "Gradient Finder".
        """
        if len(task.train_examples) < 2:
            return True  # Can't verify with single example
        
        is_relational = candidate.op_type.startswith('relational_')
        
        # PHASE 34: Check symmetry equivariance (only for relational operators)
        if is_relational:
            preserved_symmetries = self._detect_preserved_symmetries(task)
            if preserved_symmetries and not self._check_equivariance(candidate, task, preserved_symmetries):
                return False
        
        improvement_count = 0
        degradation_count = 0
        neutral_count = 0
        
        for example in task.train_examples:
            inp = example.input_grid
            expected = example.output_grid
            
            # Apply operator
            result = self._apply_operator(inp, candidate)
            if result is None:
                neutral_count += 1
                continue
            
            result_data = result.data.numpy() if isinstance(result.data, torch.Tensor) else result.data
            expected_data = expected.data.numpy() if isinstance(expected.data, torch.Tensor) else expected.data
            inp_data = inp.data.numpy() if isinstance(inp.data, torch.Tensor) else inp.data
            
            # Handle shape mismatches by computing normalized distance
            if result.shape == expected.shape:
                # Perfect match
                if np.array_equal(result_data, expected_data):
                    improvement_count += 1
                    continue
                
                # Compute distances
                result_errors = (result_data != expected_data).sum()
                result_distance = result_errors / expected_data.size
                
                # Compare to baseline (input vs expected)
                if inp.shape == expected.shape:
                    inp_errors = (inp_data != expected_data).sum()
                    inp_distance = inp_errors / expected_data.size
                    
                    # INFORMATION GAIN: result is better than input
                    if result_distance < inp_distance - 0.01:  # At least 1% improvement
                        improvement_count += 1
                    elif result_distance > inp_distance + 0.05:  # More than 5% degradation
                        degradation_count += 1
                    else:
                        neutral_count += 1
                else:
                    # Input shape differs - use absolute distance
                    if result_distance < 0.5:  # Less than 50% error
                        improvement_count += 1
                    else:
                        neutral_count += 1
            else:
                # Result shape doesn't match expected - count as neutral
                neutral_count += 1
        
        # RELAXED VERIFICATION:
        # - Relational: must improve ALL examples
        # - Standard: must improve at least 1 example without significant degradation
        if is_relational:
            return improvement_count == len(task.train_examples)
        
        # Accept if: at least 1 improvement AND no more than 1 degradation
        return improvement_count >= 1 and degradation_count <= 1
    
    def _detect_preserved_symmetries(self, task: ARCTask) -> List[str]:
        """
        Detect which D4 symmetries are preserved by the task.
        
        PHASE 34: A symmetry T is preserved if input→output respects it:
        ∀ examples: T(output) corresponds to T(input) under the same rule.
        """
        preserved = []
        symmetries = ['rot90', 'rot180', 'rot270', 'flip_h', 'flip_v']
        
        for sym in symmetries:
            is_preserved = True
            for example in task.train_examples:
                inp_data = example.input_grid.data.numpy() if isinstance(example.input_grid.data, torch.Tensor) else example.input_grid.data
                out_data = example.output_grid.data.numpy() if isinstance(example.output_grid.data, torch.Tensor) else example.output_grid.data
                
                # Apply symmetry to both
                try:
                    if sym == 'rot90':
                        T_inp = np.rot90(inp_data, 1)
                        T_out = np.rot90(out_data, 1)
                    elif sym == 'rot180':
                        T_inp = np.rot90(inp_data, 2)
                        T_out = np.rot90(out_data, 2)
                    elif sym == 'rot270':
                        T_inp = np.rot90(inp_data, 3)
                        T_out = np.rot90(out_data, 3)
                    elif sym == 'flip_h':
                        T_inp = np.fliplr(inp_data)
                        T_out = np.fliplr(out_data)
                    elif sym == 'flip_v':
                        T_inp = np.flipud(inp_data)
                        T_out = np.flipud(out_data)
                    else:
                        continue
                    
                    # Check if T(output) has same shape as output
                    # (Symmetry-preserved means shape is compatible)
                    if T_out.shape != out_data.shape:
                        is_preserved = False
                        break
                        
                except Exception:
                    is_preserved = False
                    break
            
            if is_preserved:
                preserved.append(sym)
        
        return preserved
    
    def _check_equivariance(self, op: CanonicalOperator, task: ARCTask, 
                            symmetries: List[str], epsilon: float = 0.1) -> bool:
        """
        Check if operator P is equivariant under preserved symmetries.
        
        PHASE 34 (SGC Theory):
        P is equivariant w.r.t. T if: ||P(T·x) - T·P(x)|| < ε
        
        This ensures the operator respects the task's inherent structure.
        """
        for sym in symmetries:
            for example in task.train_examples[:1]:  # Check first example for efficiency
                inp = example.input_grid
                inp_data = inp.data.numpy() if isinstance(inp.data, torch.Tensor) else inp.data
                
                try:
                    # Compute P(x)
                    Px = self._apply_operator(inp, op)
                    if Px is None:
                        continue
                    Px_data = Px.data.numpy() if isinstance(Px.data, torch.Tensor) else Px.data
                    
                    # Compute T(x)
                    if sym == 'rot90':
                        Tx_data = np.rot90(inp_data, 1)
                    elif sym == 'rot180':
                        Tx_data = np.rot90(inp_data, 2)
                    elif sym == 'rot270':
                        Tx_data = np.rot90(inp_data, 3)
                    elif sym == 'flip_h':
                        Tx_data = np.fliplr(inp_data)
                    elif sym == 'flip_v':
                        Tx_data = np.flipud(inp_data)
                    else:
                        continue
                    
                    Tx = ARCGrid(torch.tensor(Tx_data.copy(), dtype=torch.long))
                    
                    # Compute P(T·x)
                    PTx = self._apply_operator(Tx, op)
                    if PTx is None:
                        continue
                    PTx_data = PTx.data.numpy() if isinstance(PTx.data, torch.Tensor) else PTx.data
                    
                    # Compute T·P(x)
                    if sym == 'rot90':
                        TPx_data = np.rot90(Px_data, 1)
                    elif sym == 'rot180':
                        TPx_data = np.rot90(Px_data, 2)
                    elif sym == 'rot270':
                        TPx_data = np.rot90(Px_data, 3)
                    elif sym == 'flip_h':
                        TPx_data = np.fliplr(Px_data)
                    elif sym == 'flip_v':
                        TPx_data = np.flipud(Px_data)
                    else:
                        continue
                    
                    # Check ||P(T·x) - T·P(x)|| < ε
                    if PTx_data.shape != TPx_data.shape:
                        return False  # Shape mismatch = not equivariant
                    
                    diff = np.sum(PTx_data != TPx_data) / max(PTx_data.size, 1)
                    if diff > epsilon:
                        return False  # Too much disagreement
                        
                except Exception:
                    continue
        
        return True  # Passed all equivariance checks
    
    def _apply_operator(self, grid: ARCGrid, op: CanonicalOperator) -> Optional[ARCGrid]:
        """Apply an operator to a grid."""
        data = grid.data.numpy() if isinstance(grid.data, torch.Tensor) else grid.data
        
        try:
            if op.op_type == 'translate':
                dy, dx = op.params.get('dy', 0), op.params.get('dx', 0)
                result = np.roll(np.roll(data, int(dy), axis=0), int(dx), axis=1)
                return ARCGrid(torch.tensor(result, dtype=torch.long))
            
            elif op.op_type == 'color_map':
                result = data.copy()
                for from_c, to_c in op.params.get('mapping', {}).items():
                    result[data == from_c] = to_c
                return ARCGrid(torch.tensor(result, dtype=torch.long))
            
            elif op.op_type == 'rotate90':
                return ARCGrid(torch.tensor(np.rot90(data, 1).copy(), dtype=torch.long))
            
            elif op.op_type == 'rotate180':
                return ARCGrid(torch.tensor(np.rot90(data, 2).copy(), dtype=torch.long))
            
            elif op.op_type == 'rotate270':
                return ARCGrid(torch.tensor(np.rot90(data, 3).copy(), dtype=torch.long))
            
            elif op.op_type == 'flip_h':
                return ARCGrid(torch.tensor(np.fliplr(data).copy(), dtype=torch.long))
            
            elif op.op_type == 'flip_v':
                return ARCGrid(torch.tensor(np.flipud(data).copy(), dtype=torch.long))
            
            elif op.op_type == 'transpose':
                return ARCGrid(torch.tensor(data.T.copy(), dtype=torch.long))
            
            elif op.op_type == 'identity':
                return grid
            
            # PHASE 33: Relational Predicate Operators
            elif op.op_type == 'relational_paint':
                result = data.copy()
                paint_color = op.params.get('paint_color', 1)
                predicate_type = op.params.get('predicate_type', 'interior_of')
                predicate_args = op.params.get('predicate_args', {})
                
                # Build SceneGraph for current grid
                graph = SceneGraphBuilder().build(grid)
                
                # Compute mask from predicate
                mask = self._evaluate_predicate(data, graph, predicate_type, predicate_args)
                if mask is not None and mask.any():
                    result[mask] = paint_color
                return ARCGrid(torch.tensor(result, dtype=torch.long))
            
            elif op.op_type == 'relational_recolor':
                result = data.copy()
                from_color = op.params.get('from_color', 0)
                to_color = op.params.get('to_color', 1)
                predicate_type = op.params.get('predicate_type', 'interior_of')
                predicate_args = op.params.get('predicate_args', {})
                
                # Build SceneGraph for current grid
                graph = SceneGraphBuilder().build(grid)
                
                # Compute mask from predicate
                mask = self._evaluate_predicate(data, graph, predicate_type, predicate_args)
                if mask is not None and mask.any():
                    recolor_mask = mask & (data == from_color)
                    result[recolor_mask] = to_color
                return ARCGrid(torch.tensor(result, dtype=torch.long))
            
            # PARTIAL OPERATOR: Guarded recolor (selective color change)
            elif op.op_type == 'guarded_recolor':
                result = data.copy()
                from_color = op.params.get('from_color', 0)
                to_color = op.params.get('to_color', 1)
                
                # Apply selective recolor: only change from_color to to_color
                # This is a partial operator - it changes specific color transitions
                result[data == from_color] = to_color
                return ARCGrid(torch.tensor(result, dtype=torch.long))
            
        except Exception:
            return None
        
        return None
    
    def _evaluate_predicate(self, data: np.ndarray, graph: SceneGraph,
                            predicate_type: str, predicate_args: Dict) -> Optional[np.ndarray]:
        """Evaluate a relational predicate to produce a mask."""
        from scipy.ndimage import binary_fill_holes
        
        target_color = predicate_args.get('color', None)
        mask = np.zeros(data.shape, dtype=bool)
        
        if predicate_type == 'interior_of':
            for obj_id, obj in graph.objects.items():
                if target_color is None or obj.color == target_color:
                    r1, c1, r2, c2 = obj.bbox
                    mask[r1:r2, c1:c2] = True
            return mask
        
        elif predicate_type == 'enclosed_by':
            for obj_id, obj in graph.objects.items():
                if target_color is None or obj.color == target_color:
                    filled = binary_fill_holes(obj.mask)
                    enclosed = filled & ~obj.mask
                    mask |= enclosed
            return mask
        
        elif predicate_type == 'between_aligned':
            for edge in graph.get_edges_by_relation('aligned_x') + graph.get_edges_by_relation('aligned_y'):
                obj_a = graph.objects.get(edge.src_id)
                obj_b = graph.objects.get(edge.dst_id)
                if obj_a and obj_b:
                    if target_color is None or obj_a.color == target_color or obj_b.color == target_color:
                        cy_a, cx_a = obj_a.centroid
                        cy_b, cx_b = obj_b.centroid
                        n = max(abs(int(cy_b - cy_a)), abs(int(cx_b - cx_a)), 1)
                        for i in range(n + 1):
                            t = i / max(n, 1)
                            y = int(cy_a + t * (cy_b - cy_a))
                            x = int(cx_a + t * (cx_b - cx_a))
                            if 0 <= y < data.shape[0] and 0 <= x < data.shape[1]:
                                mask[y, x] = True
            return mask
        
        return None
    
    def get_stats(self) -> Dict:
        verified = sum(1 for log in self.compilation_log if log.get('verified', False))
        by_family = Counter(log['family'] for log in self.compilation_log)
        return {
            'total_attempts': len(self.compilation_log),
            'verified': verified,
            'by_family': dict(by_family)
        }


# =============================================================================
# PHASE 30: SPECTRAL LOGIC ENGINE (System 3 - Deep Reasoning via Sheaf Theory)
# =============================================================================

@dataclass
class SheafStalk:
    """
    A Stalk in the Sheaf structure - local data at a point/object.
    
    PHASE 34 (Theory Alignment):
    Stalk basis v_i = [color, area, cx, cy, h, w] ∈ R^6
    
    This fixed basis allows restriction maps R_ij to be linear operators
    that enforce consistency constraints between adjacent stalks.
    """
    obj_id: int
    features: Dict[str, Any]  # color, area, cx, cy, h, w
    neighbors: List[int]  # Connected objects (local topology)
    
    # Stalk dimension indices (for restriction map construction)
    DIM_COLOR = 0
    DIM_AREA = 1
    DIM_CX = 2
    DIM_CY = 3
    DIM_H = 4
    DIM_W = 5
    STALK_DIM = 6
    
    def to_vector(self) -> np.ndarray:
        """
        Convert stalk features to R^6 vector.
        
        Basis: [color, area, cx, cy, h, w]
        Normalization: area/100, cx/30, cy/30, h/30, w/30 for numerical stability.
        """
        return np.array([
            self.features.get('color', 0),
            self.features.get('area', 0) / 100.0,
            self.features.get('centroid_x', 0) / 30.0,
            self.features.get('centroid_y', 0) / 30.0,
            self.features.get('height', 0) / 30.0,
            self.features.get('width', 0) / 30.0,
        ], dtype=np.float32)


class SheafStructure:
    """
    A Cellular Sheaf on the Scene Graph.
    
    PHASE 34 (Theory Alignment):
    - Base Space X: The Scene Graph (nodes = objects, edges = relations)
    - Stalks F_x: Feature vectors v_i ∈ R^6 at each node
    - Restriction Maps R_ij: Linear maps enforcing edge constraints
    
    The Sheaf Energy is E_sheaf = Σ_{(i,j)} ||R_ij v_i - v_j||²
    A Global Section is a section σ with E_sheaf(σ) = 0.
    """
    
    # Restriction map types
    RESTRICTION_SAME_COLOR = 'same_color'
    RESTRICTION_ALIGNED_X = 'aligned_x'
    RESTRICTION_ALIGNED_Y = 'aligned_y'
    RESTRICTION_SAME_SHAPE = 'same_shape'
    RESTRICTION_ADJACENT = 'adjacent'
    
    def __init__(self):
        self.stalks: Dict[int, SheafStalk] = {}
        self.edges: List[Tuple[int, int, str]] = []  # (i, j, relation_type)
        self.adjacency: Dict[int, List[int]] = {}
    
    def build_from_scene_graph(self, graph: SceneGraph):
        """Construct Sheaf structure from Scene Graph with typed edges."""
        self.stalks.clear()
        self.edges.clear()
        self.adjacency.clear()
        
        # Build stalks (one per object)
        for obj_id, obj in graph.objects.items():
            neighbors = [n_id for n_id, _ in graph.get_neighbors(obj_id)]
            
            stalk = SheafStalk(
                obj_id=obj_id,
                features={
                    'color': obj.color,
                    'area': obj.area,
                    'centroid_x': obj.centroid[1],
                    'centroid_y': obj.centroid[0],
                    'width': obj.width,
                    'height': obj.height
                },
                neighbors=neighbors
            )
            self.stalks[obj_id] = stalk
            self.adjacency[obj_id] = neighbors
        
        # Build typed edges from scene graph relations
        seen_edges = set()
        for edge in graph.edges:
            edge_key = (min(edge.src_id, edge.dst_id), max(edge.src_id, edge.dst_id))
            if edge_key in seen_edges:
                continue
            seen_edges.add(edge_key)
            
            # Map scene graph relation to restriction type
            rel_type = self._map_relation_to_restriction(edge.relation)
            if rel_type:
                self.edges.append((edge.src_id, edge.dst_id, rel_type))
    
    def _map_relation_to_restriction(self, relation: str) -> Optional[str]:
        """Map scene graph relation names to restriction types."""
        mapping = {
            'aligned_x': self.RESTRICTION_ALIGNED_X,
            'aligned_y': self.RESTRICTION_ALIGNED_Y,
            'same_color': self.RESTRICTION_SAME_COLOR,
            'same_shape': self.RESTRICTION_SAME_SHAPE,
            'adjacent': self.RESTRICTION_ADJACENT,
            'contains': self.RESTRICTION_ADJACENT,  # Treat contains as adjacent
            'left_of': self.RESTRICTION_ALIGNED_Y,  # Same row
            'right_of': self.RESTRICTION_ALIGNED_Y,
            'above': self.RESTRICTION_ALIGNED_X,  # Same column
            'below': self.RESTRICTION_ALIGNED_X,
        }
        return mapping.get(relation)
    
    def apply_restriction_diff(self, rel_type: str, v_i: np.ndarray, 
                                v_j: np.ndarray) -> np.ndarray:
        """
        Apply restriction map R_ij and compute residual R_ij(v_i) - v_j.
        
        PHASE 34: Implements the restriction library from SGC theory.
        Each restriction type projects onto the dimensions that must agree.
        
        Returns: The difference vector (residual) in the constrained subspace.
        """
        if rel_type == self.RESTRICTION_SAME_COLOR:
            # Constraint: v_i.color = v_j.color
            # Residual: scalar difference on color dimension
            return np.array([v_i[SheafStalk.DIM_COLOR] - v_j[SheafStalk.DIM_COLOR]])
        
        elif rel_type == self.RESTRICTION_ALIGNED_X:
            # Constraint: v_i.cx = v_j.cx (same column)
            return np.array([v_i[SheafStalk.DIM_CX] - v_j[SheafStalk.DIM_CX]])
        
        elif rel_type == self.RESTRICTION_ALIGNED_Y:
            # Constraint: v_i.cy = v_j.cy (same row)
            return np.array([v_i[SheafStalk.DIM_CY] - v_j[SheafStalk.DIM_CY]])
        
        elif rel_type == self.RESTRICTION_SAME_SHAPE:
            # Constraint: area, h, w must match
            return np.array([
                v_i[SheafStalk.DIM_AREA] - v_j[SheafStalk.DIM_AREA],
                v_i[SheafStalk.DIM_H] - v_j[SheafStalk.DIM_H],
                v_i[SheafStalk.DIM_W] - v_j[SheafStalk.DIM_W],
            ])
        
        elif rel_type == self.RESTRICTION_ADJACENT:
            # Adjacent: no strict feature constraint (topological only)
            # Return zero residual - adjacency doesn't constrain features
            return np.array([0.0])
        
        # Unknown relation: no constraint
        return np.array([0.0])
    
    def compute_sheaf_energy(self) -> float:
        """
        Compute the Sheaf Consistency Energy.
        
        PHASE 34 (Theory):
        E_sheaf(σ) = Σ_{(i,j,τ)} ||R_ij(v_i) - v_j||²
        
        This measures how well the current section satisfies local constraints.
        A perfect global section has E_sheaf = 0.
        """
        energy = 0.0
        
        for i, j, rel_type in self.edges:
            if i not in self.stalks or j not in self.stalks:
                continue
            
            v_i = self.stalks[i].to_vector()
            v_j = self.stalks[j].to_vector()
            
            # Compute restriction residual
            diff = self.apply_restriction_diff(rel_type, v_i, v_j)
            energy += np.sum(diff ** 2)
        
        return energy
    
    def compute_laplacian(self) -> np.ndarray:
        """
        Compute the Sheaf Laplacian matrix (deprecated - use compute_sheaf_energy).
        
        Kept for backward compatibility with spectral analysis.
        """
        n = len(self.stalks)
        if n == 0:
            return np.array([[0.0]])
        
        id_to_idx = {obj_id: i for i, obj_id in enumerate(sorted(self.stalks.keys()))}
        
        A = np.zeros((n, n), dtype=np.float32)
        for obj_id, neighbors in self.adjacency.items():
            i = id_to_idx[obj_id]
            for neighbor_id in neighbors:
                if neighbor_id in id_to_idx:
                    j = id_to_idx[neighbor_id]
                    v_i = self.stalks[obj_id].to_vector()
                    v_j = self.stalks[neighbor_id].to_vector()
                    similarity = np.exp(-np.linalg.norm(v_i - v_j))
                    A[i, j] = similarity
                    A[j, i] = similarity
        
        D = np.diag(A.sum(axis=1))
        L = D - A
        return L
    
    def get_feature_matrix(self) -> np.ndarray:
        """Get matrix of stalk feature vectors."""
        if not self.stalks:
            return np.zeros((1, SheafStalk.STALK_DIM))
        
        vectors = []
        for obj_id in sorted(self.stalks.keys()):
            vectors.append(self.stalks[obj_id].to_vector())
        return np.array(vectors)


class SpectralLogicEngine:
    """
    System 3 (Deep) Reasoning via Spectral Analysis of Sheaf Structure.
    
    Theory (SGC): The transformation from Input to Output can be understood
    as a "flow" on the Sheaf manifold. The direction of this flow is encoded
    in the eigenvectors of the Difference Laplacian.
    
    Architecture:
    1. Build Sheaf on Input Scene Graph
    2. Build Sheaf on Output Scene Graph  
    3. Compute the "Difference Sheaf" (what changed?)
    4. Spectral decomposition reveals the "transformation axis"
    5. Induce a rule that acts along this axis
    
    This is the "Harmonics of Geometry" - solving ARC by finding the
    principal modes of transformation.
    """
    
    def __init__(self):
        self.graph_builder = SceneGraphBuilder()
        self.discovered_operators: Dict[str, Dict] = {}  # Hash -> Operator
        self.operator_memory: List[Dict] = []  # Persistent memory
    
    def analyze_transformation(self, task: ARCTask) -> Dict[str, Any]:
        """
        Spectral analysis of input->output transformation.
        
        Returns the "transformation signature" - the principal axis of change.
        """
        if not task.train_examples:
            return {'success': False}
        
        ex = task.train_examples[0]
        
        # Build sheaves
        inp_graph = self.graph_builder.build(ex.input_grid)
        out_graph = self.graph_builder.build(ex.output_grid)
        
        inp_sheaf = SheafStructure()
        out_sheaf = SheafStructure()
        inp_sheaf.build_from_scene_graph(inp_graph)
        out_sheaf.build_from_scene_graph(out_graph)
        
        # Compute Laplacians
        L_in = inp_sheaf.compute_laplacian()
        L_out = out_sheaf.compute_laplacian()
        
        # Spectral decomposition
        try:
            if L_in.shape[0] > 1:
                eigenvalues_in, eigenvectors_in = np.linalg.eigh(L_in)
            else:
                eigenvalues_in, eigenvectors_in = np.array([0.0]), np.array([[1.0]])
            
            if L_out.shape[0] > 1:
                eigenvalues_out, eigenvectors_out = np.linalg.eigh(L_out)
            else:
                eigenvalues_out, eigenvectors_out = np.array([0.0]), np.array([[1.0]])
        except:
            return {'success': False}
        
        # Analyze transformation type
        analysis = {
            'success': True,
            'n_objects_in': len(inp_graph.objects),
            'n_objects_out': len(out_graph.objects),
            'object_delta': len(out_graph.objects) - len(inp_graph.objects),
            'spectral_gap_in': eigenvalues_in[1] - eigenvalues_in[0] if len(eigenvalues_in) > 1 else 0,
            'spectral_gap_out': eigenvalues_out[1] - eigenvalues_out[0] if len(eigenvalues_out) > 1 else 0,
            'transformation_type': self._classify_transformation(
                inp_graph, out_graph, eigenvalues_in, eigenvalues_out
            )
        }
        
        # Induce operator from spectral signature
        operator = self._induce_spectral_operator(
            inp_sheaf, out_sheaf, ex.input_grid, ex.output_grid, analysis
        )
        if operator:
            analysis['induced_operator'] = operator
            self._register_operator(operator)
        
        return analysis
    
    def _classify_transformation(self, inp_graph: SceneGraph, out_graph: SceneGraph,
                                  eig_in: np.ndarray, eig_out: np.ndarray) -> str:
        """Classify the transformation type from spectral properties."""
        n_in = len(inp_graph.objects)
        n_out = len(out_graph.objects)
        
        # Object count change
        if n_out > n_in:
            return 'expansion'  # Objects were added
        elif n_out < n_in:
            return 'contraction'  # Objects were removed
        
        # Check color changes
        colors_in = set(o.color for o in inp_graph.objects.values())
        colors_out = set(o.color for o in out_graph.objects.values())
        if colors_in != colors_out:
            return 'recolor'
        
        # Check for structural change (spectral gap)
        gap_in = eig_in[1] - eig_in[0] if len(eig_in) > 1 else 0
        gap_out = eig_out[1] - eig_out[0] if len(eig_out) > 1 else 0
        if abs(gap_out - gap_in) > 0.5:
            return 'restructure'  # Connectivity changed
        
        return 'preserve'  # Structure mostly preserved
    
    def _induce_spectral_operator(self, inp_sheaf: SheafStructure, 
                                   out_sheaf: SheafStructure,
                                   inp_grid: ARCGrid, out_grid: ARCGrid,
                                   analysis: Dict) -> Optional[Dict]:
        """
        Induce an operator from the spectral analysis.
        
        This is the "Rule Discovery" engine - finding new priors.
        """
        transform_type = analysis.get('transformation_type', 'unknown')
        
        inp_data = inp_grid.data.numpy() if isinstance(inp_grid.data, torch.Tensor) else inp_grid.data
        out_data = out_grid.data.numpy() if isinstance(out_grid.data, torch.Tensor) else out_grid.data
        
        operator = {
            'type': transform_type,
            'hash': None,
            'apply': None,
            'confidence': 0.0
        }
        
        if transform_type == 'expansion':
            # Analyze what was added
            diff = (out_data != 0).astype(int) - (inp_data != 0).astype(int) if inp_data.shape == out_data.shape else None
            if diff is not None:
                added_pixels = (diff > 0).sum()
                if added_pixels > 0:
                    operator['action'] = 'add_structure'
                    operator['added_count'] = int(added_pixels)
                    operator['hash'] = f"expand_{added_pixels}"
                    operator['confidence'] = 0.6
        
        elif transform_type == 'recolor':
            # Find color mapping
            if inp_data.shape == out_data.shape:
                color_map = {}
                for c in np.unique(inp_data):
                    if c == 0:
                        continue
                    mask = (inp_data == c)
                    out_colors = out_data[mask]
                    if len(out_colors) > 0:
                        new_c = int(np.median(out_colors))
                        if new_c != c:
                            color_map[int(c)] = new_c
                if color_map:
                    operator['action'] = 'color_map'
                    operator['mapping'] = color_map
                    operator['hash'] = f"recolor_{hash(tuple(sorted(color_map.items())))}"
                    operator['confidence'] = 0.8
        
        elif transform_type == 'restructure':
            # Connectivity changed - analyze the Laplacian difference
            operator['action'] = 'connect_or_split'
            operator['hash'] = f"restructure_{analysis['object_delta']}"
            operator['confidence'] = 0.5
        
        elif transform_type == 'preserve':
            # Structure preserved - look for movement/rotation
            if inp_data.shape == out_data.shape:
                # Check for shift
                for dy in range(-3, 4):
                    for dx in range(-3, 4):
                        if dy == 0 and dx == 0:
                            continue
                        shifted = np.roll(np.roll(inp_data, dy, axis=0), dx, axis=1)
                        if np.array_equal(shifted, out_data):
                            operator['action'] = 'shift'
                            operator['delta'] = (dy, dx)
                            operator['hash'] = f"shift_{dy}_{dx}"
                            operator['confidence'] = 1.0
                            break
                    if operator.get('confidence', 0) > 0:
                        break
        
        if operator.get('hash'):
            return operator
        return None
    
    def _register_operator(self, operator: Dict):
        """Register a discovered operator in memory."""
        op_hash = operator.get('hash')
        if op_hash and op_hash not in self.discovered_operators:
            self.discovered_operators[op_hash] = operator
            self.operator_memory.append({
                'hash': op_hash,
                'type': operator.get('type'),
                'action': operator.get('action'),
                'confidence': operator.get('confidence', 0)
            })
    
    def apply_discovered_operators(self, grid: ARCGrid, target: ARCGrid) -> Optional[ARCGrid]:
        """
        Apply discovered operators to try to reach the target.
        
        This is the "Tool Use" phase - composing learned priors.
        """
        data = grid.data.numpy() if isinstance(grid.data, torch.Tensor) else grid.data.copy()
        target_data = target.data.numpy() if isinstance(target.data, torch.Tensor) else target.data
        
        best_result = None
        best_distance = float('inf')
        
        for op_hash, operator in self.discovered_operators.items():
            action = operator.get('action')
            result = None
            
            if action == 'shift':
                dy, dx = operator.get('delta', (0, 0))
                result = np.roll(np.roll(data, dy, axis=0), dx, axis=1)
            
            elif action == 'color_map':
                result = data.copy()
                mapping = operator.get('mapping', {})
                for from_c, to_c in mapping.items():
                    result[data == from_c] = to_c
            
            if result is not None and result.shape == target_data.shape:
                distance = (result != target_data).sum()
                if distance < best_distance:
                    best_distance = distance
                    best_result = result
        
        if best_result is not None and best_distance < (data != target_data).sum():
            return ARCGrid(torch.tensor(best_result, dtype=torch.long))
        return None
    
    def get_operator_memory(self) -> List[Dict]:
        """Return the discovered operators (the Toolbox)."""
        return self.operator_memory


# =============================================================================
# PHASE 31: THE COMPOSITION ENGINE (Frontal Cortex - Executive Function)
# =============================================================================
# Updated to use Canonical Operator IR with A* search and energy-based priors.
# =============================================================================

@dataclass
class CompositionState:
    """A state in the A* search - represents a partial solution."""
    grid: np.ndarray
    path: List[str]  # Sequence of operator hashes applied
    g_cost: float  # Cost so far (sum of operator costs)
    h_cost: float  # Heuristic (Fisher-Rao distance to target)
    _id: int = field(default_factory=lambda: id(object()))  # Unique ID for tiebreaking
    
    @property
    def f_cost(self) -> float:
        """Total cost for A* ordering."""
        return self.g_cost + self.h_cost
    
    def __lt__(self, other):
        # Primary: f_cost, Secondary: unique ID (avoids array comparison)
        if self.f_cost != other.f_cost:
            return self.f_cost < other.f_cost
        return self._id < other._id
    
    def __eq__(self, other):
        return self._id == other._id
    
    def __hash__(self):
        return self._id
    
    def __le__(self, other):
        return self.f_cost < other.f_cost


class UnifiedCompositionEngine:
    """
    Phase 31+32: Unified Composition Engine with Canonical Operator IR.
    
    Theory (Category Theory + Thermodynamics):
    - Operators are Morphisms in the category of ARC grids
    - Solutions are Compositions: h o g o f
    - A* search finds optimal path through morphism space
    - Energy-based priors guide search toward promising operators
    
    Key Improvements over basic beam search:
    1. Uses CanonicalOperator IR for all operators
    2. A* search with memoization over grid signatures
    3. Thermodynamic prior: operators sorted by energy (success history)
    4. Content-addressed caching prevents revisiting states
    
    This implements "think fast unless forced to think slow":
    - Fast path: hot operators + gated legality
    - Slow path: A* expansion when metric plateau persists
    """
    
    def __init__(self, metric: 'AdaptiveFisherRaoMetric', 
                 memory: ContentAddressedOperatorMemory,
                 beam_width: int = 5, max_depth: int = 4):
        self.metric = metric
        self.memory = memory
        self.beam_width = beam_width
        self.max_depth = max_depth
        self.stats = {'attempts': 0, 'successes': 0, 'compositions_found': 0,
                     'cache_hits': 0, 'states_explored': 0}
    
    def compose(self, start_grid: ARCGrid, target: ARCGrid,
                laws: List[str] = None) -> Optional[Tuple[ARCGrid, List[str]]]:
        """
        A* search over operator compositions.
        
        Uses:
        - Fisher-Rao distance as heuristic (h)
        - Operator cost as path cost (g)
        - Energy-based operator ordering
        - Memoization over grid signatures
        - FIX 9: Sheaf-consistency energy penalty for invariant violations
        
        Returns (result_grid, operator_path) or None if no composition found.
        """
        self.stats['attempts'] += 1
        laws = laws or []
        
        # FIX 9: Extract invariants from laws for sheaf-consistency check
        # These are the "restrictions" that a valid section must respect
        self._current_laws = set(laws)
        
        start_data = start_grid.data.numpy() if isinstance(start_grid.data, torch.Tensor) else start_grid.data
        target_data = target.data.numpy() if isinstance(target.data, torch.Tensor) else target.data
        
        # Check if shapes match
        if start_data.shape != target_data.shape:
            return None
        
        # Initial state
        initial_dist = self.metric.compute(start_grid, target)
        initial_state = CompositionState(
            grid=start_data.copy(),
            path=[],
            g_cost=0.0,
            h_cost=initial_dist['total']
        )
        
        # Already perfect?
        if initial_state.h_cost == 0:
            return (start_grid, [])
        
        # PHASE 35: Get base operators (non-templates) once
        # Templates get instantiated per-node with state/target context
        base_operators = [op for op in self.memory.get_all() 
                         if not op.preconditions.get('template', False)]
        
        if not base_operators and not any(op.preconditions.get('template', False) 
                                           for op in self.memory.get_all()):
            return None
        
        # A* search with beam pruning
        import heapq
        open_set = [initial_state]
        heapq.heapify(open_set)
        best_seen = initial_state
        visited_hashes = {self._grid_hash(start_data): 0.0}  # hash -> best g_cost
        
        while open_set and len(visited_hashes) < 1000:  # Increased limit for deeper search
            # Pop lowest f-cost state
            current = heapq.heappop(open_set)
            self.stats['states_explored'] += 1
            
            # Depth limit
            if len(current.path) >= self.max_depth:
                continue
            
            # PHASE 35: Get operators WITH template instantiation for this state
            # Templates → instantiate(template, current.grid, target) → concrete ops
            operators = self.memory.get_compatible(
                laws, state=current.grid, target=target_data, top_k_bindings=3
            )
            operators.sort(key=lambda op: op.energy())
            
            # Try each operator (ordered by energy = thermodynamic prior)
            for op in operators:
                op_hash = op.content_hash()
                
                # Skip if already in path (avoid cycles)
                if op_hash in current.path:
                    continue
                
                # Apply operator
                new_grid = self._apply_canonical_operator(current.grid, op)
                if new_grid is None:
                    continue
                
                # Check if already visited with better cost
                grid_hash = self._grid_hash(new_grid)
                new_g_cost = current.g_cost + op.cost
                
                if grid_hash in visited_hashes:
                    if visited_hashes[grid_hash] <= new_g_cost:
                        self.stats['cache_hits'] += 1
                        continue
                
                visited_hashes[grid_hash] = new_g_cost
                
                # Compute new heuristic
                # FIX 7: Allow shape-changing operators if they produce target shape
                # Object-level ops like extract_largest, crop_to_content change shape
                if new_grid.shape != target_data.shape:
                    # Skip if shapes don't match AND we're not at depth 0
                    # Allow first-level shape changes to reach target
                    if len(current.path) > 0:
                        continue
                    # At depth 0, skip only if no possible further composition could help
                    continue
                
                new_arc_grid = ARCGrid(torch.tensor(new_grid, dtype=torch.long))
                new_dist = self.metric.compute(new_arc_grid, target)
                
                # FIX 2: Scale h_cost to balance against g_cost
                # Theory: h(n) must be comparable to g(n) for A* to work
                # If op.cost ~ 0.1 and h ~ 0.1-1.0, scale h by 5 for proper balance
                scaled_h = new_dist['total'] * 5.0
                
                # FIX 9: Add sheaf-consistency penalty for invariant violations
                # Operators that break discovered restrictions get penalized
                consistency_penalty = self._compute_consistency_penalty(
                    current.grid, new_grid, op, target_data
                )
                scaled_h += consistency_penalty
                
                new_state = CompositionState(
                    grid=new_grid,
                    path=current.path + [op_hash],
                    g_cost=new_g_cost,
                    h_cost=scaled_h
                )
                
                # Check for perfect solution
                if new_state.h_cost == 0 or np.array_equal(new_grid, target_data):
                    self.stats['successes'] += 1
                    self.stats['compositions_found'] += 1
                    # Update operator success stats
                    for used_hash in new_state.path:
                        self.memory.update_operator(used_hash, True)
                    return (new_arc_grid, new_state.path)
                
                # Track best seen
                if new_state.h_cost < best_seen.h_cost:
                    best_seen = new_state
                
                heapq.heappush(open_set, new_state)
            
            # Beam pruning: keep only top-k in open set
            if len(open_set) > self.beam_width * 2:
                open_set = heapq.nsmallest(self.beam_width, open_set)
                heapq.heapify(open_set)
        
        # Return best found if it's an improvement
        if best_seen.h_cost < initial_state.h_cost:
            result_grid = ARCGrid(torch.tensor(best_seen.grid, dtype=torch.long))
            return (result_grid, best_seen.path)
        
        return None
    
    def _apply_canonical_operator(self, data: np.ndarray, 
                                  op: CanonicalOperator) -> Optional[np.ndarray]:
        """Apply a CanonicalOperator to the grid."""
        try:
            if op.op_type == 'translate':
                dy, dx = op.params.get('dy', 0), op.params.get('dx', 0)
                return np.roll(np.roll(data, int(dy), axis=0), int(dx), axis=1)
            
            elif op.op_type == 'color_map':
                result = data.copy()
                for from_c, to_c in op.params.get('mapping', {}).items():
                    result[data == from_c] = to_c
                return result
            
            elif op.op_type == 'rotate90':
                return np.rot90(data, 1).copy()
            
            elif op.op_type == 'rotate180':
                return np.rot90(data, 2).copy()
            
            elif op.op_type == 'rotate270':
                return np.rot90(data, 3).copy()
            
            elif op.op_type == 'flip_h':
                return np.fliplr(data).copy()
            
            elif op.op_type == 'flip_v':
                return np.flipud(data).copy()
            
            elif op.op_type == 'transpose':
                return data.T.copy()
            
            elif op.op_type == 'identity':
                return data.copy()
            
            # Object-level operators
            elif op.op_type == 'extract_largest':
                # Extract the largest connected component
                labeled, num = ndimage.label(data > 0)
                if num == 0:
                    return data.copy()
                sizes = ndimage.sum(data > 0, labeled, range(1, num + 1))
                largest = np.argmax(sizes) + 1
                mask = labeled == largest
                rows, cols = np.where(mask)
                if len(rows) == 0:
                    return data.copy()
                return data[rows.min():rows.max()+1, cols.min():cols.max()+1].copy()
            
            elif op.op_type == 'extract_smallest':
                labeled, num = ndimage.label(data > 0)
                if num == 0:
                    return data.copy()
                sizes = ndimage.sum(data > 0, labeled, range(1, num + 1))
                smallest = np.argmin(sizes) + 1
                mask = labeled == smallest
                rows, cols = np.where(mask)
                if len(rows) == 0:
                    return data.copy()
                return data[rows.min():rows.max()+1, cols.min():cols.max()+1].copy()
            
            elif op.op_type == 'crop_to_content':
                # Crop to bounding box of non-zero content
                rows, cols = np.where(data > 0)
                if len(rows) == 0:
                    return data.copy()
                return data[rows.min():rows.max()+1, cols.min():cols.max()+1].copy()
            
            elif op.op_type == 'remove_background':
                # Set background (most common color) to 0
                colors, counts = np.unique(data, return_counts=True)
                bg_color = colors[np.argmax(counts)]
                result = data.copy()
                result[data == bg_color] = 0
                return result
            
            elif op.op_type == 'fill_enclosed':
                # Fill holes in objects
                from scipy.ndimage import binary_fill_holes
                mask = data > 0
                filled = binary_fill_holes(mask)
                result = data.copy()
                # Get the most common non-zero color
                nonzero = data[data > 0]
                if len(nonzero) > 0:
                    fill_color = np.bincount(nonzero).argmax()
                    result[filled & ~mask] = fill_color
                return result
            
            elif op.op_type == 'connect_aligned_h':
                # Connect horizontally aligned objects
                result = data.copy()
                for row in range(data.shape[0]):
                    line = data[row, :]
                    nonzero = np.where(line > 0)[0]
                    if len(nonzero) >= 2:
                        fill_color = line[nonzero[0]]
                        result[row, nonzero[0]:nonzero[-1]+1] = fill_color
                return result
            
            elif op.op_type == 'connect_aligned_v':
                # Connect vertically aligned objects
                result = data.copy()
                for col in range(data.shape[1]):
                    line = data[:, col]
                    nonzero = np.where(line > 0)[0]
                    if len(nonzero) >= 2:
                        fill_color = line[nonzero[0]]
                        result[nonzero[0]:nonzero[-1]+1, col] = fill_color
                return result
            
            # FIX 7: Graph grammar operators (scene-graph-aware)
            elif op.op_type == 'graph_connect':
                # Connect objects based on graph relations
                result = data.copy()
                color = op.params.get('color', 1)
                relations = op.params.get('pattern_relations', [])
                
                # Build scene graph for current state
                grid = ARCGrid(torch.tensor(data, dtype=torch.long))
                graph = SceneGraphBuilder().build(grid)
                
                for relation in relations:
                    for edge in graph.get_edges_by_relation(relation):
                        obj_a = graph.objects.get(edge.src_id)
                        obj_b = graph.objects.get(edge.dst_id)
                        if obj_a and obj_b:
                            # Draw line between centroids
                            cy_a, cx_a = int(obj_a.centroid[0]), int(obj_a.centroid[1])
                            cy_b, cx_b = int(obj_b.centroid[0]), int(obj_b.centroid[1])
                            n = max(abs(cy_b - cy_a), abs(cx_b - cx_a), 1)
                            for i in range(n + 1):
                                t = i / max(n, 1)
                                y = int(cy_a + t * (cy_b - cy_a))
                                x = int(cx_a + t * (cx_b - cx_a))
                                if 0 <= y < result.shape[0] and 0 <= x < result.shape[1]:
                                    result[y, x] = color
                return result
            
            elif op.op_type == 'graph_fill':
                # Fill regions between objects based on graph relations
                result = data.copy()
                color = op.params.get('color', 1)
                
                grid = ARCGrid(torch.tensor(data, dtype=torch.long))
                graph = SceneGraphBuilder().build(grid)
                
                for edge in graph.get_edges_by_relation('adjacent'):
                    obj_a = graph.objects.get(edge.src_id)
                    obj_b = graph.objects.get(edge.dst_id)
                    if obj_a and obj_b:
                        r1 = min(obj_a.bbox[0], obj_b.bbox[0])
                        r2 = max(obj_a.bbox[2], obj_b.bbox[2])
                        c1 = min(obj_a.bbox[1], obj_b.bbox[1])
                        c2 = max(obj_a.bbox[3], obj_b.bbox[3])
                        for r in range(r1, r2):
                            for c in range(c1, c2):
                                if 0 <= r < result.shape[0] and 0 <= c < result.shape[1]:
                                    if result[r, c] == 0:
                                        result[r, c] = color
                return result
            
            elif op.op_type == 'graph_recolor':
                # Recolor based on graph relations
                result = data.copy()
                from_c = op.params.get('from_color', 0)
                to_c = op.params.get('to_color', 0)
                result[data == from_c] = to_c
                return result
            
            # FIX 8: Guarded local operators
            elif op.op_type == 'guarded_recolor':
                result = data.copy()
                from_c = op.params.get('from_color', 0)
                to_c = op.params.get('to_color', 0)
                bounds = op.params.get('mask_bounds', None)
                predicate = op.params.get('mask_predicate', 'bounding_box')
                
                if bounds:
                    r_min, c_min, r_max, c_max = bounds
                    # Apply recolor only within bounds
                    region = result[r_min:r_max+1, c_min:c_max+1]
                    region[region == from_c] = to_c
                else:
                    result[data == from_c] = to_c
                return result
            
            elif op.op_type == 'guarded_paint':
                result = data.copy()
                color = op.params.get('color', 1)
                bounds = op.params.get('mask_bounds', None)
                predicate = op.params.get('mask_predicate', 'bounding_box')
                
                if bounds:
                    r_min, c_min, r_max, c_max = bounds
                    # Paint background pixels within bounds
                    for r in range(r_min, min(r_max+1, result.shape[0])):
                        for c in range(c_min, min(c_max+1, result.shape[1])):
                            if result[r, c] == 0:
                                result[r, c] = color
                return result
            
            # PHASE 33: Relational Predicate Operators
            # These compute masks DYNAMICALLY from the current grid's SceneGraph
            elif op.op_type == 'relational_paint':
                result = data.copy()
                paint_color = op.params.get('paint_color', 1)
                predicate_type = op.params.get('predicate_type', 'interior_of')
                predicate_args = op.params.get('predicate_args', {})
                
                # Build SceneGraph for current grid
                grid = ARCGrid(torch.tensor(data, dtype=torch.long))
                graph = SceneGraphBuilder().build(grid)
                
                # Compute mask from predicate
                mask = self._evaluate_relational_predicate(
                    data, graph, predicate_type, predicate_args
                )
                
                if mask is not None and mask.any():
                    result[mask] = paint_color
                return result
            
            elif op.op_type == 'relational_recolor':
                result = data.copy()
                from_color = op.params.get('from_color', 0)
                to_color = op.params.get('to_color', 1)
                predicate_type = op.params.get('predicate_type', 'interior_of')
                predicate_args = op.params.get('predicate_args', {})
                
                # Build SceneGraph for current grid
                grid = ARCGrid(torch.tensor(data, dtype=torch.long))
                graph = SceneGraphBuilder().build(grid)
                
                # Compute mask from predicate
                mask = self._evaluate_relational_predicate(
                    data, graph, predicate_type, predicate_args
                )
                
                if mask is not None and mask.any():
                    # Only recolor pixels that match from_color within the mask
                    recolor_mask = mask & (data == from_color)
                    result[recolor_mask] = to_color
                return result
            
            # PHASE 36: Ad-hoc operators for residual cleanup
            elif op.op_type == 'fix_pixel':
                result = data.copy()
                row = op.params.get('row', 0)
                col = op.params.get('col', 0)
                color = op.params.get('color', 0)
                if 0 <= row < result.shape[0] and 0 <= col < result.shape[1]:
                    result[row, col] = color
                return result
            
            elif op.op_type == 'fix_region':
                result = data.copy()
                bbox = op.params.get('bbox', (0, 0, 0, 0))
                local_mask = op.params.get('local_mask', [[]])
                color = op.params.get('color', 0)
                
                r_min, c_min, r_max, c_max = bbox
                local_mask_arr = np.array(local_mask, dtype=bool)
                
                for i in range(local_mask_arr.shape[0]):
                    for j in range(local_mask_arr.shape[1]):
                        if local_mask_arr[i, j]:
                            r, c = r_min + i, c_min + j
                            if 0 <= r < result.shape[0] and 0 <= c < result.shape[1]:
                                result[r, c] = color
                return result
            
            elif op.op_type == 'fix_color_swap':
                result = data.copy()
                from_color = op.params.get('from_color', 0)
                to_color = op.params.get('to_color', 0)
                result[data == from_color] = to_color
                return result
            
        except Exception:
            return None
        
        return None
    
    def _evaluate_relational_predicate(self, data: np.ndarray, graph: SceneGraph,
                                        predicate_type: str, 
                                        predicate_args: Dict) -> Optional[np.ndarray]:
        """
        PHASE 33: Evaluate a relational predicate on a SceneGraph to produce a mask.
        
        This is the key operation that makes operators work across different grids:
        - The predicate is defined relationally (e.g., "interior of color X")
        - It's evaluated fresh on each grid's SceneGraph
        - The result is a mask of pixels that satisfy the predicate
        """
        from scipy.ndimage import binary_fill_holes
        
        target_color = predicate_args.get('color', None)
        mask = np.zeros(data.shape, dtype=bool)
        
        if predicate_type == 'interior_of':
            # Find objects with matching color, return their interior (bounding box)
            for obj_id, obj in graph.objects.items():
                if target_color is None or obj.color == target_color:
                    r1, c1, r2, c2 = obj.bbox
                    mask[r1:r2, c1:c2] = True
            return mask
        
        elif predicate_type == 'enclosed_by':
            # Find enclosed regions (holes) within objects of matching color
            for obj_id, obj in graph.objects.items():
                if target_color is None or obj.color == target_color:
                    filled = binary_fill_holes(obj.mask)
                    enclosed = filled & ~obj.mask
                    mask |= enclosed
            return mask
        
        elif predicate_type == 'between_aligned':
            # Find pixels between aligned objects
            aligned_edges = graph.get_edges_by_relation('aligned_x') + \
                           graph.get_edges_by_relation('aligned_y')
            
            for edge in aligned_edges:
                obj_a = graph.objects.get(edge.src_id)
                obj_b = graph.objects.get(edge.dst_id)
                if obj_a and obj_b:
                    # Check if either object matches target color
                    if target_color is None or obj_a.color == target_color or obj_b.color == target_color:
                        cy_a, cx_a = obj_a.centroid
                        cy_b, cx_b = obj_b.centroid
                        
                        n = max(abs(int(cy_b - cy_a)), abs(int(cx_b - cx_a)), 1)
                        for i in range(n + 1):
                            t = i / max(n, 1)
                            y = int(cy_a + t * (cy_b - cy_a))
                            x = int(cx_a + t * (cx_b - cx_a))
                            if 0 <= y < data.shape[0] and 0 <= x < data.shape[1]:
                                mask[y, x] = True
            return mask
        
        elif predicate_type == 'adjacent_to':
            # Find pixels adjacent to objects of matching color
            from scipy.ndimage import binary_dilation
            for obj_id, obj in graph.objects.items():
                if target_color is None or obj.color == target_color:
                    dilated = binary_dilation(obj.mask)
                    adjacent = dilated & ~obj.mask
                    mask |= adjacent
            return mask
        
        return None
    
    def _grid_hash(self, grid: np.ndarray) -> int:
        """Create a hash for visited state tracking."""
        return hash(grid.tobytes())
    
    def _compute_consistency_penalty(self, old_grid: np.ndarray, new_grid: np.ndarray,
                                      op: CanonicalOperator, target: np.ndarray) -> float:
        """
        PHASE 34: Compute E_laws penalty (fast path).
        
        Theory (SGC):
        Full energy: E = E_data + λE_sheaf + μE_laws
        
        For A* efficiency, we compute E_laws inline and defer E_sheaf to 
        verification stage (where it's computed once per candidate, not per state).
        """
        laws = getattr(self, '_current_laws', set())
        law_penalty = 0.0
        
        # E_laws: Conservation law violations
        if 'mass' in laws:
            new_mass = (new_grid > 0).sum()
            target_mass = (target > 0).sum()
            old_mass = (old_grid > 0).sum()
            
            old_err = abs(old_mass - target_mass)
            new_err = abs(new_mass - target_mass)
            if new_err > old_err:
                law_penalty += 0.3 * (new_err - old_err) / max(target_mass, 1)
        
        if 'color_palette' in laws:
            target_colors = set(np.unique(target))
            new_colors = set(np.unique(new_grid))
            extra_colors = new_colors - target_colors
            if extra_colors:
                law_penalty += 0.2 * len(extra_colors)
        
        # Shape consistency (implicit in A* by shape filtering)
        if 'shape' in laws and new_grid.shape != target.shape:
            law_penalty += 1.0  # Large penalty for shape mismatch
        
        return law_penalty
    
    def compute_full_energy(self, grid: np.ndarray, target: np.ndarray) -> Tuple[float, float, float]:
        """
        PHASE 34: Compute full energy functional E = E_data + λE_sheaf + μE_laws.
        
        This is the mathematically complete version used for final verification,
        not during A* search (too expensive).
        
        Returns: (E_data, E_sheaf, E_laws)
        """
        # E_data: pixel-level distance
        if grid.shape != target.shape:
            E_data = 1.0
        else:
            E_data = (grid != target).sum() / max(grid.size, 1)
        
        # E_sheaf: sheaf consistency energy
        E_sheaf = 0.0
        try:
            grid_arc = ARCGrid(torch.tensor(grid, dtype=torch.long))
            graph = SceneGraphBuilder().build(grid_arc)
            sheaf = SheafStructure()
            sheaf.build_from_scene_graph(graph)
            E_sheaf = sheaf.compute_sheaf_energy()
        except Exception:
            pass
        
        # E_laws: conservation violations
        laws = getattr(self, '_current_laws', set())
        E_laws = 0.0
        
        if 'mass' in laws:
            grid_mass = (grid > 0).sum()
            target_mass = (target > 0).sum()
            E_laws += abs(grid_mass - target_mass) / max(target_mass, 1)
        
        if 'color_palette' in laws:
            target_colors = set(np.unique(target))
            grid_colors = set(np.unique(grid))
            E_laws += len(grid_colors - target_colors) * 0.2
        
        return E_data, E_sheaf, E_laws
    
    def get_stats(self) -> Dict:
        return self.stats


class UnifiedExecutive:
    """
    Phase 32: The Unified Solver Executive.
    
    Coordinates:
    - ContentAddressedOperatorMemory (the Toolbox)
    - ResidualCompiler (discovers new operators from near-misses)
    - UnifiedCompositionEngine (A* search over operator chains)
    
    This is the "Frontal Cortex" that:
    1. Measures the residual (Fisher-Rao + invariants)
    2. Compiles residuals into new operators
    3. Composes operators via A* search
    4. Updates operator statistics based on outcomes
    
    Theory (Cybernetics + Autopoiesis):
    - TOTE loop: Test-Operate-Test-Exit
    - Self-modifying: discovers and registers new tools
    - Thermodynamic: energy guides search priority
    """
    
    def __init__(self, metric: 'AdaptiveFisherRaoMetric'):
        self.metric = metric
        self.memory = ContentAddressedOperatorMemory()  # Global memory
        self.compiler = ResidualCompiler(self.memory)
        self.composer = UnifiedCompositionEngine(metric, self.memory)
        self.consolidation = ConsolidationEngine(self.memory)  # PHASE 37
        self.execution_log: List[Dict] = []
        self.adhoc_stats = {'total_synthesized': 0, 'total_applied': 0, 'composition_solves': 0}
        self.current_working_memory: Optional[WorkingMemory] = None  # Track for consolidation
    
    def solve_by_composition(self, start_grid: ARCGrid, target: ARCGrid,
                             task: ARCTask, laws: List[str],
                             verbose: bool = False) -> Optional[Tuple[ARCGrid, List[str]]]:
        """
        PHASE 36: Attempt to solve by composing operators with Working Memory.
        
        Architecture:
        1. Create task-specific WorkingMemory (Global + Task-Local)
        2. Try A* composition with global operators
        3. If near-miss, synthesize ad-hoc operators into WorkingMemory
        4. Retry composition with ad-hoc operators (cleanup step)
        
        Theory: Global ops do the heavy lifting (98%), ad-hoc ops do cleanup (2%).
        """
        # PHASE 36: Create task-local WorkingMemory
        working_memory = WorkingMemory(self.memory)
        
        # Update composer to use working memory for this task
        original_memory = self.composer.memory
        self.composer.memory = working_memory
        
        try:
            # FIX 7: Compile graph grammar rules into canonical operators
            try:
                grammar = GraphGrammarEngine()
                graph_ops = grammar.compile_to_canonical_operators(task)
                for op in graph_ops:
                    self.memory.register(op)  # Register to global memory
                if verbose and graph_ops:
                    print(f"  [GRAPH->IR] Registered {len(graph_ops)} graph operators", flush=True)
            except Exception:
                pass
            
            # Step 1: Try composition search with global + template operators
            result = self.composer.compose(start_grid, target, laws)
            
            if result is not None:
                grid, path = result
                if np.array_equal(
                    grid.data.numpy() if isinstance(grid.data, torch.Tensor) else grid.data,
                    target.data.numpy() if isinstance(target.data, torch.Tensor) else target.data
                ):
                    if verbose and path:
                        print(f"  [COMPOSE] {' -> '.join(path)}", flush=True)
                    self.execution_log.append({
                        'success': True, 'path': path, 'path_length': len(path), 'compiled': False
                    })
                    self.adhoc_stats['composition_solves'] += 1
                    return result
            
            # Step 2: Get best result so far for ad-hoc synthesis
            best_result = result[0] if result else start_grid
            best_data = best_result.data.numpy() if isinstance(best_result.data, torch.Tensor) else best_result.data
            target_data = target.data.numpy() if isinstance(target.data, torch.Tensor) else target.data
            
            # Check if near-miss (small residual)
            if best_data.shape == target_data.shape:
                residual_size = (best_data != target_data).sum()
                total_pixels = best_data.size
                residual_ratio = residual_size / max(total_pixels, 1)
                
                # PHASE 36: Synthesize ad-hoc operators for small residuals
                if 0 < residual_ratio < 0.15:  # Near-miss threshold
                    adhoc_ops = self.compiler.synthesize_adhoc_operators(
                        best_data, target_data, working_memory
                    )
                    self.adhoc_stats['total_synthesized'] += len(adhoc_ops)
                    
                    if verbose and adhoc_ops:
                        print(f"  [ADHOC] Synthesized {len(adhoc_ops)} cleanup ops", flush=True)
                    
                    # Step 3: Retry composition with ad-hoc operators
                    if adhoc_ops:
                        result2 = self.composer.compose(best_result, target, laws)
                        
                        if result2 is not None:
                            grid2, path2 = result2
                            grid2_data = grid2.data.numpy() if isinstance(grid2.data, torch.Tensor) else grid2.data
                            if np.array_equal(grid2_data, target_data):
                                full_path = (result[1] if result else []) + path2
                                if verbose:
                                    print(f"  [ADHOC-COMPOSE] {' -> '.join(path2)}", flush=True)
                                self.execution_log.append({
                                    'success': True, 'path': full_path, 
                                    'path_length': len(full_path), 'adhoc': True
                                })
                                self.adhoc_stats['total_applied'] += len(path2)
                                self.adhoc_stats['composition_solves'] += 1
                                return (grid2, full_path)
            
            # Step 4: Fall back to standard residual compilation
            compiled_op = self.compiler.compile(start_grid, target, task, laws)
            
            if compiled_op is not None:
                if verbose:
                    print(f"  [COMPILED] {compiled_op.op_type}: {compiled_op.content_hash()}", flush=True)
                
                # Try applying the compiled operator directly
                applied = self.compiler._apply_operator(start_grid, compiled_op)
                if applied is not None:
                    if applied.shape == target.shape:
                        applied_data = applied.data.numpy() if isinstance(applied.data, torch.Tensor) else applied.data
                        if np.array_equal(applied_data, target_data):
                            self.memory.update_operator(compiled_op.content_hash(), True)
                            self.execution_log.append({
                                'success': True,
                                'path': [compiled_op.content_hash()],
                                'path_length': 1,
                                'compiled': True
                            })
                            return (applied, [compiled_op.content_hash()])
            
            self.execution_log.append({'success': False})
            return None
            
        finally:
            # PHASE 37: Collect successful ad-hoc operators for consolidation
            self.consolidation.collect_from_working_memory(working_memory)
            self.current_working_memory = working_memory  # Keep reference for stats
            
            # PHASE 36: Restore original memory after task completion
            self.composer.memory = original_memory
    
    def dream_cycle(self, verbose: bool = False) -> Dict:
        """
        PHASE 37: Run the consolidation cycle (between tasks/batches).
        
        This is the "Sleep" phase that:
        1. Coarse-grains successful ad-hoc operators into macro-ops
        2. Promotes high-utility macro-ops to Global Memory
        3. Prunes high-energy, low-utility operators
        
        Call this after processing a batch of tasks.
        """
        return self.consolidation.dream_cycle(
            decay_rate=0.02,
            prune_threshold=1.0,
            verbose=verbose
        )
    
    def get_stats(self) -> Dict:
        successes = sum(1 for log in self.execution_log if log.get('success', False))
        compiled = sum(1 for log in self.execution_log if log.get('compiled', False))
        avg_path = np.mean([log['path_length'] for log in self.execution_log 
                           if log.get('success', False) and 'path_length' in log]) if successes > 0 else 0
        return {
            'attempts': len(self.execution_log),
            'successes': successes,
            'compiled_successes': compiled,
            'avg_path_length': float(avg_path),
            'memory_stats': self.memory.get_stats(),
            'compiler_stats': self.compiler.get_stats(),
            'composer_stats': self.composer.get_stats(),
            'consolidation_stats': self.consolidation.get_stats()  # PHASE 37
        }


# Keep old CompositionExecutive for backwards compatibility
class CompositionExecutive:
    """Legacy wrapper - delegates to UnifiedExecutive."""
    
    def __init__(self, metric: 'AdaptiveFisherRaoMetric'):
        self.unified = UnifiedExecutive(metric)
        self.execution_log = self.unified.execution_log
    
    def solve_by_composition(self, start_grid: ARCGrid, target: ARCGrid,
                             toolbox: Dict[str, Dict], 
                             verbose: bool = False) -> Optional[Tuple[ARCGrid, List[str]]]:
        # Create a dummy task for backwards compatibility
        return None  # Will be replaced by direct UnifiedExecutive usage
    
    def get_stats(self) -> Dict:
        return self.unified.get_stats()


# =============================================================================
# CONSERVATION GATING (Hard Gate for Smart Search)
# =============================================================================

class ConservationGate:
    """
    Hard Gating mechanism based on discovered conservation laws.
    
    Theory: If a conservation law holds, operations that violate it should be
    DISABLED before search begins. This turns exhaustive search into smart search.
    
    Gates:
    - Mass Conservation → disable delete, crop (unless preserving), extract
    - Color Conservation → disable recolor, color_map operations
    - Shape Conservation → disable resize, distort operations
    - Symmetry Gates → disable rotations that don't match discovered symmetry
    """
    
    def __init__(self):
        self.gates = {
            'mass': True,      # Allow mass-changing operations
            'color': True,     # Allow color-changing operations
            'shape': True,     # Allow shape-changing operations
            'crop': True,      # Allow cropping
            'extract': True,   # Allow object extraction
            'rotate': True,    # Allow rotations
            'flip': True,      # Allow flips
        }
        self.symmetries = set()  # Discovered symmetries (rot90, rot180, flip_h, etc.)
    
    def configure_from_laws(self, conservation_laws: List[str], symmetries: Dict, 
                             size_changes: bool = False):
        """Configure gates based on discovered conservation laws.
        
        Args:
            conservation_laws: List of discovered conservation laws
            symmetries: Discovered symmetry operations
            size_changes: True if output size differs from input (enables crop/extract)
        """
        # Reset gates
        for key in self.gates:
            self.gates[key] = True
        
        # Apply conservation law constraints
        if 'mass' in conservation_laws and not size_changes:
            # Mass is conserved AND same size → disable crop/extract
            # But if size changes, crop/extract might be the solution!
            self.gates['crop'] = False
            self.gates['extract'] = False
        
        if 'color_palette' in conservation_laws:
            # Color palette is conserved → disable recoloring
            self.gates['color'] = False
        
        if 'shape' in conservation_laws:
            # Shape is conserved → disable resize/distort
            # (Rotations and flips preserve shape, so keep them enabled)
            pass
        
        # Configure symmetry gates
        self.symmetries = set()
        if symmetries:
            # Handle both dict and list formats
            if isinstance(symmetries, dict):
                if symmetries.get('rot90', False):
                    self.symmetries.add('rot90')
                    self.symmetries.add('rot180')
                    self.symmetries.add('rot270')
                if symmetries.get('rot180', False):
                    self.symmetries.add('rot180')
                if symmetries.get('flip_h', False):
                    self.symmetries.add('flip_h')
                if symmetries.get('flip_v', False):
                    self.symmetries.add('flip_v')
            elif isinstance(symmetries, list):
                for sym in symmetries:
                    if 'rot90' in str(sym):
                        self.symmetries.update(['rot90', 'rot180', 'rot270'])
                    elif 'rot180' in str(sym):
                        self.symmetries.add('rot180')
                    elif 'flip_h' in str(sym):
                        self.symmetries.add('flip_h')
                    elif 'flip_v' in str(sym):
                        self.symmetries.add('flip_v')
        
        # If no symmetries discovered, disable rotation searches to save time
        if not self.symmetries:
            self.gates['rotate'] = False
            self.gates['flip'] = False
    
    def is_allowed(self, operation: str) -> bool:
        """Check if an operation is allowed given current gates."""
        op_lower = operation.lower()
        
        # Check crop operations
        if 'crop' in op_lower:
            return self.gates['crop']
        
        # Check extract operations
        if 'extract' in op_lower:
            return self.gates['extract']
        
        # Check color operations
        if 'color' in op_lower or 'recolor' in op_lower or 'swap' in op_lower:
            return self.gates['color']
        
        # Check rotation operations
        if 'rot' in op_lower:
            if not self.gates['rotate']:
                return False
            # If symmetries discovered, only allow matching rotations
            if self.symmetries:
                if 'rot90' in op_lower:
                    return 'rot90' in self.symmetries
                if 'rot180' in op_lower:
                    return 'rot180' in self.symmetries
                if 'rot270' in op_lower:
                    return 'rot270' in self.symmetries
            return True
        
        # Check flip operations
        if 'flip' in op_lower:
            if not self.gates['flip']:
                return False
            if self.symmetries:
                if 'flip_h' in op_lower:
                    return 'flip_h' in self.symmetries
                if 'flip_v' in op_lower:
                    return 'flip_v' in self.symmetries
            return True
        
        # Default: allow
        return True
    
    def get_status(self) -> Dict:
        """Get current gate status."""
        return {
            'gates': self.gates.copy(),
            'symmetries': list(self.symmetries),
            'disabled_ops': [k for k, v in self.gates.items() if not v]
        }


# =============================================================================
# THERMODYNAMIC INJECTION SOLVER (Phase 15 + 19 + 23)
# =============================================================================

class ThermodynamicInjectionSolver:
    """
    The Full Stack Agent: Injects Phase 15/19 "matter" into Phase 23 "physics."
    
    Architecture:
    1. Phase 15 (CEGAR): Generate rich candidates via movement, crop, color, extract
    2. Phase 19 (Fractal): Decompose input/output to discover transformation structure
    3. Phase 23 (Laws): Filter candidates by conservation laws (mass, color, shape)
    4. Phase 22 (Metric): Rank by adaptive Fisher-Rao distance
    5. Phase 22 (MGD): Refine near-misses via manifold gradient descent
    6. Phase 23 (Genes): Induce successful operators into thermodynamic gene pool
    
    This is the "Standard Model of ARC":
    - Gravity (Goal): Fisher-Rao metric pulls toward solution
    - Thermodynamics (Selection): Gene pool selects efficient operators
    - Symmetry (Constraints): Conservation laws filter invalid candidates
    - Matter (Candidates): CEGAR/Fractal generate the particles
    """
    
    def __init__(self):
        self.config = ARCPhase83Config()
        self.metric = AdaptiveFisherRaoMetric()
        self.scientist = ActiveScientist(self.metric)
        self.decomposer = LieAlgebraDecomposer()
        self.mgd = ManifoldGradientDescent(self.metric, self.decomposer)
        self.gate = ConservationGate()  # Hard gating for smart search
        self.grammar = GraphGrammarEngine()  # System 2: Graph Grammar for near-misses
        self.spectral = SpectralLogicEngine()  # System 3: Sheaf/Spectral deep reasoning
        self.executive = UnifiedExecutive(self.metric)  # Phase 32: Unified Executive
        
        # Penta-Cameral Architecture (Phase 32):
        # System 1 (Fast): Conservation-gated candidate generation (Cerebellum)
        # System 2 (Medium): Graph Grammar discrete rules (Prefrontal Cortex)
        # System 3 (Deep): Spectral/Sheaf analysis + operator discovery (Hippocampus)
        # System 4 (Compiler): Residual Compiler - turns near-misses into operators
        # System 5 (Executive): A* Composition Engine with energy-based priors
        self.results: List[Dict] = []
        self.system2_attempts: int = 0
        self.system2_successes: int = 0
        self.system3_attempts: int = 0
        self.system3_discoveries: int = 0
        self.composition_attempts: int = 0
        self.composition_successes: int = 0
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve using thermodynamic injection with Conservation Gating."""
        
        # Step 1: Discover task physics (conservation laws, symmetries)
        analysis = self.scientist.analyze_task(task)
        laws = analysis['conservation_laws']
        symmetries = analysis.get('symmetries', {})
        
        if verbose and laws:
            print(f"  [LAWS] {laws}", flush=True)
        
        # Step 2: Configure Conservation Gate (HARD GATING)
        # Check if output size differs from input (enables crop/extract even with mass conservation)
        size_changes = False
        if task.train_examples:
            inp_shape = task.train_examples[0].input_grid.shape
            out_shape = task.train_examples[0].output_grid.shape
            size_changes = (inp_shape != out_shape)
        
        self.gate.configure_from_laws(laws, symmetries, size_changes)
        if verbose and self.gate.get_status()['disabled_ops']:
            print(f"  [GATE] Disabled: {self.gate.get_status()['disabled_ops']}", flush=True)
        
        # Step 3: Adapt metric to task features
        self.metric.adapt_to_task(task)
        
        # Step 4: Generate GATED candidates (Smart Search, not Exhaustive)
        candidates = self._generate_gated_candidates(task)
        
        if not candidates:
            return self._make_result(task, None, 'no_candidates')
        
        # Step 5: Filter by conservation laws (additional filtering)
        candidates = self.scientist.filter_by_conservation(candidates, task)
        
        # Step 5: Evaluate and rank by Fisher-Rao metric
        evaluated = []
        for method, pred in candidates:
            if task.train_examples:
                target = task.train_examples[0].output_grid
                if pred.shape == target.shape:
                    dist = self.metric.compute(pred, target)
                    evaluated.append((method, pred, dist))
        
        if not evaluated:
            return self._make_result(task, None, 'no_valid_candidates')
        
        evaluated.sort(key=lambda x: x[2]['total'])
        best_method, best_pred, best_dist = evaluated[0]
        
        # Step 6: Check if System 1 got a perfect solution
        is_perfect = False
        if task.train_examples:
            target = task.train_examples[0].output_grid
            if best_pred.shape == target.shape:
                is_perfect = torch.equal(best_pred.data, target.data)
        
        # Step 7: SYSTEM 2 - Graph Grammar ONLY for near-misses (not all failures)
        # This keeps System 2 "slow but focused" rather than "slow and exhaustive"
        if not is_perfect and best_dist['total'] < 0.2 and task.train_examples:
            target = task.train_examples[0].output_grid
            self.system2_attempts += 1
            
            # Try Graph Grammar reasoning
            grammar_result = self.grammar.refine_near_miss(task, best_pred, target)
            if grammar_result is not None:
                if grammar_result.shape == target.shape:
                    grammar_perfect = torch.equal(grammar_result.data, target.data)
                    grammar_dist = self.metric.compute(grammar_result, target)
                    
                    if grammar_perfect or grammar_dist['total'] < best_dist['total']:
                        best_pred = grammar_result
                        best_dist = grammar_dist
                        best_method = f"{best_method}+grammar"
                        is_perfect = grammar_perfect
                        if grammar_perfect:
                            self.system2_successes += 1
                        if verbose:
                            status = "PERFECT" if grammar_perfect else f"F={grammar_dist['total']:.4f}"
                            print(f"  [SYSTEM2] Graph Grammar: {status}", flush=True)
        
        # Step 8: SYSTEM 3 - Spectral Logic for deep analysis and operator discovery
        # This runs on ALL tasks to build the operator memory (autopoietic learning)
        if task.train_examples:
            self.system3_attempts += 1
            spectral_analysis = self.spectral.analyze_transformation(task)
            
            if spectral_analysis.get('induced_operator'):
                self.system3_discoveries += 1
                if verbose:
                    op = spectral_analysis['induced_operator']
                    print(f"  [SYSTEM3] Discovered: {op.get('hash')} (conf={op.get('confidence', 0):.2f})", flush=True)
            
            # Try applying discovered operators if not perfect
            if not is_perfect:
                target = task.train_examples[0].output_grid
                spectral_result = self.spectral.apply_discovered_operators(best_pred, target)
                if spectral_result is not None:
                    spectral_dist = self.metric.compute(spectral_result, target)
                    spectral_perfect = torch.equal(spectral_result.data, target.data) if spectral_result.shape == target.shape else False
                    
                    if spectral_perfect or spectral_dist['total'] < best_dist['total']:
                        best_pred = spectral_result
                        best_dist = spectral_dist
                        best_method = f"{best_method}+spectral"
                        is_perfect = spectral_perfect
                        if verbose:
                            status = "PERFECT" if spectral_perfect else f"F={spectral_dist['total']:.4f}"
                            print(f"  [SYSTEM3] Applied operator: {status}", flush=True)
        
        # Step 9: UNIFIED EXECUTIVE - A* composition + residual compilation
        # This is the Phase 32 "Executive Function" that:
        # - Composes morphisms via A* search: h o g o f
        # - Compiles residuals into new operators
        # - Uses energy-based priors for search guidance
        if not is_perfect and 0 < best_dist['total'] < 0.2 and task.train_examples:
            target = task.train_examples[0].output_grid
            self.composition_attempts += 1
            
            # Use Unified Executive with canonical operator memory
            comp_result = self.executive.solve_by_composition(
                best_pred, target, task, laws, verbose=verbose
            )
            
            if comp_result is not None:
                comp_grid, comp_path = comp_result
                if comp_grid.shape == target.shape:
                    comp_perfect = torch.equal(comp_grid.data, target.data)
                    comp_dist = self.metric.compute(comp_grid, target)
                    
                    if comp_perfect or comp_dist['total'] < best_dist['total']:
                        best_pred = comp_grid
                        best_dist = comp_dist
                        best_method = f"{best_method}+compose({len(comp_path)})"
                        is_perfect = comp_perfect
                        if comp_perfect:
                            self.composition_successes += 1
                        if verbose:
                            status = "PERFECT" if comp_perfect else f"F={comp_dist['total']:.4f}"
                            path_str = ' -> '.join(comp_path) if comp_path else 'identity'
                            print(f"  [COMPOSE] {path_str}: {status}", flush=True)
        
        # Step 10: MGD refinement for remaining near-misses
        if not is_perfect and 0 < best_dist['total'] < 0.15 and task.train_examples:
            inp = task.train_examples[0].input_grid.data
            target = task.train_examples[0].output_grid
            refined = self.mgd.refine(best_pred.data, target, inp)
            if refined is not None:
                refined_dist = self.metric.compute(ARCGrid(refined), target)
                if refined_dist['total'] < best_dist['total']:
                    best_pred = ARCGrid(refined)
                    best_dist = refined_dist
                    best_method = f"{best_method}+mgd"
                    if verbose:
                        print(f"  [MGD] Refined: {best_dist['total']:.4f}", flush=True)
                    # Re-check perfection
                    if best_pred.shape == target.shape:
                        is_perfect = torch.equal(best_pred.data, target.data)
        
        # Step 8: Update gene pool and induce operators
        base_method = best_method.split(':')[-1].split('+')[0]
        self.scientist.gene_pool.use_gene(base_method, is_perfect)
        
        if is_perfect and task.train_examples:
            inp = task.train_examples[0].input_grid.data
            out = task.train_examples[0].output_grid.data
            induced = self.scientist.induce_operator(inp, out, task.task_id[:8])
            if induced and verbose:
                print(f"  [INDUCED] {induced}", flush=True)
        
        # Step 9: Anneal metric based on outcome
        self.metric.anneal_from_result(is_perfect, best_dist)
        
        # Evolve gene pool periodically
        if len(self.results) % 20 == 0:
            self.scientist.gene_pool.evolve()
        
        result = self._make_result(task, best_pred, best_method, best_dist, is_perfect)
        self.results.append(result)
        return result
    
    def _apply_cegar_method(self, inp: ARCGrid, method: str) -> Optional[ARCGrid]:
        """Apply a CEGAR method to get prediction."""
        # Parse method like "movement:1.0*V_TopEdge" or "crop:crop_to_content"
        try:
            if 'identity' in method.lower():
                return inp
            elif 'crop_to_content' in method:
                data = inp.data
                mask = (data != 0)
                if mask.any():
                    rows = mask.any(dim=1)
                    cols = mask.any(dim=0)
                    r_idx = torch.where(rows)[0]
                    c_idx = torch.where(cols)[0]
                    if len(r_idx) > 0 and len(c_idx) > 0:
                        r1, r2 = r_idx[0].item(), r_idx[-1].item() + 1
                        c1, c2 = c_idx[0].item(), c_idx[-1].item() + 1
                        return ARCGrid(data[r1:r2, c1:c2])
            elif 'color(' in method:
                # Parse color(X->Y)
                import re
                match = re.search(r'color\((\d+)->(\d+)\)', method)
                if match:
                    src, dst = int(match.group(1)), int(match.group(2))
                    data = inp.data.clone()
                    data[data == src] = dst
                    return ARCGrid(data)
        except:
            pass
        return None
    
    def _apply_fractal_method(self, inp: ARCGrid, method: str) -> Optional[ARCGrid]:
        """Apply a fractal method to get prediction."""
        return self._apply_cegar_method(inp, method)  # Reuse parsing
    
    def _generate_gated_candidates(self, task: ARCTask) -> List[Tuple[str, ARCGrid]]:
        """
        Generate candidates using Conservation Gating (Smart Search).
        
        Operations are DISABLED if they violate discovered conservation laws.
        This is System 1 (Fast) - only try operations that are likely to work.
        """
        candidates = []
        if not task.train_examples:
            return candidates
        
        inp = task.train_examples[0].input_grid
        out = task.train_examples[0].output_grid
        data = inp.data
        
        # Use hot genes first (always allowed - they've proven successful)
        for gene_name in self.scientist.gene_pool.get_hot_genes(10):
            gene = self.scientist.gene_pool.genes.get(gene_name)
            if gene and self.gate.is_allowed(gene_name):
                try:
                    result = gene['function'](data)
                    candidates.append((gene_name, ARCGrid(result)))
                except:
                    pass
        
        # Identity is always allowed
        candidates.append(('identity', inp))
        
        # Rotations (gated by symmetry discovery)
        if self.gate.is_allowed('rot90'):
            candidates.append(('rot90', ARCGrid(torch.rot90(data, k=1))))
        if self.gate.is_allowed('rot180'):
            candidates.append(('rot180', ARCGrid(torch.rot90(data, k=2))))
        if self.gate.is_allowed('rot270'):
            candidates.append(('rot270', ARCGrid(torch.rot90(data, k=3))))
        
        # Flips (gated by symmetry discovery)
        if self.gate.is_allowed('flip_h'):
            candidates.append(('flip_h', ARCGrid(torch.flip(data, dims=[1]))))
        if self.gate.is_allowed('flip_v'):
            candidates.append(('flip_v', ARCGrid(torch.flip(data, dims=[0]))))
        
        # Transpose (always try - shape preserving)
        candidates.append(('transpose', ARCGrid(data.T)))
        
        # Crop operations (gated by mass conservation)
        if self.gate.is_allowed('crop'):
            # Crop to content
            mask = (data != 0)
            if mask.any():
                rows = mask.any(dim=1)
                cols = mask.any(dim=0)
                r_idx = torch.where(rows)[0]
                c_idx = torch.where(cols)[0]
                if len(r_idx) > 0 and len(c_idx) > 0:
                    r1, r2 = r_idx[0].item(), r_idx[-1].item() + 1
                    c1, c2 = c_idx[0].item(), c_idx[-1].item() + 1
                    candidates.append(('crop_content', ARCGrid(data[r1:r2, c1:c2])))
            
            # Crop to output size
            if out.shape != inp.shape:
                oh, ow = out.shape
                ih, iw = inp.shape
                if oh <= ih and ow <= iw:
                    candidates.append(('crop_tl', ARCGrid(data[:oh, :ow])))
                    candidates.append(('crop_tr', ARCGrid(data[:oh, iw-ow:])))
                    candidates.append(('crop_bl', ARCGrid(data[ih-oh:, :ow])))
                    candidates.append(('crop_br', ARCGrid(data[ih-oh:, iw-ow:])))
                    r_start, c_start = (ih - oh) // 2, (iw - ow) // 2
                    candidates.append(('crop_center', ARCGrid(data[r_start:r_start+oh, c_start:c_start+ow])))
        
        # Extract operations (gated by mass conservation)
        if self.gate.is_allowed('extract'):
            for color in data.unique().tolist():
                if color == 0:
                    continue
                mask = (data == color).numpy().astype(np.int32)
                labeled, n_objs = ndimage.label(mask)
                if n_objs > 0:
                    sizes = [(labeled == i).sum() for i in range(1, n_objs + 1)]
                    if sizes:
                        largest_id = np.argmax(sizes) + 1
                        obj_mask = (labeled == largest_id)
                        rows = np.any(obj_mask, axis=1)
                        cols = np.any(obj_mask, axis=0)
                        r_idx, c_idx = np.where(rows)[0], np.where(cols)[0]
                        if len(r_idx) > 0 and len(c_idx) > 0:
                            r1, r2 = r_idx[0], r_idx[-1] + 1
                            c1, c2 = c_idx[0], c_idx[-1] + 1
                            candidates.append((f'extract_obj_{color}', ARCGrid(data[r1:r2, c1:c2].clone())))
        
        # Color operations (gated by color conservation)
        if self.gate.is_allowed('color'):
            colors = [c for c in data.unique().tolist() if c != 0]
            for src in colors[:3]:  # Limit to top 3 colors
                for dst in range(10):
                    if src != dst:
                        mapped = data.clone()
                        mapped[data == src] = dst
                        candidates.append((f'color({src}->{dst})', ARCGrid(mapped)))
            
            # Color swap
            if len(colors) >= 2:
                c1, c2 = colors[0], colors[1]
                swapped = data.clone()
                mask1, mask2 = (data == c1), (data == c2)
                swapped[mask1], swapped[mask2] = c2, c1
                candidates.append((f'swap({c1},{c2})', ARCGrid(swapped)))
            
            # Fill background
            if colors:
                filled = data.clone()
                filled[data == 0] = colors[0]
                candidates.append((f'fill_bg({colors[0]})', ARCGrid(filled)))
        
        # Tile quadrant (always try - structural operation)
        h, w = data.shape
        if h > 1 and w > 1:
            qh, qw = h // 2, w // 2
            if qh > 0 and qw > 0:
                quad = data[:qh, :qw]
                tiled = quad.repeat(2, 2)[:h, :w]
                candidates.append(('tile_quad', ARCGrid(tiled)))
        
        return candidates
    
    def _generate_candidates(self, task: ARCTask) -> List[Tuple[str, ARCGrid]]:
        """Generate candidates using gene pool + comprehensive transforms."""
        candidates = []
        if not task.train_examples:
            return candidates
        
        inp = task.train_examples[0].input_grid
        out = task.train_examples[0].output_grid
        data = inp.data
        
        # Use hot genes first
        for gene_name in self.scientist.gene_pool.get_hot_genes(10):
            gene = self.scientist.gene_pool.genes.get(gene_name)
            if gene:
                try:
                    result = gene['function'](data)
                    candidates.append((gene_name, ARCGrid(result)))
                except:
                    pass
        
        # Standard D4 transforms
        candidates.append(('identity', inp))
        for k in [1, 2, 3]:
            candidates.append((f'rot{k*90}', ARCGrid(torch.rot90(data, k=k))))
        candidates.append(('flip_h', ARCGrid(torch.flip(data, dims=[1]))))
        candidates.append(('flip_v', ARCGrid(torch.flip(data, dims=[0]))))
        candidates.append(('transpose', ARCGrid(data.T)))
        
        # Crop operations
        for bg in [0]:
            mask = (data != bg)
            if mask.any():
                rows = mask.any(dim=1)
                cols = mask.any(dim=0)
                r_idx = torch.where(rows)[0]
                c_idx = torch.where(cols)[0]
                if len(r_idx) > 0 and len(c_idx) > 0:
                    r1, r2 = r_idx[0].item(), r_idx[-1].item() + 1
                    c1, c2 = c_idx[0].item(), c_idx[-1].item() + 1
                    candidates.append(('crop_content', ARCGrid(data[r1:r2, c1:c2])))
        
        # Crop to output size
        if out.shape != inp.shape:
            oh, ow = out.shape
            ih, iw = inp.shape
            if oh <= ih and ow <= iw:
                candidates.append(('crop_tl', ARCGrid(data[:oh, :ow])))
                candidates.append(('crop_tr', ARCGrid(data[:oh, iw-ow:])))
                candidates.append(('crop_bl', ARCGrid(data[ih-oh:, :ow])))
                candidates.append(('crop_br', ARCGrid(data[ih-oh:, iw-ow:])))
                r_start, c_start = (ih - oh) // 2, (iw - ow) // 2
                candidates.append(('crop_center', ARCGrid(data[r_start:r_start+oh, c_start:c_start+ow])))
        
        # Extract connected components
        for color in data.unique().tolist():
            if color == 0:
                continue
            mask = (data == color).numpy().astype(np.int32)
            labeled, n_objs = ndimage.label(mask)
            if n_objs > 0:
                sizes = [(labeled == i).sum() for i in range(1, n_objs + 1)]
                if sizes:
                    largest_id = np.argmax(sizes) + 1
                    obj_mask = (labeled == largest_id)
                    rows = np.any(obj_mask, axis=1)
                    cols = np.any(obj_mask, axis=0)
                    r_idx, c_idx = np.where(rows)[0], np.where(cols)[0]
                    if len(r_idx) > 0 and len(c_idx) > 0:
                        r1, r2 = r_idx[0], r_idx[-1] + 1
                        c1, c2 = c_idx[0], c_idx[-1] + 1
                        candidates.append((f'extract_obj_{color}', ARCGrid(data[r1:r2, c1:c2].clone())))
        
        # Color operations
        colors = [c for c in data.unique().tolist() if c != 0]
        for src in colors[:5]:
            for dst in range(10):
                if src != dst:
                    mapped = data.clone()
                    mapped[data == src] = dst
                    candidates.append((f'color({src}->{dst})', ARCGrid(mapped)))
        
        # Color swap
        if len(colors) >= 2:
            c1, c2 = colors[0], colors[1]
            swapped = data.clone()
            mask1, mask2 = (data == c1), (data == c2)
            swapped[mask1], swapped[mask2] = c2, c1
            candidates.append((f'swap({c1},{c2})', ARCGrid(swapped)))
        
        # Fill background
        if colors:
            filled = data.clone()
            filled[data == 0] = colors[0]
            candidates.append((f'fill_bg({colors[0]})', ARCGrid(filled)))
        
        # Tile quadrant
        h, w = data.shape
        if h > 1 and w > 1:
            qh, qw = h // 2, w // 2
            if qh > 0 and qw > 0:
                quad = data[:qh, :qw]
                tiled = quad.repeat(2, 2)[:h, :w]
                candidates.append(('tile_quad', ARCGrid(tiled)))
        
        return candidates
    
    def _make_result(self, task, pred, method, dist=None, is_perfect=False):
        return {
            'task_id': task.task_id,
            'method': method,
            'prediction': pred,
            'fisher_distance': dist['total'] if dist else 1.0,
            'is_perfect': is_perfect,
            'conservation_laws': self.scientist.discovered_laws.get(task.task_id, [])
        }
    
    def get_summary(self) -> Dict:
        perfect = sum(1 for r in self.results if r['is_perfect'])
        near_miss = sum(1 for r in self.results 
                        if 0 < r['fisher_distance'] < 0.1 and not r['is_perfect'])
        grammar_solves = sum(1 for r in self.results if '+grammar' in r.get('method', ''))
        spectral_solves = sum(1 for r in self.results if '+spectral' in r.get('method', ''))
        compose_solves = sum(1 for r in self.results if '+compose' in r.get('method', ''))
        return {
            'total_tasks': len(self.results),
            'perfect_solves': perfect,
            'near_misses': near_miss,
            'system2_stats': {
                'attempts': self.system2_attempts,
                'successes': self.system2_successes,
                'grammar_solves': grammar_solves
            },
            'system3_stats': {
                'attempts': self.system3_attempts,
                'discoveries': self.system3_discoveries,
                'spectral_solves': spectral_solves,
                'operator_memory': len(self.spectral.get_operator_memory())
            },
            'composition_stats': {
                'attempts': self.composition_attempts,
                'successes': self.composition_successes,
                'compose_solves': compose_solves,
                'executive_stats': self.executive.get_stats()
            },
            'gene_pool': self.scientist.gene_pool.get_stats(),
            'mgd_stats': self.mgd.get_stats(),
            'final_weights': self.metric.weights
        }


def run_injection(data_path: str, verbose: bool = True):
    """Run Thermodynamic Injection Solver (Phase 15 + 19 + 23)."""
    
    tasks = load_arc_tasks(data_path, 'cpu')
    print(f"Loaded {len(tasks)} tasks", flush=True)
    
    print("\n" + "=" * 70, flush=True)
    print("THERMODYNAMIC INJECTION SOLVER (Phase 15 + 19 + 23)", flush=True)
    print("=" * 70, flush=True)
    print("\nARCHITECTURE:", flush=True)
    print("  1. Phase 15 CEGAR (movement, crop, color, extract)", flush=True)
    print("  2. Phase 19 Fractal Decomposition", flush=True)
    print("  3. Phase 23 Conservation Laws (mass, color, shape)", flush=True)
    print("  4. Phase 22 Adaptive Fisher-Rao Metric", flush=True)
    print("  5. Phase 22 Manifold Gradient Descent", flush=True)
    print("  6. Phase 23 Thermodynamic Gene Pool", flush=True)
    print("\n" + "=" * 50, flush=True)
    
    solver = ThermodynamicInjectionSolver()
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose)
        
        marker = "[PERFECT]" if result['is_perfect'] else \
                 "[NEAR]   " if result['fisher_distance'] < 0.1 else \
                 "[APPROX] " if result['fisher_distance'] < 0.3 else "         "
        
        if result['is_perfect'] or result['fisher_distance'] < 0.3:
            print(f"  {marker} {task.task_id}: {result['method']}", flush=True)
            print(f"            F={result['fisher_distance']:.4f} "
                  f"laws={result['conservation_laws']}", flush=True)
        
        if (i + 1) % 20 == 0:
            summary = solver.get_summary()
            print(f"  Progress: {i+1}/{len(tasks)}, "
                  f"perfect={summary['perfect_solves']}, "
                  f"genes={summary['gene_pool']['total']}", flush=True)
            
            # PHASE 37: Run dream cycle every 20 tasks
            if hasattr(solver, 'executive') and hasattr(solver.executive, 'dream_cycle'):
                dream_stats = solver.executive.dream_cycle(verbose=verbose)
                if dream_stats.get('promoted', 0) > 0 or dream_stats.get('pruned', 0) > 0:
                    print(f"  [DREAM] epoch={dream_stats['epoch']}, "
                          f"promoted={dream_stats.get('promoted', 0)}, "
                          f"pruned={dream_stats.get('pruned', 0)}", flush=True)
    
    # PHASE 37: Final dream cycle at the end
    if hasattr(solver, 'executive') and hasattr(solver.executive, 'dream_cycle'):
        final_dream = solver.executive.dream_cycle(verbose=verbose)
        if final_dream.get('promoted', 0) > 0 or final_dream.get('pruned', 0) > 0:
            print(f"  [FINAL DREAM] promoted={final_dream.get('promoted', 0)}, "
                  f"pruned={final_dream.get('pruned', 0)}", flush=True)
    
    summary = solver.get_summary()
    exec_stats = summary['composition_stats'].get('executive_stats', {})
    mem_stats = exec_stats.get('memory_stats', {})
    
    print("\n" + "=" * 70, flush=True)
    print("PHASE 32: UNIFIED EXECUTIVE SUMMARY", flush=True)
    print("=" * 70, flush=True)
    print(f"  Perfect solves: {summary['perfect_solves']}", flush=True)
    print(f"  Near misses: {summary['near_misses']}", flush=True)
    print(f"  System 1 (Conservation Gate): Fast path - gated candidates", flush=True)
    print(f"  System 2 (Graph Grammar): {summary['system2_stats']}", flush=True)
    print(f"  System 3 (Spectral/Sheaf): {summary['system3_stats']}", flush=True)
    print(f"  System 4 (Composition): {summary['composition_stats']['compose_solves']} solves", flush=True)
    print(f"  Canonical Operator Memory: {mem_stats.get('total', 0)} operators", flush=True)
    print(f"    - By source: {mem_stats.get('by_source', {})}", flush=True)
    print(f"    - By type: {mem_stats.get('by_type', {})}", flush=True)
    print(f"  Residual Compiler: {exec_stats.get('compiler_stats', {})}", flush=True)
    print(f"  A* Composer: {exec_stats.get('composer_stats', {})}", flush=True)
    
    # PHASE 37: Consolidation stats
    consol_stats = exec_stats.get('consolidation_stats', {})
    if consol_stats:
        print(f"  Consolidation Engine: epochs={consol_stats.get('current_epoch', 0)}, "
              f"coarse_grained={consol_stats.get('coarse_grained', 0)}, "
              f"consolidated={consol_stats.get('consolidated', 0)}, "
              f"pruned={consol_stats.get('pruned', 0)}", flush=True)
    
    print(f"  Gene pool: {summary['gene_pool']}", flush=True)
    print(f"  MGD stats: {summary['mgd_stats']}", flush=True)
    print(f"  Final weights: {summary['final_weights']}", flush=True)
    
    return solver.results


def run_hybrid(data_path: str, verbose: bool = True):
    """Run Hybrid Agentic Solver (Phase 20 + Phase 23)."""
    
    tasks = load_arc_tasks(data_path, 'cpu')
    print(f"Loaded {len(tasks)} tasks", flush=True)
    
    print("\n" + "=" * 70, flush=True)
    print("HYBRID AGENTIC SOLVER (Phase 20 + Phase 23)", flush=True)
    print("=" * 70, flush=True)
    print("\nCOMPONENTS:", flush=True)
    print("  1. Phase 20 CEGAR rules + decomposition", flush=True)
    print("  2. Conservation Law Discovery", flush=True)
    print("  3. Adaptive Fisher-Rao Metric", flush=True)
    print("  4. Manifold Gradient Descent", flush=True)
    print("  5. Operator Gene Pool", flush=True)
    print("\n" + "=" * 50, flush=True)
    
    solver = HybridAgenticSolver()
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose)
        
        marker = "[PERFECT]" if result['is_perfect'] else \
                 "[NEAR]   " if result['fisher_distance'] < 0.1 else \
                 "[APPROX] " if result['fisher_distance'] < 0.3 else "         "
        
        if result['is_perfect'] or result['fisher_distance'] < 0.3:
            print(f"  {marker} {task.task_id}: {result['method']}", flush=True)
            print(f"            F={result['fisher_distance']:.4f} "
                  f"laws={result['conservation_laws']}", flush=True)
        
        if (i + 1) % 20 == 0:
            summary = solver.get_summary()
            print(f"  Progress: {i+1}/{len(tasks)}, "
                  f"perfect={summary['perfect_solves']}, "
                  f"genes={summary['gene_pool']['total']}", flush=True)
    
    summary = solver.get_summary()
    print("\n" + "=" * 70, flush=True)
    print("HYBRID SOLVER SUMMARY", flush=True)
    print("=" * 70, flush=True)
    print(f"  Perfect solves: {summary['perfect_solves']}", flush=True)
    print(f"  Near misses: {summary['near_misses']}", flush=True)
    print(f"  Gene pool: {summary['gene_pool']}", flush=True)
    print(f"  MGD stats: {summary['mgd_stats']}", flush=True)
    print(f"  Final weights: {summary['final_weights']}", flush=True)
    
    return solver.results


# =============================================================================
# MAIN RUNNER
# =============================================================================

def run_phase23(data_path: str, verbose: bool = True):
    """Run Phase 23: The Active Scientist."""
    
    tasks = load_arc_tasks(data_path, 'cpu')
    print(f"Loaded {len(tasks)} tasks", flush=True)
    
    print("\n" + "=" * 70, flush=True)
    print("PHASE 23: THE ACTIVE SCIENTIST", flush=True)
    print("=" * 70, flush=True)
    print("\nCOMPONENTS:", flush=True)
    print("  1. Symmetry Oracle (D4 equivariance testing)", flush=True)
    print("  2. Conservation Law Discovery (mass, color, shape)", flush=True)
    print("  3. Operator Gene Pool (thermodynamic selection)", flush=True)
    print("  4. Active Inference (hypothesis testing)", flush=True)
    print("\n" + "=" * 50, flush=True)
    
    solver = Phase23Solver()
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose)
        
        marker = "[PERFECT]" if result['is_perfect'] else \
                 "[NEAR]   " if result['fisher_distance'] < 0.1 else \
                 "[APPROX] " if result['fisher_distance'] < 0.3 else "         "
        
        if result['is_perfect'] or result['fisher_distance'] < 0.3:
            print(f"  {marker} {task.task_id}: {result['method']}", flush=True)
            print(f"            F={result['fisher_distance']:.4f} "
                  f"laws={result['conservation_laws']}", flush=True)
        
        if (i + 1) % 20 == 0:
            summary = solver.get_summary()
            print(f"  Progress: {i+1}/{len(tasks)}, "
                  f"perfect={summary['perfect_solves']}, "
                  f"genes={summary['gene_pool']['total']}", flush=True)
    
    summary = solver.get_summary()
    print("\n" + "=" * 70, flush=True)
    print("PHASE 23 SUMMARY", flush=True)
    print("=" * 70, flush=True)
    print(f"  Perfect solves: {summary['perfect_solves']}", flush=True)
    print(f"  Near misses: {summary['near_misses']}", flush=True)
    print(f"  Gene pool: {summary['gene_pool']}", flush=True)
    print(f"  MGD stats: {summary['mgd_stats']}", flush=True)
    
    return solver.results


def run_phase22(data_path: str, verbose: bool = True):
    """Run Phase 22: The Thermodynamic Agent."""
    
    tasks = load_arc_tasks(data_path, 'cpu')
    print(f"Loaded {len(tasks)} tasks", flush=True)
    
    print("\n" + "=" * 70, flush=True)
    print("PHASE 22: THE THERMODYNAMIC AGENT", flush=True)
    print("=" * 70, flush=True)
    print("\nCOMPONENTS:", flush=True)
    print("  1. Adaptive Fisher-Rao Metric (Dynamic Attention)", flush=True)
    print("  2. Lie Algebra Decomposer (Generator Induction)", flush=True)
    print("  3. Manifold Gradient Descent (Continuous Flow)", flush=True)
    print("  4. Thermodynamic Policy (Active Inference)", flush=True)
    print("\n" + "=" * 50, flush=True)
    
    solver = Phase22Solver()
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose)
        
        marker = "[PERFECT]" if result['is_perfect'] else \
                 "[NEAR]   " if result['fisher_distance'] < 0.1 else \
                 "[APPROX] " if result['fisher_distance'] < 0.3 else "         "
        
        if result['is_perfect'] or result['fisher_distance'] < 0.3:
            print(f"  {marker} {task.task_id}: {result['method']}", flush=True)
            print(f"            F={result['fisher_distance']:.4f}", flush=True)
        
        if (i + 1) % 20 == 0:
            summary = solver.get_summary()
            print(f"  Progress: {i+1}/{len(tasks)}, "
                  f"perfect={summary['perfect_solves']}, "
                  f"near_miss={summary['near_misses']}", flush=True)
    
    # Final summary
    summary = solver.get_summary()
    print("\n" + "=" * 70, flush=True)
    print("PHASE 22 SUMMARY", flush=True)
    print("=" * 70, flush=True)
    print(f"  Perfect solves: {summary['perfect_solves']}", flush=True)
    print(f"  Near misses: {summary['near_misses']}", flush=True)
    print(f"  MGD refinements: {summary['mgd_stats']}", flush=True)
    print(f"  Final weights: {summary['final_weights']}", flush=True)
    print(f"  Final temperature: {summary['temperature']:.3f}", flush=True)
    
    return solver.results


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_injection(arc_path, verbose=True)
    else:
        print("ARC data not found!")


if __name__ == "__main__":
    main()
