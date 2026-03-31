#!/usr/bin/env python3
"""
PERIHELION Stage 4: SGC Engine

Computes trans_rate and δ for each relation type.
Applies RG coarse-graining toward 2×2 fixed point.

Key formulas:
- trans_rate = P((a,R,c) exists | (a,R,b) and (b,R,c) exist)
- δ = 1 - trans_rate
- Percolation threshold: trans_rate = 0.83
- Fixed point: L = c·[[1,-1],[-1,1]]
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from collections import defaultdict


@dataclass
class TransRateMeasurement:
    """Result of trans_rate measurement for a relation."""
    relation: str
    trans_rate: float
    delta: float
    n_chains_tested: int
    n_chains_closed: int
    phase: str  # "ordered", "critical", "disordered"
    coupling_c: float = 0.0


@dataclass 
class RGConvergenceResult:
    """Result of RG flow to fixed point."""
    relation: str
    iterations: int
    initial_dim: int
    final_c: float
    converged: bool
    c_trajectory: List[float] = field(default_factory=list)


class SGCEngine:
    """
    Stage 4 of PERIHELION pipeline.
    
    Core functions:
    1. Measure trans_rate for each relation
    2. Compute δ = 1 - trans_rate
    3. Classify phase: ordered (δ<0.05), critical (0.05≤δ<0.30), disordered (δ≥0.30)
    4. Apply RG coarse-graining to reach 2×2 fixed point
    5. Extract coupling constant c
    """
    
    # Phase boundaries from SGC theory
    ORDERED_THRESHOLD = 0.05      # δ < 0.05 = ordered phase
    CRITICAL_UPPER = 0.30         # 0.05 ≤ δ < 0.30 = critical phase
    PERCOLATION_THRESHOLD = 0.83  # trans_rate crossing point for grokking
    
    def __init__(self, min_chains: int = 10):
        """
        Initialize SGC engine.
        
        Args:
            min_chains: Minimum chains needed for reliable measurement
        """
        self.min_chains = min_chains
        
        # Streaming state: accumulated triplets per relation
        self._triplet_index: Dict[str, Dict[str, set]] = defaultdict(lambda: defaultdict(set))
        self._trans_rate_history: Dict[str, List[Tuple[int, float]]] = defaultdict(list)
    
    def add_triplet(self, subject: str, relation: str, obj: str, timestep: int = 0):
        """Add a triplet to the streaming accumulator."""
        # Index by (relation, subject) -> set of objects
        self._triplet_index[relation][subject].add(obj)
    
    def measure_trans_rate(self, relation: str) -> Optional[TransRateMeasurement]:
        """
        Measure trans_rate for a relation from accumulated triplets.
        
        Trans_rate = P((a,R,c) | (a,R,b) ∧ (b,R,c))
        
        We look for chains: a→b and b→c, then check if a→c exists.
        """
        index = self._triplet_index[relation]
        
        if not index:
            return None
        
        n_chains_tested = 0
        n_chains_closed = 0
        
        # For each subject a with objects
        for a, objects_of_a in index.items():
            # For each b that a points to
            for b in objects_of_a:
                # Check if b has outgoing edges
                if b in index:
                    # For each c that b points to
                    for c in index[b]:
                        if c != a:  # Avoid self-loops
                            n_chains_tested += 1
                            # Check if a→c exists
                            if c in objects_of_a:
                                n_chains_closed += 1
        
        if n_chains_tested < self.min_chains:
            return None
        
        trans_rate = n_chains_closed / n_chains_tested if n_chains_tested > 0 else 0.0
        delta = 1.0 - trans_rate
        
        # Classify phase
        if delta < self.ORDERED_THRESHOLD:
            phase = "ordered"
        elif delta < self.CRITICAL_UPPER:
            phase = "critical"
        else:
            phase = "disordered"
        
        # Compute coupling c from composition law
        # c = 1 / (1 + δ) approximately
        coupling_c = 1.0 / (1.0 + delta) if delta < 10 else 0.0
        
        return TransRateMeasurement(
            relation=relation,
            trans_rate=trans_rate,
            delta=delta,
            n_chains_tested=n_chains_tested,
            n_chains_closed=n_chains_closed,
            phase=phase,
            coupling_c=coupling_c
        )
    
    def measure_all_relations(self) -> Dict[str, TransRateMeasurement]:
        """Measure trans_rate for all accumulated relations."""
        results = {}
        for relation in self._triplet_index.keys():
            measurement = self.measure_trans_rate(relation)
            if measurement:
                results[relation] = measurement
        return results
    
    def update_streaming(self, triplets: list, timestep: int) -> Dict[str, float]:
        """
        Update with new triplets and return current trans_rates.
        
        Used in streaming mode to track trans_rate evolution over time.
        """
        # Add new triplets
        for t in triplets:
            self.add_triplet(t.subject, t.relation, t.obj, timestep)
        
        # Measure current trans_rates
        current_rates = {}
        for relation in self._triplet_index.keys():
            measurement = self.measure_trans_rate(relation)
            if measurement:
                current_rates[relation] = measurement.trans_rate
                self._trans_rate_history[relation].append((timestep, measurement.trans_rate))
        
        return current_rates
    
    def get_trans_rate_history(self, relation: str) -> List[Tuple[int, float]]:
        """Get history of trans_rate measurements for a relation."""
        return self._trans_rate_history[relation]
    
    def detect_grokking_moment(self, relation: str) -> Optional[int]:
        """
        Detect timestep T* when trans_rate crosses percolation threshold.
        
        Returns timestep of grokking moment, or None if not yet occurred.
        """
        history = self._trans_rate_history[relation]
        
        for i, (timestep, rate) in enumerate(history):
            if rate >= self.PERCOLATION_THRESHOLD:
                return timestep
        
        return None
    
    def rg_coarse_grain(
        self,
        adjacency_matrix: np.ndarray,
        max_iterations: int = 20
    ) -> RGConvergenceResult:
        """
        Apply RG coarse-graining to adjacency matrix.
        
        Iteratively reduces dimension until reaching 2×2 fixed point.
        At fixed point: L = c·[[1,-1],[-1,1]]
        
        Args:
            adjacency_matrix: Square matrix representing relation graph
            max_iterations: Maximum RG steps
            
        Returns:
            RGConvergenceResult with convergence information
        """
        L = adjacency_matrix.astype(float)
        n = L.shape[0]
        initial_dim = n
        c_trajectory = []
        
        for iteration in range(max_iterations):
            current_n = L.shape[0]
            
            # Compute current coupling c
            c = self._extract_coupling(L)
            c_trajectory.append(c)
            
            # Check convergence to 2×2
            if current_n <= 2:
                return RGConvergenceResult(
                    relation="",
                    iterations=iteration + 1,
                    initial_dim=initial_dim,
                    final_c=c,
                    converged=True,
                    c_trajectory=c_trajectory
                )
            
            # RG step: coarse-grain by merging pairs
            new_n = current_n // 2
            if new_n < 2:
                new_n = 2
            
            # Spectral coarse-graining via eigenvector projection
            L_new = self._spectral_coarse_grain(L, new_n)
            L = L_new
        
        # Did not converge in max iterations
        return RGConvergenceResult(
            relation="",
            iterations=max_iterations,
            initial_dim=initial_dim,
            final_c=self._extract_coupling(L),
            converged=False,
            c_trajectory=c_trajectory
        )
    
    def _spectral_coarse_grain(self, L: np.ndarray, target_dim: int) -> np.ndarray:
        """
        Spectral coarse-graining via eigenvector projection.
        
        Projects onto top eigenvectors, preserving dominant structure.
        """
        n = L.shape[0]
        
        if n <= target_dim:
            return L
        
        # Compute eigenvectors
        try:
            eigenvalues, eigenvectors = np.linalg.eigh(L)
        except np.linalg.LinAlgError:
            # Fallback: simple averaging
            return self._simple_coarse_grain(L, target_dim)
        
        # Sort by eigenvalue magnitude
        idx = np.argsort(np.abs(eigenvalues))[::-1]
        
        # Project onto top eigenvectors
        V = eigenvectors[:, idx[:target_dim]]
        
        # Coarse-grained matrix
        L_coarse = V.T @ L @ V
        
        return L_coarse
    
    def _simple_coarse_grain(self, L: np.ndarray, target_dim: int) -> np.ndarray:
        """Simple coarse-graining by averaging blocks."""
        n = L.shape[0]
        block_size = n // target_dim
        
        L_coarse = np.zeros((target_dim, target_dim))
        
        for i in range(target_dim):
            for j in range(target_dim):
                i_start, i_end = i * block_size, min((i + 1) * block_size, n)
                j_start, j_end = j * block_size, min((j + 1) * block_size, n)
                L_coarse[i, j] = np.mean(L[i_start:i_end, j_start:j_end])
        
        return L_coarse
    
    def _extract_coupling(self, L: np.ndarray) -> float:
        """
        Extract coupling constant c from matrix.
        
        For 2×2 fixed point: L = c·[[1,-1],[-1,1]]
        So c = (L[0,0] - L[0,1]) / 2 approximately
        """
        if L.shape[0] < 2:
            return 0.0
        
        # Use the anti-symmetric part
        c = (L[0, 0] - L[0, 1] + L[1, 1] - L[1, 0]) / 4.0
        return abs(c)
    
    def build_adjacency_from_triplets(self, relation: str) -> np.ndarray:
        """Build adjacency matrix from accumulated triplets."""
        index = self._triplet_index[relation]
        
        # Get all unique nodes
        nodes = set()
        for subj, objs in index.items():
            nodes.add(subj)
            nodes.update(objs)
        
        node_list = sorted(nodes)
        node_to_idx = {n: i for i, n in enumerate(node_list)}
        n = len(node_list)
        
        if n == 0:
            return np.array([[]])
        
        # Build adjacency
        adj = np.zeros((n, n))
        for subj, objs in index.items():
            i = node_to_idx[subj]
            for obj in objs:
                j = node_to_idx[obj]
                adj[i, j] = 1.0
        
        return adj
    
    def reset(self):
        """Reset streaming state."""
        self._triplet_index = defaultdict(lambda: defaultdict(set))
        self._trans_rate_history = defaultdict(list)


def test_sgc_engine():
    """Quick test of SGC engine."""
    print("Testing SGCEngine...")
    
    engine = SGCEngine(min_chains=5)
    
    # Add transitive triplets (should have high trans_rate)
    # a→b→c→d with closure a→c, a→d, b→d
    transitive_triplets = [
        ("a", "b"), ("b", "c"), ("c", "d"),
        ("a", "c"), ("a", "d"), ("b", "d")  # Transitive closure
    ]
    for s, o in transitive_triplets:
        engine.add_triplet(s, "transitive", o)
    
    # Add non-transitive triplets (should have low trans_rate)
    nontrans_triplets = [
        ("x", "y"), ("y", "z"), ("z", "w"),
        ("p", "q"), ("q", "r"), ("r", "s")
        # No transitive closure
    ]
    for s, o in nontrans_triplets:
        engine.add_triplet(s, "nontrans", o)
    
    # Measure
    trans_result = engine.measure_trans_rate("transitive")
    nontrans_result = engine.measure_trans_rate("nontrans")
    
    print(f"  Transitive relation:")
    print(f"    trans_rate: {trans_result.trans_rate:.3f}")
    print(f"    δ: {trans_result.delta:.3f}")
    print(f"    phase: {trans_result.phase}")
    
    print(f"  Non-transitive relation:")
    print(f"    trans_rate: {nontrans_result.trans_rate:.3f}")
    print(f"    δ: {nontrans_result.delta:.3f}")
    print(f"    phase: {nontrans_result.phase}")
    
    assert trans_result.trans_rate > nontrans_result.trans_rate
    print("  ✓ SGC engine test passed")
    
    # Test RG coarse-graining
    print("\n  Testing RG coarse-graining...")
    adj = engine.build_adjacency_from_triplets("transitive")
    if adj.size > 0:
        rg_result = engine.rg_coarse_grain(adj)
        print(f"    Initial dim: {rg_result.initial_dim}")
        print(f"    Iterations: {rg_result.iterations}")
        print(f"    Final c: {rg_result.final_c:.4f}")
        print(f"    Converged: {rg_result.converged}")
    
    return engine


if __name__ == "__main__":
    test_sgc_engine()
