#!/usr/bin/env python3
"""
PERIHELION Sprint 3 - Entity-Resolved Triplet Extraction

Key insight: Nodes should be identified by VALUE (binned), not TIMESTAMP.
When two observations produce the same value-bin, they map to the SAME node.
Edges accumulate across all windows, creating a coherent growing graph.

This resolves the disconnected subgraph problem from Sprint 2:
- Sprint 2: nodes = timestamps → disconnected cliques per window
- Sprint 3: nodes = value-bins → connected graph across all time

For approximate equality relation (|a-b| < ε):
- Edge (bin_i, APPROX_EQ, bin_j) exists if |center_i - center_j| < ε
- Transitivity: if bin_a ≈ bin_b and bin_b ≈ bin_c, is bin_a ≈ bin_c?
- This is NOT inherently transitive (depends on bin spacing vs tolerance)
"""

import numpy as np
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Set
from collections import defaultdict


@dataclass
class EntityResolvedCorpus:
    """
    Corpus where entities are value-bins, not timestamps.
    
    Uses DIRECTIONAL transitions: (bin_i, FOLLOWS, bin_j) means
    "after observing value in bin_i, we observed value in bin_j".
    
    This creates chains that the SGC engine can measure for transitivity.
    As the system stabilizes, transitions become more predictable → ordered.
    """
    n_bins: int
    value_min: float
    value_max: float
    
    # Entity (bin) observation counts
    bin_counts: Dict[int, int] = field(default_factory=lambda: defaultdict(int))
    
    # DIRECTED edge counts: (bin_from, bin_to) -> count of transitions
    edge_counts: Dict[Tuple[int, int], int] = field(default_factory=lambda: defaultdict(int))
    
    # Track last observed bin for sequential transitions
    last_bin: int = -1
    
    # Relation name
    relation: str = "FOLLOWS"
    
    def value_to_bin(self, value: float) -> int:
        """Map a continuous value to its bin index."""
        if self.value_max <= self.value_min:
            return 0
        normalized = (value - self.value_min) / (self.value_max - self.value_min)
        bin_idx = int(normalized * self.n_bins)
        return max(0, min(self.n_bins - 1, bin_idx))
    
    def bin_to_center(self, bin_idx: int) -> float:
        """Get the center value of a bin."""
        bin_width = (self.value_max - self.value_min) / self.n_bins
        return self.value_min + (bin_idx + 0.5) * bin_width
    
    def add_observation(self, value: float):
        """
        Add a single observation.
        
        Creates a DIRECTED edge from last_bin to current_bin.
        This captures the transition structure of the data.
        """
        bin_idx = self.value_to_bin(value)
        self.bin_counts[bin_idx] += 1
        
        # Create directed edge from previous observation to current
        if self.last_bin >= 0:
            edge = (self.last_bin, bin_idx)
            self.edge_counts[edge] += 1
        
        self.last_bin = bin_idx
    
    def add_observations(self, values: np.ndarray):
        """Add multiple observations in sequence."""
        for v in values:
            self.add_observation(v)
    
    def get_graph_stats(self) -> dict:
        """Get statistics about the entity-resolved graph."""
        n_entities = len(self.bin_counts)
        n_edges = len(self.edge_counts)
        total_observations = sum(self.bin_counts.values())
        total_edge_weight = sum(self.edge_counts.values())
        
        return {
            'n_entities': n_entities,
            'n_edges': n_edges,
            'total_observations': total_observations,
            'total_edge_weight': total_edge_weight,
            'density': n_edges / max(1, n_entities * n_entities)  # Directed graph
        }
    
    def get_triplets_for_sgc(self) -> List[Tuple[str, str, str]]:
        """
        Convert entity-resolved graph to triplets for SGC engine.
        
        Returns list of (subject, relation, object) tuples.
        Adds triplets proportional to edge weight to capture evidence strength.
        """
        triplets = []
        for (bin_from, bin_to), count in self.edge_counts.items():
            # Add multiple triplets to capture evidence strength
            # Cap at reasonable number to avoid explosion
            n_triplets = min(count, 10)
            for _ in range(n_triplets):
                triplets.append((f"bin_{bin_from}", self.relation, f"bin_{bin_to}"))
        return triplets


class AmplitudeRatioExtractor:
    """
    Extract amplitude ratios from damped pendulum trajectory.
    
    The correct observable for damped pendulum phase transition:
    - Extract local maxima of |θ(t)| (amplitude of each swing)
    - Compute ratio amplitude[n] / amplitude[n-1]
    - Early: ratios vary (transient, disordered)
    - Late: ratios converge to exp(-b*T) (exponential decay, ordered)
    
    This relation is NOT inherently transitive but BECOMES transitive
    as the exponential decay pattern establishes.
    """
    
    def __init__(self, min_peak_distance: int = 10):
        """
        Args:
            min_peak_distance: Minimum samples between detected peaks
        """
        self.min_peak_distance = min_peak_distance
    
    def extract_amplitudes(self, theta: np.ndarray) -> np.ndarray:
        """
        Extract local maxima of |θ(t)| (swing amplitudes).
        
        Uses simple peak detection: a point is a peak if it's larger
        than its neighbors and larger than points min_peak_distance away.
        """
        abs_theta = np.abs(theta)
        n = len(abs_theta)
        
        # Find local maxima
        peaks = []
        for i in range(1, n - 1):
            # Check if local maximum
            if abs_theta[i] > abs_theta[i-1] and abs_theta[i] > abs_theta[i+1]:
                # Check minimum distance from previous peak
                if len(peaks) == 0 or i - peaks[-1] >= self.min_peak_distance:
                    peaks.append(i)
        
        if len(peaks) < 2:
            return np.array([])
        
        amplitudes = abs_theta[peaks]
        return amplitudes
    
    def compute_amplitude_ratios(self, amplitudes: np.ndarray) -> np.ndarray:
        """Compute consecutive amplitude ratios."""
        if len(amplitudes) < 2:
            return np.array([])
        
        # Avoid division by zero
        amplitudes_safe = np.maximum(amplitudes, 1e-10)
        ratios = amplitudes_safe[1:] / amplitudes_safe[:-1]
        return ratios
    
    def extract_from_trajectory(self, theta: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """
        Extract amplitudes and ratios from full trajectory.
        
        Returns:
            (amplitudes, ratios)
        """
        amplitudes = self.extract_amplitudes(theta)
        ratios = self.compute_amplitude_ratios(amplitudes)
        return amplitudes, ratios


def create_entity_resolved_corpus(
    values: np.ndarray,
    n_bins: int = 20,
    relation: str = "FOLLOWS"
) -> EntityResolvedCorpus:
    """
    Create an entity-resolved corpus from observed values.
    
    Uses DIRECTIONAL transitions: consecutive values create directed edges
    between their bins. This captures the transition structure.
    
    Args:
        values: Array of observed values (in sequence order)
        n_bins: Number of bins for discretization
        relation: Name of the relation
        
    Returns:
        EntityResolvedCorpus with all observations added
    """
    if len(values) == 0:
        return EntityResolvedCorpus(
            n_bins=n_bins,
            value_min=0.0,
            value_max=1.0,
            relation=relation
        )
    
    value_min = float(np.min(values))
    value_max = float(np.max(values))
    
    # Expand range slightly to avoid edge effects
    range_width = value_max - value_min
    if range_width < 1e-10:
        range_width = 1.0
    value_min -= 0.01 * range_width
    value_max += 0.01 * range_width
    
    corpus = EntityResolvedCorpus(
        n_bins=n_bins,
        value_min=value_min,
        value_max=value_max,
        relation=relation
    )
    
    corpus.add_observations(values)
    return corpus


def test_entity_resolution():
    """Test entity-resolved corpus."""
    print("=" * 60)
    print("  Entity-Resolved Corpus Test")
    print("=" * 60)
    
    # Generate test data: values that cluster over time
    np.random.seed(42)
    
    # Phase 1: spread values
    phase1 = np.random.uniform(0, 10, 50)
    
    # Phase 2: clustering values
    phase2 = 5.0 + np.random.normal(0, 0.5, 50)
    
    values = np.concatenate([phase1, phase2])
    
    # Create corpus
    corpus = create_entity_resolved_corpus(values, n_bins=20, tolerance_factor=2.0)
    
    print(f"\n[1] Corpus statistics:")
    stats = corpus.get_graph_stats()
    for k, v in stats.items():
        print(f"  {k}: {v}")
    
    print(f"\n[2] Bin distribution:")
    for bin_idx in sorted(corpus.bin_counts.keys()):
        count = corpus.bin_counts[bin_idx]
        center = corpus.bin_to_center(bin_idx)
        bar = "#" * min(count, 30)
        print(f"  bin {bin_idx:2d} (center={center:.2f}): {count:3d} {bar}")
    
    print(f"\n[3] Top edges:")
    sorted_edges = sorted(corpus.edge_counts.items(), key=lambda x: -x[1])[:10]
    for (bin_i, bin_j), count in sorted_edges:
        c_i, c_j = corpus.bin_to_center(bin_i), corpus.bin_to_center(bin_j)
        print(f"  ({bin_i}, {bin_j}) [{c_i:.2f} <-> {c_j:.2f}]: {count}")
    
    print("\n" + "=" * 60)


if __name__ == "__main__":
    test_entity_resolution()
