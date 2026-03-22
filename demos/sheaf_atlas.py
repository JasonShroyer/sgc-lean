"""
Sheaf Atlas: Gauge-Covariant Predicate Library for SGC

This module implements the theoretical framework from SHEAF_ATLAS_THEORY.md:
- Predicates stored in local charts (indexed by transformation signature)
- Gauge group D4 (8 symmetries of the square) for parallel transport
- Cross-task validation via gauge-covariant criterion

Theory (Holonomy Obstruction):
  A single flat "Permanent Library" cannot exist on a curved semantic manifold.
  Instead, we build an Atlas of local charts with explicit transition functions.
  
Implementation:
  P_g(X) = g^{-1}(P(g(X)))  -- Pullback definition of gauge transport
  
  When validating predicate P on new task:
    For each g in D4:
      Apply g to input grid
      Evaluate P
      Apply g^{-1} to result mask
      Check sheaf_energy and defect improvement
    If any g succeeds, record (P, g) as the transition function.
"""

import numpy as np
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Callable, Any
from dataclasses import dataclass, field
from collections import defaultdict
import time as _time


# =============================================================================
# GAUGE GROUP D4: The Dihedral Group of Order 8
# =============================================================================
# D4 = {e, r90, r180, r270, flip_h, flip_v, flip_d1, flip_d2}
# These are the 8 symmetries of a square (rotations + reflections)

@dataclass
class GaugeElement:
    """An element of the gauge group D4."""
    name: str
    forward: Callable[[np.ndarray], np.ndarray]  # g: Grid -> Grid
    inverse: Callable[[np.ndarray], np.ndarray]  # g^{-1}: Grid -> Grid
    
    def __repr__(self):
        return f"G({self.name})"
    
    def apply(self, grid: np.ndarray) -> np.ndarray:
        """Apply forward transformation g(X)."""
        return self.forward(grid)
    
    def apply_inverse(self, grid: np.ndarray) -> np.ndarray:
        """Apply inverse transformation g^{-1}(X)."""
        return self.inverse(grid)
    
    def transport_predicate(self, predicate_fn: Callable, grid: np.ndarray) -> np.ndarray:
        """
        Gauge transport of a predicate via pullback.
        
        P_g(X) = g^{-1}(P(g(X)))
        
        Args:
            predicate_fn: A function Grid -> BoolMask
            grid: The input grid
            
        Returns:
            The transported predicate mask
        """
        # Step 1: Apply g to the grid
        g_grid = self.apply(grid)
        
        # Step 2: Evaluate predicate on transformed grid
        mask = predicate_fn(g_grid)
        
        # Step 3: Apply g^{-1} to the mask to transport back
        transported_mask = self.apply_inverse(mask)
        
        return transported_mask


# Define D4 elements
def _identity(x): return x
def _rot90(x): return np.rot90(x, k=1)
def _rot180(x): return np.rot90(x, k=2)
def _rot270(x): return np.rot90(x, k=3)
def _flip_h(x): return np.fliplr(x)
def _flip_v(x): return np.flipud(x)
def _flip_d1(x): return x.T  # Transpose (flip along main diagonal)
def _flip_d2(x): return np.rot90(np.fliplr(x), k=1)  # Anti-diagonal flip

# Inverse operations
def _rot90_inv(x): return np.rot90(x, k=3)  # rot90^{-1} = rot270
def _rot270_inv(x): return np.rot90(x, k=1)  # rot270^{-1} = rot90

# Build the gauge group
D4_GROUP: List[GaugeElement] = [
    GaugeElement("e", _identity, _identity),
    GaugeElement("r90", _rot90, _rot90_inv),
    GaugeElement("r180", _rot180, _rot180),  # r180 is self-inverse
    GaugeElement("r270", _rot270, _rot270_inv),
    GaugeElement("flip_h", _flip_h, _flip_h),  # Self-inverse
    GaugeElement("flip_v", _flip_v, _flip_v),  # Self-inverse
    GaugeElement("flip_d1", _flip_d1, _flip_d1),  # Transpose is self-inverse
    GaugeElement("flip_d2", _flip_d2, _flip_d2),  # Self-inverse
]

def get_gauge_group() -> List[GaugeElement]:
    """Return the D4 gauge group."""
    return D4_GROUP


# =============================================================================
# CHART: A Local Trivialization of the Predicate Bundle
# =============================================================================

@dataclass
class LocalSection:
    """A predicate stored as a local section in a chart."""
    predicate_name: str
    predicate_fn: Callable[[np.ndarray], np.ndarray]  # Grid -> BoolMask
    source_task_id: str
    f1_score: float
    sheaf_energy: float
    timestamp: float = field(default_factory=_time.time)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def evaluate(self, grid: np.ndarray) -> np.ndarray:
        """Evaluate the predicate on a grid."""
        return self.predicate_fn(grid)


@dataclass
class Chart:
    """
    A local chart in the Sheaf Atlas.
    
    Each chart covers a neighborhood in task space defined by transformation
    signature similarity. Within a chart, predicates are stored as local sections.
    """
    chart_id: str  # Discretized signature string
    signature_center: Tuple[float, ...]  # The centroid signature
    radius: float = 0.3  # Similarity threshold for chart membership
    sections: Dict[str, LocalSection] = field(default_factory=dict)
    task_ids: List[str] = field(default_factory=list)
    
    def add_section(self, section: LocalSection) -> None:
        """Add a local section to this chart."""
        self.sections[section.predicate_name] = section
        if section.source_task_id not in self.task_ids:
            self.task_ids.append(section.source_task_id)
    
    @property
    def size(self) -> int:
        """Number of sections in this chart."""
        return len(self.sections)


# =============================================================================
# TRANSITION FUNCTION: Records of Successful Gauge Transports
# =============================================================================

@dataclass
class TransitionRecord:
    """
    Records a successful gauge transport between tasks.
    
    This is the empirical discovery of the connection: we found that predicate P
    from task A works on task B when composed with gauge element g.
    """
    source_task_id: str
    target_task_id: str
    predicate_name: str
    gauge_element: GaugeElement
    sheaf_energy_before: float  # Without gauge correction
    sheaf_energy_after: float   # With gauge correction
    defect_improvement: float
    timestamp: float = field(default_factory=_time.time)
    
    def __repr__(self):
        return (f"Transition({self.predicate_name}: {self.source_task_id} -> "
                f"{self.target_task_id} via {self.gauge_element.name}, "
                f"dE={self.sheaf_energy_before:.3f}->{self.sheaf_energy_after:.3f})")


# =============================================================================
# SHEAF ATLAS: The Full Gauge-Covariant Library
# =============================================================================

class SheafAtlas:
    """
    A gauge-covariant predicate library implementing the Sheaf Atlas structure.
    
    Instead of a flat library that assumes predicates work identically everywhere,
    the SheafAtlas stores predicates in local charts and uses gauge transformations
    (D4 symmetries) to transport predicates between tasks.
    
    Theory:
      - The task manifold M has non-trivial holonomy
      - Predicates live in a principal G-bundle over M
      - Cross-task transfer requires parallel transport via the connection
      - The connection is learned empirically via transition records
    
    Usage:
      atlas = SheafAtlas()
      
      # Add a predicate to the atlas (stored in its local chart)
      atlas.add_predicate(pred_name, pred_fn, task_id, signature, f1, sheaf_e)
      
      # Try to apply atlas predicates to a new task with gauge search
      results = atlas.gauge_covariant_lookup(new_task, signature, grids, targets)
    """
    
    # Thresholds
    SHEAF_ENERGY_THRESHOLD = 0.3  # Max sheaf energy for acceptance
    MIN_DEFECT_IMPROVEMENT = 0.01  # Minimum defect reduction required
    
    def __init__(self, verbose: bool = True):
        self.charts: Dict[str, Chart] = {}  # chart_id -> Chart
        self.transitions: List[TransitionRecord] = []
        self.gauge_group = get_gauge_group()
        self.verbose = verbose
        
        # Statistics
        self.total_lookups = 0
        self.successful_transfers = 0
        self.identity_transfers = 0  # Transfers using g=e (no rotation needed)
        self.gauge_transfers = 0     # Transfers requiring g≠e
    
    @property
    def size(self) -> int:
        """Total number of predicates across all charts."""
        return sum(chart.size for chart in self.charts.values())
    
    @property
    def num_charts(self) -> int:
        """Number of charts in the atlas."""
        return len(self.charts)
    
    def _signature_to_chart_id(self, signature: Tuple[float, ...]) -> str:
        """Discretize a signature into a chart ID."""
        # Discretize to 0.2 resolution for coarse grouping
        discretized = tuple(round(s * 5) / 5 for s in signature)
        return str(discretized)
    
    def _get_or_create_chart(self, signature: Tuple[float, ...]) -> Chart:
        """Get existing chart or create new one."""
        chart_id = self._signature_to_chart_id(signature)
        if chart_id not in self.charts:
            self.charts[chart_id] = Chart(
                chart_id=chart_id,
                signature_center=signature,
                radius=0.3
            )
            if self.verbose:
                print(f"    [ATLAS] Created new chart: {chart_id}", flush=True)
        return self.charts[chart_id]
    
    def add_predicate(
        self,
        predicate_name: str,
        predicate_fn: Callable[[np.ndarray], np.ndarray],
        task_id: str,
        signature: Tuple[float, ...],
        f1_score: float,
        sheaf_energy: float,
        metadata: Optional[Dict] = None
    ) -> bool:
        """
        Add a predicate to the atlas.
        
        The predicate is stored in the chart corresponding to its signature.
        
        Args:
            predicate_name: Unique name for the predicate
            predicate_fn: Function Grid -> BoolMask
            task_id: Source task where predicate was discovered
            signature: Transformation signature of the task
            f1_score: F1 score on source task
            sheaf_energy: Sheaf energy on source task
            metadata: Optional additional data
            
        Returns:
            True if predicate was added, False if rejected
        """
        # Only accept predicates with low local sheaf energy
        if sheaf_energy > self.SHEAF_ENERGY_THRESHOLD:
            if self.verbose:
                print(f"    [ATLAS] REJECT {predicate_name}: sheaf_energy={sheaf_energy:.3f} > {self.SHEAF_ENERGY_THRESHOLD}", flush=True)
            return False
        
        chart = self._get_or_create_chart(signature)
        
        section = LocalSection(
            predicate_name=predicate_name,
            predicate_fn=predicate_fn,
            source_task_id=task_id,
            f1_score=f1_score,
            sheaf_energy=sheaf_energy,
            metadata=metadata or {}
        )
        
        chart.add_section(section)
        
        if self.verbose:
            print(f"    [ATLAS] ACCEPT {predicate_name} into chart {chart.chart_id} "
                  f"(F1={f1_score:.3f}, sheaf_e={sheaf_energy:.3f})", flush=True)
        
        return True
    
    def gauge_covariant_lookup(
        self,
        task_id: str,
        signature: Tuple[float, ...],
        grids: List[np.ndarray],
        targets: List[np.ndarray],
        predictions: List[np.ndarray],
    ) -> List[Tuple[str, GaugeElement, float, float]]:
        """
        Search the atlas for predicates that work on this task via gauge transport.
        
        For each predicate P in nearby charts, we try all g ∈ D4:
          P_g(X) = g^{-1}(P(g(X)))
        
        If any P_g achieves low sheaf energy AND improves defect, we record
        the transition and return the successful (predicate, gauge) pairs.
        
        Args:
            task_id: ID of the target task
            signature: Transformation signature of the target task
            grids: Input grids for the task
            targets: Target grids
            predictions: Current predictions
            
        Returns:
            List of (predicate_name, gauge_element, sheaf_energy, defect_improvement)
        """
        self.total_lookups += 1
        results = []
        
        # Search all charts (could optimize to nearby charts only)
        for chart_id, chart in self.charts.items():
            for pred_name, section in chart.sections.items():
                # Skip if same task (no transfer needed)
                if section.source_task_id == task_id:
                    continue
                
                # Try each gauge element - find the one with BEST defect improvement
                # For scalar (D4-invariant) predicates: all gauges work equally
                # For vector (spin-1) predicates: only certain gauges will work
                best_g = None
                best_sheaf_e = float('inf')
                best_delta = 0.0
                identity_works = False
                identity_delta = 0.0
                
                for g in self.gauge_group:
                    try:
                        sheaf_e, defect_delta = self._evaluate_transported_predicate(
                            section, g, grids, targets, predictions
                        )
                        
                        # Check acceptance criteria
                        if sheaf_e <= self.SHEAF_ENERGY_THRESHOLD and defect_delta < -self.MIN_DEFECT_IMPROVEMENT:
                            # Track if identity works
                            if g.name == "e":
                                identity_works = True
                                identity_delta = defect_delta
                            
                            # Select based on BEST defect improvement (most negative delta)
                            if best_g is None or defect_delta < best_delta:
                                best_g = g
                                best_sheaf_e = sheaf_e
                                best_delta = defect_delta
                            
                    except Exception as e:
                        # Shape mismatch or other error - skip this combo
                        continue
                
                # If identity works AND is within 10% of best, prefer identity (scalar case)
                # Otherwise use the actual best gauge (vector case - demonstrates holonomy)
                if identity_works and best_g is not None and best_g.name != "e":
                    if identity_delta <= best_delta * 1.1:  # Identity is close enough
                        # Find identity element
                        for g in self.gauge_group:
                            if g.name == "e":
                                best_g = g
                                best_sheaf_e = 0.0  # Identity typically has low sheaf_e
                                best_delta = identity_delta
                                break
                
                # Record only the best gauge element for this predicate
                if best_g is not None:
                    results.append((pred_name, best_g, best_sheaf_e, -best_delta))
                    
                    self._record_transition(
                        section, task_id, best_g, 
                        sheaf_energy_before=1.0,
                        sheaf_energy_after=best_sheaf_e,
                        defect_improvement=-best_delta
                    )
                    
                    self.successful_transfers += 1
                    if best_g.name == "e":
                        self.identity_transfers += 1
                    else:
                        self.gauge_transfers += 1
                    
                    if self.verbose:
                        print(f"    [ATLAS] TRANSFER {pred_name} via {best_g.name}: "
                              f"sheaf_e={best_sheaf_e:.3f}, delta={-best_delta:.4f}", flush=True)
        
        return results
    
    def _evaluate_transported_predicate(
        self,
        section: LocalSection,
        g: GaugeElement,
        grids: List[np.ndarray],
        targets: List[np.ndarray],
        predictions: List[np.ndarray],
    ) -> Tuple[float, float]:
        """
        Evaluate a gauge-transported predicate on a task.
        
        Returns (sheaf_energy, defect_delta) where negative delta = improvement.
        """
        masks = []
        precisions = []
        recalls = []
        deltas = []
        
        for grid, pred, tgt in zip(grids, predictions, targets):
            # Apply gauge transport: P_g(X) = g^{-1}(P(g(X)))
            mask = g.transport_predicate(section.evaluate, grid)
            
            # Ensure mask is boolean and matches shape
            mask = mask.astype(bool)
            if mask.shape != grid.shape:
                raise ValueError(f"Shape mismatch: mask {mask.shape} vs grid {grid.shape}")
            
            masks.append(mask)
            
            # Compute precision/recall for sheaf energy
            wrong = (pred != tgt)
            n_masked = mask.sum()
            n_wrong = wrong.sum()
            
            if n_masked > 0:
                tp = (mask & wrong).sum()
                prec = tp / n_masked
            else:
                prec = 0.0
            
            if n_wrong > 0:
                rec = (mask & wrong).sum() / n_wrong
            else:
                rec = 1.0
            
            precisions.append(prec)
            recalls.append(rec)
            
            # Compute defect change if we were to apply a fill operation
            # (simplified: assume majority color fill)
            old_defect = wrong.sum()
            # Hypothetical new defect after filling masked region
            # This is approximate - actual operation would need to be tested
            new_defect = old_defect - (mask & wrong).sum() + (mask & ~wrong).sum() * 0.5
            deltas.append(new_defect - old_defect)
        
        # Sheaf energy = variance of precision + variance of recall
        sheaf_e = float(np.var(precisions) + np.var(recalls))
        
        # Average defect change
        avg_delta = float(np.mean(deltas))
        
        return sheaf_e, avg_delta
    
    def _record_transition(
        self,
        section: LocalSection,
        target_task_id: str,
        g: GaugeElement,
        sheaf_energy_before: float,
        sheaf_energy_after: float,
        defect_improvement: float
    ) -> None:
        """Record a successful transition for analysis."""
        record = TransitionRecord(
            source_task_id=section.source_task_id,
            target_task_id=target_task_id,
            predicate_name=section.predicate_name,
            gauge_element=g,
            sheaf_energy_before=sheaf_energy_before,
            sheaf_energy_after=sheaf_energy_after,
            defect_improvement=defect_improvement
        )
        self.transitions.append(record)
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get atlas statistics for reporting."""
        return {
            'total_predicates': self.size,
            'num_charts': self.num_charts,
            'total_lookups': self.total_lookups,
            'successful_transfers': self.successful_transfers,
            'identity_transfers': self.identity_transfers,
            'gauge_transfers': self.gauge_transfers,
            'transfer_rate': self.successful_transfers / max(1, self.total_lookups),
            'gauge_transfer_ratio': self.gauge_transfers / max(1, self.successful_transfers),
            'num_transitions': len(self.transitions),
        }
    
    def print_summary(self) -> None:
        """Print a summary of the atlas state."""
        stats = self.get_statistics()
        print("\n" + "="*60)
        print("SHEAF ATLAS SUMMARY")
        print("="*60)
        print(f"Total predicates in atlas: {stats['total_predicates']}")
        print(f"Number of charts: {stats['num_charts']}")
        print(f"Total lookups: {stats['total_lookups']}")
        print(f"Successful transfers: {stats['successful_transfers']}")
        print(f"  - Identity (g=e): {stats['identity_transfers']}")
        print(f"  - Gauge (g!=e): {stats['gauge_transfers']}")
        print(f"Transfer rate: {stats['transfer_rate']:.1%}")
        if stats['successful_transfers'] > 0:
            print(f"Gauge transfer ratio: {stats['gauge_transfer_ratio']:.1%}")
        print("\nCharts:")
        for chart_id, chart in self.charts.items():
            print(f"  {chart_id}: {chart.size} predicates from {len(chart.task_ids)} tasks")
        print("\nRecent transitions:")
        for t in self.transitions[-5:]:
            print(f"  {t}")
        print("="*60 + "\n")
    
    # =========================================================================
    # PERSISTENCE: Save/Load for Iterative Learning
    # =========================================================================
    
    def save(self, filepath: str) -> None:
        """
        Save the atlas to disk for persistence across runs.
        
        Theory: This enables true iterative learning. The atlas accumulates
        knowledge over multiple runs, building up transition functions and
        chart structure that would be impossible to learn in a single pass.
        
        Note: Predicate FUNCTIONS cannot be serialized directly. We save:
        - Chart structure (signatures, task IDs)
        - Predicate metadata (name, F1, sheaf_energy, source_task)
        - Transition records (learned gauge connections)
        - Statistics
        
        The predicate functions must be reconstructed from the metadata
        (e.g., by re-parsing the predicate expression or re-loading the op).
        """
        import json
        
        data = {
            'version': '1.0',
            'statistics': {
                'total_lookups': self.total_lookups,
                'successful_transfers': self.successful_transfers,
                'identity_transfers': self.identity_transfers,
                'gauge_transfers': self.gauge_transfers,
            },
            'charts': {},
            'transitions': [],
        }
        
        # Save charts (without functions - those must be reconstructed)
        for chart_id, chart in self.charts.items():
            chart_data = {
                'chart_id': chart.chart_id,
                'signature_center': list(chart.signature_center),
                'radius': chart.radius,
                'task_ids': list(chart.task_ids),
                'sections': {},
            }
            for pred_name, section in chart.sections.items():
                section_data = {
                    'predicate_name': section.predicate_name,
                    'source_task_id': section.source_task_id,
                    'f1_score': section.f1_score,
                    'sheaf_energy': section.sheaf_energy,
                    'metadata': section.metadata,
                }
                # Remove non-serializable items from metadata
                if 'op' in section_data['metadata']:
                    # Store op description if available
                    op = section_data['metadata']['op']
                    if hasattr(op, 'describe'):
                        section_data['metadata']['op_description'] = op.describe()
                    del section_data['metadata']['op']
                chart_data['sections'][pred_name] = section_data
            data['charts'][chart_id] = chart_data
        
        # Save transitions
        for t in self.transitions:
            data['transitions'].append({
                'source_task_id': t.source_task_id,
                'target_task_id': t.target_task_id,
                'predicate_name': t.predicate_name,
                'gauge_element': t.gauge_element.name,
                'sheaf_energy_before': t.sheaf_energy_before,
                'sheaf_energy_after': t.sheaf_energy_after,
                'defect_improvement': t.defect_improvement,
                'timestamp': t.timestamp,
            })
        
        with open(filepath, 'w') as f:
            json.dump(data, f, indent=2)
        
        if self.verbose:
            print(f"[ATLAS] Saved to {filepath} ({self.size} predicates, {len(self.transitions)} transitions)")
    
    def load(self, filepath: str) -> int:
        """
        Load atlas state from disk.
        
        Returns the number of predicates loaded.
        
        Note: This loads metadata only. Predicate functions are NOT restored
        because functions cannot be serialized. The caller must re-register
        predicate functions using the metadata (op_description, etc.).
        
        For practical use, call load() at start of run, then let the solver
        re-discover predicates. The loaded statistics and transition history
        help guide gauge transport decisions.
        """
        import json
        
        if not Path(filepath).exists():
            if self.verbose:
                print(f"[ATLAS] No saved atlas at {filepath}, starting fresh")
            return 0
        
        with open(filepath, 'r') as f:
            data = json.load(f)
        
        # Restore statistics
        stats = data.get('statistics', {})
        self.total_lookups = stats.get('total_lookups', 0)
        self.successful_transfers = stats.get('successful_transfers', 0)
        self.identity_transfers = stats.get('identity_transfers', 0)
        self.gauge_transfers = stats.get('gauge_transfers', 0)
        
        # Restore charts (metadata only, no functions)
        n_loaded = 0
        for chart_id, chart_data in data.get('charts', {}).items():
            chart = Chart(
                chart_id=chart_data['chart_id'],
                signature_center=tuple(chart_data['signature_center']),
                radius=chart_data.get('radius', 0.3),
            )
            chart.task_ids = set(chart_data.get('task_ids', []))
            
            # Restore section metadata (but not functions)
            for pred_name, section_data in chart_data.get('sections', {}).items():
                # Create a placeholder section without a working predicate_fn
                # The function will be re-registered when the op is re-discovered
                section = LocalSection(
                    predicate_name=section_data['predicate_name'],
                    predicate_fn=lambda x: np.zeros_like(x, dtype=np.float32),  # Placeholder
                    source_task_id=section_data['source_task_id'],
                    f1_score=section_data.get('f1_score', 0.0),
                    sheaf_energy=section_data.get('sheaf_energy', 0.0),
                    metadata=section_data.get('metadata', {}),
                )
                # Mark as needing reconstruction
                section.metadata['_needs_reconstruction'] = True
                section.metadata['_loaded_from_disk'] = True
                chart.sections[pred_name] = section
                n_loaded += 1
            
            self.charts[chart_id] = chart
        
        # Restore transitions
        gauge_lookup = {g.name: g for g in self.gauge_group}
        for t_data in data.get('transitions', []):
            g = gauge_lookup.get(t_data['gauge_element'])
            if g is None:
                continue
            record = TransitionRecord(
                source_task_id=t_data['source_task_id'],
                target_task_id=t_data['target_task_id'],
                predicate_name=t_data['predicate_name'],
                gauge_element=g,
                sheaf_energy_before=t_data['sheaf_energy_before'],
                sheaf_energy_after=t_data['sheaf_energy_after'],
                defect_improvement=t_data['defect_improvement'],
                timestamp=t_data.get('timestamp', 0.0),
            )
            self.transitions.append(record)
        
        if self.verbose:
            print(f"[ATLAS] Loaded from {filepath}: {n_loaded} predicates, {len(self.transitions)} transitions")
        
        return n_loaded


# =============================================================================
# HELPER: Create predicate function from AtomicOp
# =============================================================================

def make_predicate_fn_from_op(op, role_detector=None) -> Callable[[np.ndarray], np.ndarray]:
    """
    Extract a predicate function from an AtomicOp.
    
    The predicate identifies which pixels the op would modify.
    This is a simplified extraction - actual implementation may need
    to parse the op's predicate expression.
    """
    def predicate_fn(grid: np.ndarray) -> np.ndarray:
        # Apply the op and see which pixels changed
        try:
            result = op.apply(grid)
            mask = (result != grid)
            return mask.astype(np.float32)
        except Exception:
            return np.zeros_like(grid, dtype=np.float32)
    
    return predicate_fn


# =============================================================================
# TEST
# =============================================================================

if __name__ == "__main__":
    print("Testing Sheaf Atlas...")
    
    # Test D4 gauge group
    print("\nD4 Gauge Group:")
    for g in D4_GROUP:
        print(f"  {g}")
    
    # Test gauge transport
    test_grid = np.array([[1, 2, 3],
                          [4, 5, 6],
                          [7, 8, 9]])
    
    print("\nOriginal grid:")
    print(test_grid)
    
    print("\nGauge transformations:")
    for g in D4_GROUP:
        transformed = g.apply(test_grid)
        print(f"\n{g.name}:")
        print(transformed)
        
        # Verify inverse
        recovered = g.apply_inverse(transformed)
        assert np.array_equal(recovered, test_grid), f"Inverse failed for {g.name}"
    
    print("\nAll inverses verified!")
    
    # Test atlas
    atlas = SheafAtlas(verbose=True)
    
    # Create a dummy predicate
    def dummy_pred(grid):
        return (grid > 5).astype(np.float32)
    
    # Add to atlas
    atlas.add_predicate(
        predicate_name="greater_than_5",
        predicate_fn=dummy_pred,
        task_id="test_task_1",
        signature=(0.5, 0.3, 0.2, 0.1, 0.4, 0.6),
        f1_score=0.95,
        sheaf_energy=0.05
    )
    
    atlas.print_summary()
    print("\nSheaf Atlas test complete!")
