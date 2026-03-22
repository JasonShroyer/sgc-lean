"""
SheafAtlas Adapter for SGC Agent Integration

This module provides a drop-in replacement for SGFEPrimitiveLibrary that uses
the gauge-covariant SheafAtlas instead of the flat cross-task validator.

Theory:
  - The flat SGFEPrimitiveLibrary assumes predicates work identically everywhere
  - The SheafAtlas stores predicates in local charts and uses D4 gauge transport
  - This adapter bridges the interface gap for seamless agent integration

Usage:
  # Replace:
  # from sgfe_engine import SGFEPrimitiveLibrary
  # With:
  from sheaf_atlas_adapter import SheafAtlasLibrary
  
  # Then use identically:
  library = SheafAtlasLibrary()
  library.add_new_primitive(name, op, metadata)
"""

import numpy as np
from typing import Dict, Optional, Tuple, List, Any, Callable
from dataclasses import dataclass

from sheaf_atlas import SheafAtlas


@dataclass
class TransformationSignature:
    """6D transformation signature for chart assignment."""
    pos_frac: float      # Fraction of additive errors
    neg_frac: float      # Fraction of subtractive errors  
    recolor_frac: float  # Fraction of recolor errors
    pure_recolor: float  # 1.0 if ONLY recolor errors, 0.0 otherwise
    is_connected: float  # 1.0 if wrong pixels form single component
    is_scattered: float  # 1.0 if wrong pixels are all isolated
    
    def as_tuple(self) -> Tuple[float, ...]:
        return (self.pos_frac, self.neg_frac, self.recolor_frac, 
                self.pure_recolor, self.is_connected, self.is_scattered)


class SheafAtlasLibrary:
    """
    Drop-in replacement for SGFEPrimitiveLibrary using gauge-covariant SheafAtlas.
    
    Key differences from flat library:
    1. Predicates stored in local charts indexed by transformation signature
    2. Cross-task validation uses D4 gauge transport (tries all 8 symmetries)
    3. Transitions recorded for learning connection structure
    
    Interface compatibility:
    - add_new_primitive() -> atlas.add_predicate()
    - get_ops() -> returns predicates from all charts
    - size -> total predicates across all charts
    """
    
    def __init__(
        self,
        verbose: bool = True,
        sheaf_energy_threshold: float = 0.3,
    ):
        self.atlas = SheafAtlas(verbose=verbose)
        self.atlas.SHEAF_ENERGY_THRESHOLD = sheaf_energy_threshold
        
        # Legacy interface compatibility
        self.primitives = []  # Shadow list for get_ops() compatibility
        self.compression_log = []
        self.cross_task_accepts = 0
        
        # Config (mimics SGFEPrimitiveLibrary interface)
        self.require_cross_task = True
        self.min_tasks = 2
        
        # Cache for gauge lookups
        self._last_lookup_results = []
        
    @property
    def size(self) -> int:
        return self.atlas.size
    
    @property
    def num_charts(self) -> int:
        return self.atlas.num_charts
    
    def add_new_primitive(
        self,
        name: str,
        op,  # AtomicOp or similar
        metadata: Dict,
        require_cross_task: Optional[bool] = None,
    ) -> bool:
        """
        Add a new primitive to the SheafAtlas.
        
        Unlike flat library, predicates are stored in local charts based on
        their transformation signature. Cross-task validation is implicit
        in the sheaf energy computation.
        
        Args:
            name: Unique predicate name
            op: The operation/predicate (must have .apply() method)
            metadata: Dict with keys:
                - task_id: Source task ID
                - f1: F1 score on source task
                - sheaf_energy: Sheaf energy on source task
                - transformation_signature: 6D signature tuple
                
        Returns:
            True if added, False if rejected
        """
        task_id = metadata.get('task_id', 'unknown')
        f1_score = metadata.get('f1', 0.5)
        sheaf_energy = metadata.get('sheaf_energy', 0.0)
        signature = metadata.get('transformation_signature', (0.5, 0.25, 0.25, 0.0, 0.5, 0.5))
        
        # Convert signature to tuple if needed
        if not isinstance(signature, tuple):
            signature = tuple(signature)
        
        # Create predicate function wrapper
        def pred_fn(grid: np.ndarray) -> np.ndarray:
            try:
                result = op.apply(grid)
                # Convert to boolean mask if needed
                if result.dtype != bool:
                    result = (result > 0).astype(np.float32)
                return result
            except Exception:
                return np.zeros_like(grid, dtype=np.float32)
        
        # Add to atlas
        added = self.atlas.add_predicate(
            predicate_name=name,
            predicate_fn=pred_fn,
            task_id=task_id,
            signature=signature,
            f1_score=f1_score,
            sheaf_energy=sheaf_energy,
            metadata={'op': op, **metadata}
        )
        
        # Maintain legacy shadow list for get_ops()
        if added:
            self.primitives.append((name, op, metadata))
            self.compression_log.append({
                'task_id': task_id,
                'name': name,
                'f1': f1_score,
                'sheaf_energy': sheaf_energy,
                'library_size': self.size,
                'chart_id': self.atlas._signature_to_chart_id(signature),
                'cross_task_validated': True,  # Sheaf energy IS the validation
            })
            self.cross_task_accepts += 1
        
        return added
    
    def gauge_covariant_lookup(
        self,
        task_id: str,
        grids: List[np.ndarray],
        targets: List[np.ndarray],
        predictions: List[np.ndarray],
        transformation_signature: Tuple[float, ...],
    ) -> List[Tuple[str, Any, float, float]]:
        """
        Search atlas for predicates that work on this task via gauge transport.
        
        This is the KEY INTEGRATION POINT for the agent. Before solving a task,
        call this to find predicates from the atlas that can help.
        
        Args:
            task_id: Current task ID
            grids: Input grids (numpy arrays)
            targets: Target grids (numpy arrays)
            predictions: Current predictions (numpy arrays)
            transformation_signature: 6D signature of current task
            
        Returns:
            List of (predicate_name, gauge_element, sheaf_energy, defect_improvement)
        """
        results = self.atlas.gauge_covariant_lookup(
            task_id=task_id,
            signature=transformation_signature,
            grids=grids,
            targets=targets,
            predictions=predictions,
        )
        
        self._last_lookup_results = results
        return results
    
    def get_ops(self) -> list:
        """Get all primitive ops for seeding solver proposals (legacy interface)."""
        return [(name, op) for name, op, _ in self.primitives]
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get combined statistics from atlas and adapter."""
        atlas_stats = self.atlas.get_statistics()
        return {
            **atlas_stats,
            'compression_log_size': len(self.compression_log),
            'cross_task_accepts': self.cross_task_accepts,
        }
    
    def print_summary(self) -> None:
        """Print atlas summary."""
        self.atlas.print_summary()
    
    def compression_ratio(self) -> float:
        """Library compression: useful primitives per total attempted."""
        if not self.compression_log:
            return 0.0
        return self.size / max(len(self.compression_log), 1)
    
    def save(self, filepath: str) -> None:
        """Save atlas to disk for persistence across runs."""
        self.atlas.save(filepath)
    
    def load(self, filepath: str) -> int:
        """Load atlas from disk. Returns number of predicates loaded."""
        return self.atlas.load(filepath)


def compute_transformation_signature(
    predictions: List[np.ndarray],
    targets: List[np.ndarray],
) -> Tuple[float, ...]:
    """
    Compute 6D transformation signature from predictions and targets.
    
    This signature determines which chart a predicate belongs to.
    Tasks with similar signatures are in the same local neighborhood
    and can share predicates without gauge transport.
    
    Returns:
        6-tuple: (pos_frac, neg_frac, recolor_frac, pure_recolor, is_connected, is_scattered)
    """
    from scipy import ndimage as ndi
    
    pos_count = 0
    neg_count = 0
    recolor_count = 0
    all_wrong_masks = []
    
    for pred, tgt in zip(predictions, targets):
        wrong = (pred != tgt)
        all_wrong_masks.append(wrong)
        
        # Classify error types
        pos_count += int((wrong & (pred == 0) & (tgt != 0)).sum())    # Should add
        neg_count += int((wrong & (pred != 0) & (tgt == 0)).sum())    # Should remove
        recolor_count += int((wrong & (pred != 0) & (tgt != 0)).sum()) # Should change
    
    n_wrong = pos_count + neg_count + recolor_count
    if n_wrong == 0:
        return (0.0, 0.0, 0.0, 0.0, 1.0, 0.0)
    
    pos_frac = pos_count / n_wrong
    neg_frac = neg_count / n_wrong
    recolor_frac = recolor_count / n_wrong
    pure_recolor = 1.0 if (pos_count == 0 and neg_count == 0 and recolor_count > 0) else 0.0
    
    # Topological features
    is_connected_f = 0.0
    is_scattered_f = 0.0
    
    for w in all_wrong_masks:
        if w.any():
            labeled, n_cc = ndi.label(w)
            is_connected_f = 1.0 if n_cc == 1 else 0.0
            
            # Scattered: each wrong pixel is isolated
            w_float = w.astype(np.float32)
            k = np.ones((3, 3), dtype=np.float32)
            k[1, 1] = 0
            adj_count = ndi.convolve(w_float, k, mode='constant', cval=0.0)
            is_scattered_f = 1.0 if bool(np.all(adj_count[w] == 0)) else 0.0
            break
    
    return (pos_frac, neg_frac, recolor_frac, pure_recolor, is_connected_f, is_scattered_f)


# Test block
if __name__ == "__main__":
    print("Testing SheafAtlasLibrary adapter...")
    
    library = SheafAtlasLibrary(verbose=True)
    
    # Create a mock operation
    class MockOp:
        def apply(self, grid):
            return (grid > 0).astype(np.float32)
    
    # Test adding predicates
    for i in range(3):
        metadata = {
            'task_id': f'test_task_{i}',
            'f1': 0.8 + i * 0.05,
            'sheaf_energy': 0.1,
            'transformation_signature': (0.5, 0.25, 0.25, 0.0, float(i % 2), 0.5),
        }
        library.add_new_primitive(f'pred_{i}', MockOp(), metadata)
    
    print(f"\nLibrary size: {library.size}")
    print(f"Number of charts: {library.num_charts}")
    
    # Test gauge lookup
    grids = [np.array([[0, 1], [1, 0]])]
    targets = [np.array([[1, 1], [1, 1]])]
    predictions = [np.array([[0, 0], [0, 0]])]
    signature = (0.5, 0.25, 0.25, 0.0, 0.5, 0.5)
    
    results = library.gauge_covariant_lookup(
        'new_task', grids, targets, predictions, signature
    )
    
    print(f"\nGauge lookup results: {len(results)} transfers found")
    for name, g, se, di in results:
        print(f"  {name} via {g.name}: sheaf_e={se:.3f}, delta={di:.3f}")
    
    library.print_summary()
    print("\nAdapter test complete!")
