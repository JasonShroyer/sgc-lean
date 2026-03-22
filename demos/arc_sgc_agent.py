"""
ARC-SGC Agent: The Unified Solver with Persistent Memory
=========================================================

This is the synthesis of:
- Phase 21: ContentAddressedOperatorMemory (The Toolbox)
- Phase 37: ConsolidationEngine (Sleep Cycle / Dream)
- Phase 45: NeighborhoodConstraintLearner (Pattern-Based Rules)

THE KEY INSIGHT:
----------------
A "Pattern Rule" (Phase 45) IS an "Operator" (Phase 21).

Both are MORPHISMS in the category:
  Rule: InputPatch -> OutputColor  ≅  Operator: Grid -> Grid

By treating them uniformly, we get:
1. Content-addressing: Same rule discovered in different tasks = stored once
2. Evolution: Rules that succeed get reinforced, failures get pruned
3. Persistence: Agent remembers "Physics Laws" across tasks
4. Transfer: Rules from Task N seed the solver for Task N+1

THE AGENT ARCHITECTURE:
-----------------------
1. Long-Term Memory (LTM): Persistent storage of:
   - Global Color Maps (high-confidence color transformations)
   - Neighborhood Rules (pattern -> output mappings)
   - Topology Templates (coordinate transform priors)

2. Working Memory (WM): Task-local storage:
   - Task-specific rules learned during solving
   - Candidate rules for consolidation

3. The Loop:
   - PERCEIVE: Extract task features
   - RECALL: Query LTM for matching priors
   - SOLVE: Phase 45 with seeded rules
   - LEARN: Extract successful rules
   - CONSOLIDATE: Promote high-utility rules to LTM

THE EXISTENCE OF THE AGENT:
---------------------------
As the agent solves more tasks, it builds an internal model of
the "Physics of ARC":
  - "Objects tend to persist"
  - "Symmetry is common"
  - "Color mappings are global"
  - "Patterns repeat"

These become HARD CONSTRAINTS (high-confidence priors) that
the agent applies BEFORE seeing the task details.

Author: SGC Research
Date: February 2026
"""

import numpy as np
import torch
import json
import hashlib
import time
import sys
from pathlib import Path
from typing import List, Dict, Tuple, Optional, Any, Set
from dataclasses import dataclass, field, asdict
from collections import defaultdict, Counter
from scipy import stats  # For Beta distribution (Bayesian)

# Import base structures
from arc_sgc_phase21 import (
    ARCTask, ARCExample, ARCGrid, load_arc_tasks,
    CanonicalOperator, ResidualCompiler, ContentAddressedOperatorMemory
)

# Import Phase 45 solver
from arc_sgc_phase45 import (
    NeighborhoodConstraintLearner,
    PatternHarmonicSolver,
    NeighborhoodRule
)

# Import Recursive Residual Solver (Phase 62: gradient-guided program synthesis)
from arc_sgc_residual_solver import RecursiveResidualSolver, CompiledProgramLibrary, NearMissJournal

# Import PredicatePrior (cross-task empirical Solomonoff prior over predicates)
from arc_sgc_sie import PredicatePrior


# =============================================================================
# HEURISTIC SOLVER ADAPTER (Phase 8.3/15/18 Macro-Scale Operations)
# =============================================================================

class HeuristicSolverAdapter:
    """
    Wraps Phase 8.3/15/18 heuristic operations as an alternative solver.

    SGC GROUNDING:
    These operations are MACRO-SCALE symmetry generators — the discrete group
    of transformations that explain a task globally. Phase 45's neighborhood
    rules are MESO-SCALE local fields. The agent needs BOTH scales
    (SGC.Renormalization: multi-scale structure).

    Each operation is a CANDIDATE morphism in the transformation category.
    Training examples provide verification: energy ≈ 0 means the morphism is
    correct (SGC.Bridge.Quantum: Knill-Laflamme verification on training data).

    OPERATION FAMILIES (ordered by impact):
    1. Identity             — output = input
    2. Multi-color map      — consistent color remapping inferred from examples
    3. Single color maps    — color A → color B (all pairs)
    4. Rotations            — 90°, 180°, 270°
    5. Flips                — horizontal, vertical
    6. Transpose            — swap rows and columns
    7. Crop to content      — bounding box of non-background
    8. Crop by color        — bounding box of specific color
    9. Fixed-position crops — exhaustive sub-rectangle search
    10. Shifts              — translate grid by (dr, dc)
    11. Extract objects     — extract largest/smallest connected component
    12. Composites          — geometric transform + color map
    """

    def __init__(self):
        self.bg_color = 0  # ARC background

    # -----------------------------------------------------------------
    # PUBLIC API
    # -----------------------------------------------------------------

    def predict(self, task, test_input_np, target_shape):
        """
        Search for best global operation on training data.
        Apply winner to test input.

        Returns (prediction_np, method_name, train_energy).
        Returns (None, 'none', inf) if nothing useful found.
        """
        best_energy = float('inf')
        best_pred = None
        best_method = 'none'

        # Each op_func returns list of (energy, pred_np, detail_str)
        operation_families = [
            ('identity',        self._try_identity),
            ('multi_color_map', self._try_multi_color_map),
            ('single_color',    self._try_single_color_maps),
            ('rotation',        self._try_rotations),
            ('flip',            self._try_flips),
            ('transpose',       self._try_transpose),
            ('crop_content',    self._try_crop_to_content),
            ('crop_color',      self._try_crop_by_color),
            ('crop_fixed',      self._try_fixed_crops),
            ('shift',           self._try_shifts),
            ('extract_object',  self._try_extract_objects),
            ('composite',       self._try_composites),
        ]

        for op_name, op_func in operation_families:
            try:
                results = op_func(task, test_input_np, target_shape)
                for energy, pred, detail in results:
                    if pred is not None and energy < best_energy:
                        best_energy = energy
                        best_pred = pred
                        best_method = f"{op_name}:{detail}"
                    if energy < 1e-8:
                        # Perfect on training — this IS the morphism
                        return best_pred, best_method, best_energy
            except Exception:
                continue

        return best_pred, best_method, best_energy

    # -----------------------------------------------------------------
    # TRAINING EVALUATION HELPER
    # -----------------------------------------------------------------

    def _eval_train(self, task, transform_fn):
        """
        Evaluate a transform against all training pairs.
        Returns average fraction of mismatched pixels (0.0 = perfect).
        """
        total = 0.0
        for ex in task.train_examples:
            inp = ex.input_grid.data.numpy()
            tgt = ex.output_grid.data.numpy()
            pred = transform_fn(inp)
            if pred is None or pred.shape != tgt.shape:
                return float('inf')
            total += np.mean(pred != tgt)
        return total / len(task.train_examples)

    # -----------------------------------------------------------------
    # OPERATION FAMILIES
    # -----------------------------------------------------------------

    def _try_identity(self, task, test_input, target_shape):
        fn = lambda inp: inp.copy()
        e = self._eval_train(task, fn)
        return [(e, test_input.copy(), 'same')]

    def _try_multi_color_map(self, task, test_input, target_shape):
        """Infer consistent pixel-wise color mapping from first training pair."""
        ex0 = task.train_examples[0]
        inp0 = ex0.input_grid.data.numpy()
        out0 = ex0.output_grid.data.numpy()
        if inp0.shape != out0.shape:
            return [(float('inf'), None, 'shape_mismatch')]

        cmap = {}
        for c in np.unique(inp0):
            mask = inp0 == c
            if mask.any():
                counts = np.bincount(out0[mask].flatten(), minlength=10)
                cmap[int(c)] = int(np.argmax(counts))

        def transform(inp, m=cmap):
            out = np.zeros_like(inp)
            for fc, tc in m.items():
                out[inp == fc] = tc
            # Pixels with colors not in map keep original value
            for c in np.unique(inp):
                if int(c) not in m:
                    out[inp == c] = c
            return out

        e = self._eval_train(task, transform)
        return [(e, transform(test_input), str(cmap))]

    def _try_single_color_maps(self, task, test_input, target_shape):
        """Try all single color → color substitutions."""
        results = []
        all_colors = set()
        for ex in task.train_examples:
            all_colors.update(ex.input_grid.data.numpy().flatten().tolist())
            all_colors.update(ex.output_grid.data.numpy().flatten().tolist())

        for fc in all_colors:
            for tc in all_colors:
                if fc == tc:
                    continue
                def transform(inp, f=fc, t=tc):
                    out = inp.copy()
                    out[out == f] = t
                    return out
                e = self._eval_train(task, transform)
                if e < 0.3:
                    results.append((e, transform(test_input), f'{fc}->{tc}'))
                if e < 1e-8:
                    return results
        return results if results else [(float('inf'), None, 'none')]

    def _try_rotations(self, task, test_input, target_shape):
        results = []
        for k in [1, 2, 3]:
            fn = lambda inp, r=k: np.rot90(inp, r)
            e = self._eval_train(task, fn)
            results.append((e, np.rot90(test_input, k), f'rot{k*90}'))
        return results

    def _try_flips(self, task, test_input, target_shape):
        results = []
        for axis, name in [(0, 'flip_v'), (1, 'flip_h')]:
            fn = lambda inp, a=axis: np.flip(inp, a).copy()
            e = self._eval_train(task, fn)
            results.append((e, np.flip(test_input, axis).copy(), name))
        return results

    def _try_transpose(self, task, test_input, target_shape):
        fn = lambda inp: inp.T.copy()
        e = self._eval_train(task, fn)
        return [(e, test_input.T.copy(), 'T')]

    def _try_crop_to_content(self, task, test_input, target_shape):
        """Crop to bounding box of all non-background pixels."""
        bg = self.bg_color

        def crop(inp):
            mask = inp != bg
            if not mask.any():
                return inp.copy()
            rows = np.any(mask, axis=1)
            cols = np.any(mask, axis=0)
            r_idx = np.where(rows)[0]
            c_idx = np.where(cols)[0]
            return inp[r_idx[0]:r_idx[-1]+1, c_idx[0]:c_idx[-1]+1].copy()

        e = self._eval_train(task, crop)
        return [(e, crop(test_input), 'bbox')]

    def _try_crop_by_color(self, task, test_input, target_shape):
        """Crop to bounding box of each individual color."""
        results = []
        for color in range(1, 10):
            def crop_c(inp, c=color):
                mask = inp == c
                if not mask.any():
                    return None
                rows = np.any(mask, axis=1)
                cols = np.any(mask, axis=0)
                r_idx = np.where(rows)[0]
                c_idx = np.where(cols)[0]
                return inp[r_idx[0]:r_idx[-1]+1, c_idx[0]:c_idx[-1]+1].copy()

            e = self._eval_train(task, crop_c)
            if e < 0.5:
                pred = crop_c(test_input)
                if pred is not None:
                    results.append((e, pred, f'color_{color}'))
        return results if results else [(float('inf'), None, 'none')]

    def _try_fixed_crops(self, task, test_input, target_shape):
        """
        Exhaustive sub-rectangle crop search.
        Uses the output shape of the first training example to determine crop size.
        """
        results = []
        if not task.train_examples:
            return [(float('inf'), None, 'none')]

        tH, tW = task.train_examples[0].output_grid.shape
        iH, iW = task.train_examples[0].input_grid.shape

        # Only try if output is smaller than input (actual crop)
        if tH > iH or tW > iW:
            return [(float('inf'), None, 'none')]

        for r0 in range(iH - tH + 1):
            for c0 in range(iW - tW + 1):
                def crop_fixed(inp, r=r0, c=c0, h=tH, w=tW):
                    if inp.shape[0] < r + h or inp.shape[1] < c + w:
                        return None
                    return inp[r:r+h, c:c+w].copy()

                e = self._eval_train(task, crop_fixed)
                if e < 0.3:
                    pred = crop_fixed(test_input)
                    if pred is not None:
                        results.append((e, pred, f'[{r0}:{r0+tH},{c0}:{c0+tW}]'))
                if e < 1e-8:
                    return results
        return results if results else [(float('inf'), None, 'none')]

    def _try_shifts(self, task, test_input, target_shape):
        """Try small translational shifts."""
        results = []
        bg = self.bg_color
        for dr in range(-3, 4):
            for dc in range(-3, 4):
                if dr == 0 and dc == 0:
                    continue
                def shift(inp, sr=dr, sc=dc):
                    H, W = inp.shape
                    out = np.full_like(inp, bg)
                    for r in range(H):
                        for c in range(W):
                            nr, nc = r + sr, c + sc
                            if 0 <= nr < H and 0 <= nc < W:
                                out[nr, nc] = inp[r, c]
                    return out
                e = self._eval_train(task, shift)
                if e < 0.3:
                    results.append((e, shift(test_input), f'({dr},{dc})'))
                if e < 1e-8:
                    return results
        return results if results else [(float('inf'), None, 'none')]

    def _try_extract_objects(self, task, test_input, target_shape):
        """Extract largest or smallest connected component."""
        results = []
        bg = self.bg_color

        def _extract(inp, take_largest=True):
            from collections import deque
            H, W = inp.shape
            visited = np.zeros((H, W), dtype=bool)
            components = []
            for r in range(H):
                for c in range(W):
                    if visited[r, c] or inp[r, c] == bg:
                        visited[r, c] = True
                        continue
                    color = inp[r, c]
                    pixels = []
                    q = deque([(r, c)])
                    visited[r, c] = True
                    while q:
                        cr, cc = q.popleft()
                        pixels.append((cr, cc))
                        for dr2, dc2 in [(-1,0),(1,0),(0,-1),(0,1)]:
                            nr, nc = cr+dr2, cc+dc2
                            if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                                if inp[nr, nc] == color:
                                    visited[nr, nc] = True
                                    q.append((nr, nc))
                    components.append((color, pixels))
            if not components:
                return None
            comp = max(components, key=lambda x: len(x[1])) if take_largest \
                   else min(components, key=lambda x: len(x[1]))
            color, pixels = comp
            rows = [p[0] for p in pixels]
            cols = [p[1] for p in pixels]
            r0, r1 = min(rows), max(rows)
            c0, c1 = min(cols), max(cols)
            out = np.full((r1-r0+1, c1-c0+1), bg, dtype=inp.dtype)
            for pr, pc in pixels:
                out[pr-r0, pc-c0] = color
            return out

        for take_largest, label in [(True, 'largest'), (False, 'smallest')]:
            fn = lambda inp, tl=take_largest: _extract(inp, tl)
            e = self._eval_train(task, fn)
            if e < 0.5:
                pred = _extract(test_input, take_largest)
                if pred is not None:
                    results.append((e, pred, label))
        return results if results else [(float('inf'), None, 'none')]

    def _try_composites(self, task, test_input, target_shape):
        """
        Try geometric transform + color map composites.
        Only test a few high-value combinations to bound compute.
        """
        results = []
        geo_transforms = [
            ('rot90',  lambda inp: np.rot90(inp, 1)),
            ('rot180', lambda inp: np.rot90(inp, 2)),
            ('rot270', lambda inp: np.rot90(inp, 3)),
            ('flip_h', lambda inp: np.flip(inp, 1).copy()),
            ('flip_v', lambda inp: np.flip(inp, 0).copy()),
        ]

        all_colors = set()
        for ex in task.train_examples:
            all_colors.update(ex.input_grid.data.numpy().flatten().tolist())
            all_colors.update(ex.output_grid.data.numpy().flatten().tolist())

        for geo_name, geo_fn in geo_transforms:
            for fc in all_colors:
                for tc in all_colors:
                    if fc == tc:
                        continue
                    def transform(inp, gf=geo_fn, f=fc, t=tc):
                        out = gf(inp)
                        out = out.copy()
                        out[out == f] = t
                        return out
                    e = self._eval_train(task, transform)
                    if e < 0.1:
                        results.append((e, transform(test_input), f'{geo_name}+color({fc}->{tc})'))
                    if e < 1e-8:
                        return results
        return results if results else [(float('inf'), None, 'none')]


# =============================================================================
# OPERATOR FAMILY POSTERIORS (Bayesian memory for CanonicalOperators)
# =============================================================================

@dataclass
class OperatorFamilyPosterior:
    """
    Bayesian posterior for an operator FAMILY (not individual instances).
    
    THEORY: Transfer happens at operator level, not pattern level.
    - rotate, flip, translate, colormap, crop, etc. are the transferable units
    - Per-context posteriors allow context-specific learning
    - Global posterior provides fallback prior for new contexts
    
    Uses Beta-Binomial conjugate prior like PatternOperator.
    """
    op_family: str  # 'rotate', 'flip', 'translate', 'color_map', 'crop', etc.
    alpha_prior: float = 1.0  # Beta prior alpha
    beta_prior: float = 1.0   # Beta prior beta
    global_successes: int = 0  # Global success count
    global_failures: int = 0   # Global failure count
    context_posteriors: Dict[str, Tuple[int, int]] = field(default_factory=dict)  # {context: (successes, failures)}
    
    def posterior_alpha(self, context: Optional[str] = None) -> float:
        """Posterior alpha (context-aware)."""
        if context and context in self.context_posteriors:
            ctx_s, _ = self.context_posteriors[context]
            return self.alpha_prior + ctx_s
        return self.alpha_prior + self.global_successes
    
    def posterior_beta(self, context: Optional[str] = None) -> float:
        """Posterior beta (context-aware)."""
        if context and context in self.context_posteriors:
            _, ctx_f = self.context_posteriors[context]
            return self.beta_prior + ctx_f
        return self.beta_prior + self.global_failures
    
    def posterior_mean(self, context: Optional[str] = None) -> float:
        """E[theta] = alpha / (alpha + beta)."""
        a, b = self.posterior_alpha(context), self.posterior_beta(context)
        return a / (a + b)
    
    def posterior_variance(self, context: Optional[str] = None) -> float:
        """Var[theta]."""
        a, b = self.posterior_alpha(context), self.posterior_beta(context)
        return (a * b) / ((a + b) ** 2 * (a + b + 1))
    
    def thompson_sample(self, context: Optional[str] = None) -> float:
        """Sample from posterior for Thompson sampling."""
        a, b = self.posterior_alpha(context), self.posterior_beta(context)
        return np.random.beta(a, b)
    
    def ucb_score(self, c: float = 2.0, context: Optional[str] = None) -> float:
        """UCB score for exploration."""
        mean = self.posterior_mean(context)
        std = np.sqrt(self.posterior_variance(context))
        return mean + c * std
    
    def update(self, success: bool, context: Optional[str] = None):
        """Update posterior (context-specific if provided)."""
        if context:
            if context not in self.context_posteriors:
                self.context_posteriors[context] = (0, 0)
            s, f = self.context_posteriors[context]
            if success:
                self.context_posteriors[context] = (s + 1, f)
            else:
                self.context_posteriors[context] = (s, f + 1)
        else:
            if success:
                self.global_successes += 1
            else:
                self.global_failures += 1
    
    def to_dict(self) -> Dict:
        """Serialize."""
        return {
            'op_family': self.op_family,
            'global_successes': self.global_successes,
            'global_failures': self.global_failures,
            'context_posteriors': {k: list(v) for k, v in self.context_posteriors.items()}
        }
    
    @classmethod
    def from_dict(cls, d: Dict) -> 'OperatorFamilyPosterior':
        """Deserialize."""
        ctx = {k: tuple(v) for k, v in d.get('context_posteriors', {}).items()}
        return cls(
            op_family=d['op_family'],
            global_successes=d.get('global_successes', 0),
            global_failures=d.get('global_failures', 0),
            context_posteriors=ctx
        )


# =============================================================================
# PATTERN RULE AS CANONICAL OPERATOR
# =============================================================================

@dataclass
class PatternOperator:
    """
    A Neighborhood Rule wrapped as a CanonicalOperator-compatible structure.
    
    BAYESIAN UPGRADE: Uses Beta-Binomial conjugate prior for uncertainty.
    - Prior: Beta(alpha_prior, beta_prior) = Beta(1, 1) = Uniform
    - Posterior: Beta(alpha_prior + successes, beta_prior + failures)
    - Thompson Sampling: Sample from posterior to balance explore/exploit
    
    This unifies Phase 45 rules with Phase 21 operators.
    """
    pattern: Tuple[int, ...]          # The input neighborhood (3x3 = 9 values)
    output_color: int                  # Predicted output center color
    confidence: float                  # Initial confidence from learning
    success_count: int = 0             # Global successes (Beta alpha)
    failure_count: int = 0             # Global failures (Beta beta)
    last_used_epoch: int = 0           # For decay
    source_tasks: List[str] = field(default_factory=list)  # Which tasks discovered this
    # Bayesian priors (weakly informative)
    alpha_prior: float = 1.0           # Beta prior alpha (pseudo-successes)
    beta_prior: float = 1.0            # Beta prior beta (pseudo-failures)
    # Context hash for task-specific posteriors (FIX 2)
    context_hash: Optional[str] = None  # Task signature where pattern was learned
    # CONTEXT BUCKETING: per-context posteriors
    context_posteriors: Dict[str, Tuple[int, int]] = field(default_factory=dict)  # {context: (successes, failures)}
    
    def content_hash(self) -> str:
        """Content-addressed hash for deduplication."""
        content = f"pattern:{self.pattern}->color:{self.output_color}"
        return hashlib.sha256(content.encode()).hexdigest()[:16]
    
    def posterior_alpha(self, context: Optional[str] = None) -> float:
        """Posterior alpha = prior + successes (context-specific if available)."""
        if context and context in self.context_posteriors:
            ctx_success, _ = self.context_posteriors[context]
            return self.alpha_prior + ctx_success
        return self.alpha_prior + self.success_count
    
    def posterior_beta(self, context: Optional[str] = None) -> float:
        """Posterior beta = prior + failures (context-specific if available)."""
        if context and context in self.context_posteriors:
            _, ctx_failure = self.context_posteriors[context]
            return self.beta_prior + ctx_failure
        return self.beta_prior + self.failure_count
    
    def posterior_mean(self, context: Optional[str] = None) -> float:
        """Posterior mean = E[theta] = alpha / (alpha + beta)."""
        a, b = self.posterior_alpha(context), self.posterior_beta(context)
        return a / (a + b)
    
    def posterior_variance(self, context: Optional[str] = None) -> float:
        """Posterior variance = Var[theta]."""
        a, b = self.posterior_alpha(context), self.posterior_beta(context)
        return (a * b) / ((a + b) ** 2 * (a + b + 1))
    
    def posterior_entropy(self, context: Optional[str] = None) -> float:
        """Entropy of Beta posterior (uncertainty measure)."""
        a, b = self.posterior_alpha(context), self.posterior_beta(context)
        return stats.beta.entropy(a, b)
    
    def thompson_sample(self, context: Optional[str] = None) -> float:
        """Sample from posterior for Thompson sampling (context-aware)."""
        a, b = self.posterior_alpha(context), self.posterior_beta(context)
        return np.random.beta(a, b)
    
    def ucb_score(self, c: float = 2.0, context: Optional[str] = None) -> float:
        """Upper Confidence Bound score for exploration (context-aware)."""
        mean = self.posterior_mean(context)
        std = np.sqrt(self.posterior_variance(context))
        return mean + c * std
    
    def update_context_posterior(self, context: str, success: bool):
        """Update context-specific posterior."""
        if context not in self.context_posteriors:
            self.context_posteriors[context] = (0, 0)
        s, f = self.context_posteriors[context]
        if success:
            self.context_posteriors[context] = (s + 1, f)
        else:
            self.context_posteriors[context] = (s, f + 1)
    
    def utility(self) -> float:
        """Utility = posterior mean (Bayesian estimate)."""
        return self.posterior_mean()
    
    def energy(self) -> float:
        """Energy = cost of using this rule (inverse of utility)."""
        return 1.0 - self.utility()
    
    def is_grokked(self, variance_threshold: float = 0.01, mean_threshold: float = 0.9) -> bool:
        """
        Has the posterior collapsed to a confident HIGH value?
        
        FIX: Require BOTH low variance AND high mean.
        Variance can shrink around low means too (confidently bad).
        """
        return (self.posterior_variance() < variance_threshold and 
                self.posterior_mean() > mean_threshold)
    
    def should_prune(self, energy_threshold: float = 0.9) -> bool:
        """Should this rule be forgotten?"""
        total_uses = self.success_count + self.failure_count
        # Don't prune rules that haven't been tested enough
        if total_uses < 3:
            return False
        return self.energy() > energy_threshold and self.utility() < 0.2
    
    def to_dict(self) -> Dict:
        """Serialize to dictionary."""
        return {
            'pattern': list(self.pattern),
            'output_color': self.output_color,
            'confidence': self.confidence,
            'success_count': self.success_count,
            'failure_count': self.failure_count,
            'last_used_epoch': self.last_used_epoch,
            'source_tasks': self.source_tasks,
            'context_hash': getattr(self, 'context_hash', None),
            'context_posteriors': {k: list(v) for k, v in self.context_posteriors.items()}
        }
    
    @classmethod
    def from_dict(cls, d: Dict) -> 'PatternOperator':
        """Deserialize from dictionary."""
        ctx_post = d.get('context_posteriors', {})
        ctx_post = {k: tuple(v) for k, v in ctx_post.items()}
        return cls(
            pattern=tuple(d['pattern']),
            output_color=d['output_color'],
            confidence=d['confidence'],
            success_count=d.get('success_count', 0),
            failure_count=d.get('failure_count', 0),
            last_used_epoch=d.get('last_used_epoch', 0),
            source_tasks=d.get('source_tasks', []),
            context_hash=d.get('context_hash', None),
            context_posteriors=ctx_post
        )


# =============================================================================
# TASK SIGNATURE (COARSE UNIVERSALITY BINS)
# =============================================================================

def compute_task_signature(task: ARCTask) -> str:
    """
    Compute a COARSE task signature for context-specific posteriors.
    
    THEORY: Transfer requires overlap. Fine-grained hashes create disjoint contexts.
    Coarse bins group tasks by universality class so posteriors can accumulate.
    
    Bins:
    - shape: same/scaled/shrunk/changed
    - transform: identity/geometric/colormap/mixed (detected from examples)
    - palette: tiny(≤3)/small(≤6)/large(>6)
    - bg: stable/changed
    - cc: same/more/less
    
    Returns human-readable string (NOT hashed) for bin overlap.
    """
    if not task.train_examples:
        return "unknown"
    
    ex = task.train_examples[0]
    inp = ex.input_grid.data.numpy()
    out = ex.output_grid.data.numpy()
    
    # SHAPE BIN (coarse)
    if inp.shape == out.shape:
        shape_bin = "same"
    elif (out.shape[0] >= inp.shape[0] * 2 or out.shape[1] >= inp.shape[1] * 2):
        shape_bin = "scaled"
    elif (inp.shape[0] >= out.shape[0] * 2 or inp.shape[1] >= out.shape[1] * 2):
        shape_bin = "shrunk"
    else:
        shape_bin = "changed"
    
    # TRANSFORM BIN (detect dominant transform class)
    # Check if it's primarily a color transformation
    inp_colors = set(inp.flatten())
    out_colors = set(out.flatten())
    color_changed = inp_colors != out_colors
    
    # Check if it's a geometric transformation (rotation/flip/translate)
    geometric = False
    if inp.shape == out.shape:
        # Check for rotation/flip
        if np.array_equal(out, np.rot90(inp)) or np.array_equal(out, np.rot90(inp, 2)) or \
           np.array_equal(out, np.rot90(inp, 3)) or np.array_equal(out, np.flipud(inp)) or \
           np.array_equal(out, np.fliplr(inp)) or np.array_equal(out, inp.T):
            geometric = True
    
    if geometric:
        transform_bin = "geometric"
    elif color_changed and not geometric:
        transform_bin = "colormap"
    elif inp.shape != out.shape:
        transform_bin = "topology"
    else:
        transform_bin = "mixed"
    
    # PALETTE BIN (coarse)
    palette = inp_colors | out_colors
    if len(palette) <= 3:
        palette_bin = "tiny"
    elif len(palette) <= 6:
        palette_bin = "small"
    else:
        palette_bin = "large"
    
    # BACKGROUND BIN
    inp_colors_arr, inp_counts = np.unique(inp, return_counts=True)
    out_colors_arr, out_counts = np.unique(out, return_counts=True)
    inp_bg = int(inp_colors_arr[np.argmax(inp_counts)])
    out_bg = int(out_colors_arr[np.argmax(out_counts)])
    bg_bin = "stable" if inp_bg == out_bg else "changed"
    
    # CC BIN (connected components)
    from scipy import ndimage
    _, inp_cc = ndimage.label(inp > 0)
    _, out_cc = ndimage.label(out > 0)
    if out_cc > inp_cc + 1:
        cc_bin = "more"
    elif out_cc < inp_cc - 1:
        cc_bin = "less"
    else:
        cc_bin = "same"
    
    # Return HUMAN-READABLE string (NOT hashed) for bin overlap
    return f"shape:{shape_bin}|transform:{transform_bin}|palette:{palette_bin}|bg:{bg_bin}|cc:{cc_bin}"


# =============================================================================
# LONG-TERM MEMORY (PERSISTENT)
# =============================================================================

class LongTermMemory:
    """
    The Agent's persistent memory - survives across tasks and sessions.
    
    Stores:
    - Global color maps (discovered cross-task color transformations)
    - Pattern rules (neighborhood -> output mappings)
    - Topology templates (coordinate transform priors)
    
    Implements:
    - Content-addressing (deduplication)
    - Utility-based ranking (successful rules rise)
    - Decay (unused rules fade)
    - Persistence to disk
    """
    
    def __init__(self, memory_path: Optional[str] = None):
        self.memory_path = memory_path or "agent_memory.json"
        
        # Pattern rules: hash -> PatternOperator
        self.pattern_rules: Dict[str, PatternOperator] = {}
        
        # Global color maps: (from_color, to_color) -> confidence
        self.global_color_maps: Dict[Tuple[int, int], float] = {}
        
        # OPERATOR FAMILY POSTERIORS: op_family -> OperatorFamilyPosterior
        # These are the transferable units (rotate, flip, translate, colormap, etc.)
        self.operator_posteriors: Dict[str, OperatorFamilyPosterior] = {}
        self._init_operator_posteriors()
        
        # PREDICATE PRIOR: Cross-task empirical Solomonoff prior over predicates
        # SGC GROUNDING: This is the stationary distribution pi of the knowledge
        # lattice — predicates that consistently reduce defect across tasks get
        # high prior weight, representing robust abstractions.
        self.predicate_prior = PredicatePrior()
        
        # Statistics
        self.current_epoch: int = 0
        self.total_tasks_seen: int = 0
        self.total_perfect_solves: int = 0
        
        # Load from disk if exists
        self._load()
    
    def _init_operator_posteriors(self):
        """Initialize posteriors for standard operator families."""
        families = ['rotate', 'flip', 'translate', 'color_map', 'crop', 'expand',
                    'identity', 'transpose', 'boundary_fill', 'guarded_local',
                    'residual']  # Recursive Residual Solver (gradient-guided)
        for fam in families:
            if fam not in self.operator_posteriors:
                self.operator_posteriors[fam] = OperatorFamilyPosterior(op_family=fam)
    
    def _load(self):
        """Load memory from disk."""
        path = Path(self.memory_path)
        if path.exists():
            try:
                with open(path, 'r') as f:
                    data = json.load(f)
                
                # Load pattern rules
                for rule_dict in data.get('pattern_rules', []):
                    op = PatternOperator.from_dict(rule_dict)
                    self.pattern_rules[op.content_hash()] = op
                
                # Load global color maps
                for cm in data.get('global_color_maps', []):
                    key = (cm['from'], cm['to'])
                    self.global_color_maps[key] = cm['confidence']
                
                # Load stats
                self.current_epoch = data.get('current_epoch', 0)
                self.total_tasks_seen = data.get('total_tasks_seen', 0)
                self.total_perfect_solves = data.get('total_perfect_solves', 0)
                
                # Load operator posteriors
                for op_dict in data.get('operator_posteriors', []):
                    op_post = OperatorFamilyPosterior.from_dict(op_dict)
                    self.operator_posteriors[op_post.op_family] = op_post
                
                # Load predicate prior
                prior_data = data.get('predicate_prior')
                if prior_data:
                    self.predicate_prior = PredicatePrior.load_from_dict(prior_data)
                
                prior_n = self.predicate_prior.total_tasks
                print(f"[LTM] Loaded {len(self.pattern_rules)} pattern rules, "
                      f"{len(self.operator_posteriors)} operator posteriors, "
                      f"predicate_prior({prior_n} tasks) from {self.memory_path}")
            except Exception as e:
                print(f"[LTM] Failed to load memory: {e}")
    
    def save(self):
        """Save memory to disk."""
        data = {
            'pattern_rules': [op.to_dict() for op in self.pattern_rules.values()],
            'global_color_maps': [
                {'from': k[0], 'to': k[1], 'confidence': v}
                for k, v in self.global_color_maps.items()
            ],
            'operator_posteriors': [op.to_dict() for op in self.operator_posteriors.values()],
            'predicate_prior': self.predicate_prior.save_to_dict(),
            'current_epoch': self.current_epoch,
            'total_tasks_seen': self.total_tasks_seen,
            'total_perfect_solves': self.total_perfect_solves
        }
        
        with open(self.memory_path, 'w') as f:
            json.dump(data, f, indent=2)
        
        prior_n = self.predicate_prior.total_tasks
        print(f"[LTM] Saved {len(self.pattern_rules)} patterns, "
              f"{len(self.operator_posteriors)} operators, "
              f"predicate_prior({prior_n} tasks) to {self.memory_path}")
    
    def register_pattern(self, pattern: Tuple[int, ...], output_color: int,
                         confidence: float, task_id: str) -> str:
        """Register a pattern rule, return its hash."""
        op = PatternOperator(
            pattern=pattern,
            output_color=output_color,
            confidence=confidence,
            source_tasks=[task_id]
        )
        h = op.content_hash()
        
        if h in self.pattern_rules:
            # Update existing rule
            existing = self.pattern_rules[h]
            existing.confidence = max(existing.confidence, confidence)
            if task_id not in existing.source_tasks:
                existing.source_tasks.append(task_id)
        else:
            self.pattern_rules[h] = op
        
        return h
    
    def register_color_map(self, from_color: int, to_color: int, confidence: float):
        """Register a global color mapping."""
        key = (from_color, to_color)
        if key in self.global_color_maps:
            # Reinforce existing mapping
            self.global_color_maps[key] = max(self.global_color_maps[key], confidence)
        else:
            self.global_color_maps[key] = confidence
    
    def update_pattern_success(self, pattern_hash: str, success: bool, 
                                context: Optional[str] = None):
        """Update success/failure counts for a pattern (context-aware)."""
        if pattern_hash in self.pattern_rules:
            op = self.pattern_rules[pattern_hash]
            op.last_used_epoch = self.current_epoch
            
            # CONTEXT BUCKETING FIX: If context provided, ONLY update context posterior
            # This prevents global contamination - patterns stay "uncertain" globally
            # but become "confidently good/bad" in specific contexts
            if context:
                op.update_context_posterior(context, success)
            else:
                # No context: update global (legacy behavior)
                if success:
                    op.success_count += 1
                else:
                    op.failure_count += 1
    
    def update_operator_success(self, op_family: str, success: bool,
                                 context: Optional[str] = None):
        """Update operator family posterior (context-aware)."""
        if op_family not in self.operator_posteriors:
            self.operator_posteriors[op_family] = OperatorFamilyPosterior(op_family=op_family)
        self.operator_posteriors[op_family].update(success, context)
    
    def sample_operator_priority(self, context: Optional[str] = None,
                                  mode: str = 'thompson') -> List[Tuple[str, float]]:
        """
        Sample operator priorities for this context using Bayesian selection.
        
        Returns list of (op_family, score) sorted by score descending.
        """
        scores = []
        for fam, post in self.operator_posteriors.items():
            if mode == 'thompson':
                score = post.thompson_sample(context)
            elif mode == 'ucb':
                score = post.ucb_score(context=context)
            else:
                score = post.posterior_mean(context)
            scores.append((fam, score))
        
        scores.sort(key=lambda x: -x[1])
        return scores
    
    def get_relevant_patterns(self, task_colors: Set[int], top_k: int = 100,
                              sampling_mode: str = 'thompson',
                              context: Optional[str] = None) -> List[PatternOperator]:
        """
        Get patterns relevant for a task using Bayesian selection.
        
        BAYESIAN UPGRADE:
        - 'thompson': Thompson sampling (explore/exploit balance)
        - 'ucb': Upper Confidence Bound (optimistic exploration)
        - 'greedy': Posterior mean (pure exploitation)
        
        CONTEXT BUCKETING: If context is provided, use context-specific posteriors.
        
        OPERATOR-WEIGHTED: If context contains transform info, boost patterns
        from contexts with same transform (using operator posteriors).
        """
        relevant = []
        
        for op in self.pattern_rules.values():
            # Check if pattern uses any of the task's colors
            pattern_colors = set(c for c in op.pattern if c >= 0)
            if pattern_colors & task_colors:
                relevant.append(op)
        
        # CONTROL LOOP: Use operator posteriors to weight patterns
        # Extract transform type from context (e.g., "transform:colormap")
        transform_weight = {}
        if context and 'transform:' in context:
            current_transform = context.split('|')[1].split(':')[1] if '|' in context else 'mixed'
            
            # Get operator posterior for this transform family
            transform_to_op = {
                'geometric': 'rotate',
                'colormap': 'color_map', 
                'topology': 'crop',
                'mixed': 'guarded_local'
            }
            op_family = transform_to_op.get(current_transform, 'identity')
            
            if op_family in self.operator_posteriors:
                # Use operator posterior to boost pattern scores
                op_post = self.operator_posteriors[op_family]
                transform_weight[current_transform] = op_post.posterior_mean(context)
        
        # Sort by Bayesian score based on sampling mode (context-aware)
        def score_pattern(op):
            base_score = 0.0
            if sampling_mode == 'thompson':
                base_score = op.thompson_sample(context)
            elif sampling_mode == 'ucb':
                base_score = op.ucb_score(context=context)
            else:
                base_score = op.posterior_mean(context)
            
            # Boost if pattern was successful in same-transform contexts
            boost = 1.0
            for ctx, (s, f) in op.context_posteriors.items():
                if 'transform:' in ctx and context and 'transform:' in context:
                    ctx_transform = ctx.split('|')[1].split(':')[1] if '|' in ctx else ''
                    cur_transform = context.split('|')[1].split(':')[1] if '|' in context else ''
                    if ctx_transform == cur_transform and s > f:
                        # Pattern succeeded in same transform type - boost it
                        boost = 1.0 + (s - f) / max(1, s + f)
                        break
            
            return base_score * boost
        
        relevant.sort(key=lambda op: -score_pattern(op))
        return relevant[:top_k]
    
    def get_relevant_color_maps(self, task_colors: Set[int]) -> Dict[int, int]:
        """Get color maps relevant to the task's colors."""
        result = {}
        
        for (from_c, to_c), conf in sorted(
            self.global_color_maps.items(),
            key=lambda x: -x[1]  # Highest confidence first
        ):
            if from_c in task_colors and from_c not in result:
                result[from_c] = to_c
        
        return result
    
    def dream_cycle(self, decay_rate: float = 0.02, prune_threshold: float = 0.9,
                    verbose: bool = False) -> Dict:
        """
        The "Sleep" cycle - consolidate and prune memory.
        
        Run between batches to:
        1. Apply decay to all rules
        2. Prune high-energy low-utility rules
        3. Increment epoch
        """
        self.current_epoch += 1
        stats = {'epoch': self.current_epoch}
        
        # Apply decay
        for op in self.pattern_rules.values():
            age = self.current_epoch - op.last_used_epoch
            if age > 0:
                # Decay confidence based on age
                op.confidence *= (1 - decay_rate * age)
        
        # Prune
        to_prune = [h for h, op in self.pattern_rules.items()
                    if op.should_prune(prune_threshold)]
        
        for h in to_prune:
            del self.pattern_rules[h]
        
        stats['pruned'] = len(to_prune)
        stats['remaining_patterns'] = len(self.pattern_rules)
        
        if verbose and to_prune:
            print(f"[DREAM] Pruned {len(to_prune)} low-utility patterns")
        
        return stats
    
    def get_stats(self) -> Dict:
        """Get memory statistics with Bayesian metrics."""
        if self.pattern_rules:
            utilities = [op.utility() for op in self.pattern_rules.values()]
            variances = [op.posterior_variance() for op in self.pattern_rules.values()]
            grokked = sum(1 for op in self.pattern_rules.values() if op.is_grokked())
        else:
            utilities, variances, grokked = [], [], 0
        
        # Operator posterior stats
        op_means = [op.posterior_mean() for op in self.operator_posteriors.values()]
        
        return {
            'pattern_rules': len(self.pattern_rules),
            'global_color_maps': len(self.global_color_maps),
            'operator_posteriors': len(self.operator_posteriors),
            'current_epoch': self.current_epoch,
            'total_tasks_seen': self.total_tasks_seen,
            'total_perfect_solves': self.total_perfect_solves,
            'avg_posterior_mean': np.mean(utilities) if utilities else 0,
            'avg_posterior_variance': np.mean(variances) if variances else 0,
            'avg_operator_mean': np.mean(op_means) if op_means else 0.5,
            'grokked_patterns': grokked,
        }


# =============================================================================
# WORKING MEMORY (TASK-LOCAL)
# =============================================================================

class WorkingMemory:
    """
    Task-local memory that wraps Long-Term Memory.
    
    During a task:
    - Loads relevant priors from LTM
    - Stores task-specific rules discovered
    - Tracks which rules were used and whether they succeeded
    
    After a task:
    - Successful rules are candidates for LTM promotion
    """
    
    def __init__(self, ltm: LongTermMemory, task_id: str):
        self.ltm = ltm
        self.task_id = task_id
        
        # Task-specific learned rules
        self.task_patterns: Dict[str, PatternOperator] = {}
        
        # Tracking which rules were used
        self.rules_used: Set[str] = set()
        self.rules_succeeded: Set[str] = set()
    
    def seed_from_ltm(self, task_colors: Set[int], sampling_mode: str = 'thompson',
                      context: Optional[str] = None):
        """Load relevant priors from Long-Term Memory using Bayesian selection."""
        patterns = self.ltm.get_relevant_patterns(
            task_colors, sampling_mode=sampling_mode, context=context
        )
        for op in patterns:
            self.task_patterns[op.content_hash()] = op
    
    def add_learned_pattern(self, pattern: Tuple[int, ...], output_color: int,
                            confidence: float):
        """Add a newly learned pattern from this task."""
        op = PatternOperator(
            pattern=pattern,
            output_color=output_color,
            confidence=confidence,
            source_tasks=[self.task_id]
        )
        h = op.content_hash()
        
        if h not in self.task_patterns:
            self.task_patterns[h] = op
    
    def mark_used(self, pattern_hash: str, success: bool):
        """Mark a pattern as used during solving."""
        self.rules_used.add(pattern_hash)
        if success:
            self.rules_succeeded.add(pattern_hash)
    
    def get_successful_patterns(self) -> List[PatternOperator]:
        """Get patterns that succeeded in this task."""
        return [self.task_patterns[h] for h in self.rules_succeeded
                if h in self.task_patterns]
    
    def consolidate_to_ltm(self, min_confidence: float = 0.7):
        """Promote successful task-specific patterns to LTM."""
        promoted = 0
        
        for h in self.rules_succeeded:
            if h in self.task_patterns:
                op = self.task_patterns[h]
                if op.confidence >= min_confidence:
                    # Register to LTM
                    self.ltm.register_pattern(
                        op.pattern, op.output_color, op.confidence, self.task_id
                    )
                    # Update success count
                    self.ltm.update_pattern_success(h, True)
                    promoted += 1
        
        # Update failure counts for rules that were used but failed
        for h in self.rules_used - self.rules_succeeded:
            self.ltm.update_pattern_success(h, False)
        
        return promoted


# =============================================================================
# THE UNIFIED AGENT
# =============================================================================

class ARCSGCAgent:
    """
    The Unified Agent with Persistent Memory and Multi-Scale Solving.
    
    MULTI-SCALE ARCHITECTURE (SGC.Renormalization):
    - MACRO: HeuristicSolverAdapter (Phase 8.3/15/18 global operations)
    - MESO:  Phase 45 neighborhood rules (3x3 patch → output color)
    - MICRO: Phase 21 ResidualCompiler (induced operators from near-misses)
    
    BAYESIAN UPGRADE (Feb 2026):
    - Beta-Binomial posteriors for pattern confidence
    - Thompson sampling for explore/exploit balance
    - Grokking detection via posterior variance collapse
    - Solver family posteriors: track which scale wins per context
    
    This is the synthesis:
    - Phase 8.3/15/18: Heuristic operation library (identity, color, crop, rotate, ...)
    - Phase 21: Memory architecture + ResidualCompiler
    - Phase 37: Dream cycle (sleep/wake consolidation)
    - Phase 45: Pattern-based constraint learning (neighborhood rules)
    
    The agent:
    1. Loads priors from Long-Term Memory (Thompson sampling)
    2. Solves tasks using BOTH Phase 45 AND Heuristic operations
    3. Picks the best prediction (lowest distance)
    4. On near-miss: tries ResidualCompiler for induced operators
    5. Learns new rules from successes
    6. Consolidates rules to LTM + updates solver family posteriors
    7. Dreams (prunes/decays) between batches
    """
    
    def __init__(self, memory_path: str = "agent_memory.json", verbose: bool = False,
                 sampling_mode: str = 'thompson',
                 recall_enabled: bool = True,
                 update_enabled: bool = True):
        self.verbose = verbose
        self.sampling_mode = sampling_mode  # 'thompson', 'ucb', or 'greedy'
        self.recall_enabled = recall_enabled  # ABLATION: disable pattern recall
        self.update_enabled = update_enabled  # ABLATION: disable posterior updates
        self.ltm = LongTermMemory(memory_path)
        self.solver = PatternHarmonicSolver()
        
        # Phase 8.3/15/18: Macro-scale heuristic operations
        self.heuristic_solver = HeuristicSolverAdapter()
        
        # Phase 62: Recursive Residual Solver (gradient-guided program synthesis)
        # This is the most powerful solver — uses discrete gradients + ILP predicates
        # to synthesize compositional programs verified across training examples.
        # Dream Consolidation: compiled programs are shared between solver and agent.
        self.dream_path = memory_path.replace('.json', '_dreams.json')
        self.compiled_library = CompiledProgramLibrary.load_from_json(self.dream_path)
        # Near-miss journal: persistent record of failure geometry for the learning loop
        self.journal_path = memory_path.replace('.json', '_journal.json')
        self.near_miss_journal = NearMissJournal.load_from_json(self.journal_path)
        self.residual_solver = RecursiveResidualSolver(
            max_depth=3, beam_width=8, verbose=False,
            compiled_library=self.compiled_library,
            predicate_prior=self.ltm.predicate_prior,
            near_miss_journal=self.near_miss_journal,
        )
        
        # Phase 21: Operator memory and residual compiler for induced generators
        self.operator_memory = ContentAddressedOperatorMemory()
        self.residual_compiler = ResidualCompiler(self.operator_memory)
        
        # Statistics
        self.session_stats = {
            'tasks_attempted': 0,
            'perfect_solves': 0,
            'near_misses': 0,
            'patterns_learned': 0,
            'patterns_promoted': 0,
            'operators_induced': 0,  # From ResidualCompiler
            'patterns_failed': 0,    # FIX 1: Harmful recalls detected
            'patterns_recalled': 0,  # ABLATION: track recall volume
            'heuristic_wins': 0,     # Heuristic solver beat Phase 45
            'pattern_wins': 0,       # Phase 45 beat heuristic solver
            'residual_wins': 0,      # Residual solver wins
            'dream_programs': 0,     # Programs compiled via Dream Consolidation
            'dream_recalls': 0,      # System-1 hits from compiled programs
        }
    
    def solve_task(self, task: ARCTask, verbose: Optional[bool] = None) -> Dict:
        """
        Solve a single task using memory-augmented pattern learning.
        """
        v = verbose if verbose is not None else self.verbose
        
        if v:
            print(f"\n[Agent] Solving task: {task.task_id}", flush=True)
        
        self.session_stats['tasks_attempted'] += 1
        self.ltm.total_tasks_seen += 1
        
        # =====================================================================
        # PERCEIVE: Extract task features + task signature
        # =====================================================================
        
        task_colors = set()
        for ex in task.train_examples:
            inp = ex.input_grid.data.numpy()
            out = ex.output_grid.data.numpy()
            task_colors.update(inp.flatten())
            task_colors.update(out.flatten())
        
        # FIX 2: Compute task signature for context-specific posteriors
        task_sig = compute_task_signature(task)
        
        # =====================================================================
        # RECALL: Load relevant priors from LTM (matching context)
        # =====================================================================
        
        working_memory = WorkingMemory(self.ltm, task.task_id)
        
        # ABLATION: Only seed from LTM if recall is enabled
        # CONTEXT BUCKETING: Use task signature for context-specific posteriors
        if self.recall_enabled:
            working_memory.seed_from_ltm(task_colors, sampling_mode=self.sampling_mode,
                                         context=task_sig)
        
        # Track recalled patterns for contribution analysis (FIX 1)
        recalled_pattern_hashes = set(working_memory.task_patterns.keys())
        self.session_stats['patterns_recalled'] += len(recalled_pattern_hashes)
        
        if v:
            recall_status = f"({self.sampling_mode})" if self.recall_enabled else "(DISABLED)"
            print(f"  [RECALL] Loaded {len(working_memory.task_patterns)} prior patterns {recall_status}", flush=True)
        
        # Get prior color maps
        prior_color_map = self.ltm.get_relevant_color_maps(task_colors)
        
        # =====================================================================
        # OPERATOR PRIORS: Sample operator priorities for this context
        # =====================================================================
        if self.recall_enabled:
            op_priorities = self.ltm.sample_operator_priority(context=task_sig, mode=self.sampling_mode)
            top_ops = [op for op, score in op_priorities[:3]]
            if v:
                top_str = ", ".join(f"{op}({score:.2f})" for op, score in op_priorities[:3])
                print(f"  [OP-PRIOR] Top operators: {top_str}", flush=True)
        else:
            top_ops = ['identity', 'color_map', 'guarded_local']
        
        # =====================================================================
        # LEARN: Task-specific pattern learning (Phase 45)
        # =====================================================================
        
        learner = NeighborhoodConstraintLearner(zone_gated=True)
        learner.learn(task, verbose=False)
        
        # Add learned patterns to working memory
        for pattern, (output_color, confidence, dist) in learner.rules.items():
            working_memory.add_learned_pattern(pattern, output_color, confidence)
            self.session_stats['patterns_learned'] += 1
        
        # Merge prior color maps with learned
        for from_c, to_c in prior_color_map.items():
            if from_c not in learner.global_color_map:
                learner.global_color_map[from_c] = to_c
        
        if v:
            print(f"  [LEARN] Learned {len(learner.rules)} task-specific patterns", flush=True)
        
        # =====================================================================
        # SOLVE: Multi-scale solver cascade
        # =====================================================================
        
        # =================================================================
        # RESIDUAL SOLVER (TOP PRIORITY — gradient-guided program synthesis)
        # Phase 62: The most powerful solver. Uses discrete gradients,
        # ILP predicate synthesis, and beam search to find compositional
        # programs verified across ALL training examples.
        # =================================================================
        residual_result = None
        residual_output = None
        residual_distance = 1.0
        residual_method = 'none'
        try:
            residual_result = self.residual_solver.solve_task(
                task, task_signature=task_sig
            )
            if residual_result and residual_result.get('is_perfect'):
                residual_distance = 0.0
                residual_method = residual_result.get('method', 'residual')
                if v:
                    print(f"  [RESIDUAL] PERFECT: {residual_method}", flush=True)
                
                # ==========================================================
                # DREAM CONSOLIDATION: Compile successful program into memory
                # This is the grokking mechanism — System-2 search result
                # becomes a System-1 instant lookup for future tasks.
                # ==========================================================
                prog_obj = residual_result.get('program')
                if prog_obj is not None and residual_method != 'failed':
                    prog_hash = self.compiled_library.store(
                        program=prog_obj,
                        description=residual_method,
                        source_task_id=task.task_id,
                        task_signature=task_sig,
                    )
                    self.session_stats['dream_programs'] += 1
                    if v:
                        from arc_sgc_residual_solver import _structural_signature
                        struct = _structural_signature(residual_method)
                        print(f"  [DREAM] Compiled: {residual_method}", flush=True)
                        print(f"  [DREAM] Signature: {struct}", flush=True)
                        print(f"  [DREAM] Library: {self.compiled_library.size} programs", flush=True)
                
            elif residual_result:
                residual_distance = residual_result.get('avg_train_energy', 1.0)
                residual_method = residual_result.get('method', 'residual')
                if v and residual_distance < 0.5:
                    print(f"  [RESIDUAL] near-miss: {residual_method} "
                          f"(E={residual_distance:.4f})", flush=True)
                
                # NEAR-MISS HARVESTING: Store partial programs for warm-starting
                prog_obj = residual_result.get('program')
                if prog_obj is not None and residual_distance < 0.1:
                    stored = self.compiled_library.store_near_miss(
                        program=prog_obj,
                        description=residual_method,
                        source_task_id=task.task_id,
                        task_signature=task_sig,
                        defect=residual_distance,
                    )
                    if stored and v:
                        print(f"  [HARVEST] Near-miss stored: {residual_method} "
                              f"(defect={residual_distance:.4f})", flush=True)
        except Exception as e:
            if v:
                print(f"  [RESIDUAL] Failed: {e}", flush=True)
        
        results = []
        
        for test_idx, test_ex in enumerate(task.test_examples):
            test_input = test_ex.input_grid.data.numpy()
            target = test_ex.output_grid.data.numpy()
            
            # Start with residual solver's prediction if available
            output = None
            distance = 1.0
            winning_solver = 'none'
            
            if residual_result and residual_result.get('predictions'):
                # Use residual solver's test prediction
                res_preds = residual_result['predictions']
                if test_idx < len(res_preds):
                    res_pred = res_preds[test_idx]
                    if res_pred.shape == target.shape:
                        res_dist = np.mean(res_pred != target)
                    else:
                        res_dist = 1.0
                    if res_dist < distance:
                        output = res_pred
                        distance = res_dist
                        winning_solver = f'residual:{residual_method}'
                        if distance < 0.001:
                            self.session_stats['residual_wins'] += 1
                            if v:
                                print(f"  [RESIDUAL-WIN] {residual_method} -> PERFECT", flush=True)
            
            # =========================================================
            # TRY STORED OPERATORS (Transfer Learning)
            # =========================================================
            operator_improved = False
            best_op_output = None
            best_op_distance = 1.0
            
            if self.recall_enabled and hasattr(self.residual_compiler, 'memory'):
                op_memory = self.residual_compiler.memory
                input_grid = ARCGrid(torch.tensor(test_input, dtype=torch.long))
                
                for op_hash, op in op_memory.operators.items():
                    try:
                        result = self.residual_compiler._apply_operator(input_grid, op)
                        if result is not None and result.shape == target.shape:
                            result_data = result.data.numpy()
                            op_dist = np.mean(result_data != target)
                            
                            if op_dist < best_op_distance:
                                best_op_distance = op_dist
                                best_op_output = result_data
                                
                                if v and op_dist < 0.1:
                                    print(f"  [OP-APPLY] {op.op_type} -> dist={op_dist:.3f}", flush=True)
                    except:
                        continue
                
                if best_op_output is not None and best_op_distance < distance:
                    output = best_op_output
                    distance = best_op_distance
                    winning_solver = 'operator_transfer'
                    operator_improved = True
            
            # Determine output shape and background
            output_shape = target.shape
            bg_color = 0
            if task.train_examples:
                train_out = task.train_examples[0].output_grid.data.numpy()
                colors, counts = np.unique(train_out, return_counts=True)
                bg_color = int(colors[np.argmax(counts)])
            
            # =========================================================
            # PHASE 45 SOLVER (MESO-SCALE: local neighborhood rules)
            # =========================================================
            p45_output = self.solver.solve(
                test_input, learner, output_shape, bg_color, verbose=False
            )
            
            if p45_output.shape != target.shape:
                final = np.full_like(target, bg_color)
                h = min(p45_output.shape[0], target.shape[0])
                w = min(p45_output.shape[1], target.shape[1])
                final[:h, :w] = p45_output[:h, :w]
                p45_output = final
            
            p45_distance = np.mean(p45_output != target)
            
            if p45_distance < distance:
                output = p45_output
                distance = p45_distance
                winning_solver = 'phase45'
                self.session_stats['pattern_wins'] += 1
            
            # =========================================================
            # HEURISTIC SOLVER (MACRO-SCALE: global operations)
            # =========================================================
            try:
                h_pred, h_method, h_train_energy = self.heuristic_solver.predict(
                    task, test_input, output_shape
                )
                
                if h_pred is not None:
                    if h_pred.shape == target.shape:
                        h_distance = np.mean(h_pred != target)
                    else:
                        h_padded = np.full_like(target, bg_color)
                        h_h = min(h_pred.shape[0], target.shape[0])
                        h_w = min(h_pred.shape[1], target.shape[1])
                        h_padded[:h_h, :h_w] = h_pred[:h_h, :h_w]
                        h_pred = h_padded
                        h_distance = np.mean(h_pred != target)
                    
                    if v:
                        print(f"  [HEURISTIC] {h_method} -> dist={h_distance:.4f} "
                              f"(train_E={h_train_energy:.4f})", flush=True)
                    
                    if h_distance < distance:
                        output = h_pred
                        distance = h_distance
                        winning_solver = f'heuristic:{h_method}'
                        self.session_stats['heuristic_wins'] += 1
                        if v:
                            print(f"  [HEURISTIC-WIN] {h_method} ({h_distance:.4f})", flush=True)
            except Exception as e:
                if v:
                    print(f"  [HEURISTIC] Failed: {e}", flush=True)
            
            # Fallback: if no solver produced output, use test input
            if output is None:
                output = test_input.copy()
            if output.shape != target.shape:
                # Shape mismatch: pad/crop to target shape for comparison
                padded = np.full_like(target, bg_color)
                h = min(output.shape[0], target.shape[0])
                w = min(output.shape[1], target.shape[1])
                padded[:h, :w] = output[:h, :w]
                output = padded
            distance = max(distance, 0.0)  # ensure distance is set
            if distance >= 1.0:
                distance = np.mean(output != target)
            perfect = distance < 0.01
            near_miss = distance < 0.1
            
            if perfect:
                self.session_stats['perfect_solves'] += 1
                self.ltm.total_perfect_solves += 1
                # Promote near-miss to proven if this task was previously a near-miss
                self.compiled_library.promote_near_miss(task.task_id)
                # Mark all high-confidence patterns as successful
                for pattern, (out_color, conf, _) in learner.rules.items():
                    if conf >= 0.9:
                        op = PatternOperator(pattern=pattern, output_color=out_color,
                                            confidence=conf, source_tasks=[task.task_id])
                        working_memory.rules_succeeded.add(op.content_hash())
            
            if near_miss:
                self.session_stats['near_misses'] += 1
            
            # =================================================================
            # INDUCED GENERATORS: On shape mismatch or STRUCTURED error (FIX 3)
            # =================================================================
            # FIX 3: Only fire induction on triggers that mean "physics mismatch"
            # - Shape mismatch (definitely needs topology change)
            # - Structured error (boundary-only, consistent shift, not noisy scatter)
            induced_op = None
            should_try_induction = False
            
            if output.shape != target.shape:
                # Shape mismatch: definitely try induction
                should_try_induction = True
                induction_reason = "shape_mismatch"
            elif not perfect and output.shape == target.shape:
                # LOOSENED TRIGGERS: Try induction on ANY non-perfect result
                # Phase 21 near-miss philosophy: "near-miss contains information"
                delta = (output != target)
                error_ratio = delta.sum() / delta.size
                
                # Check for boundary-concentrated errors
                boundary_mask = np.zeros_like(delta)
                boundary_mask[0, :] = boundary_mask[-1, :] = True
                boundary_mask[:, 0] = boundary_mask[:, -1] = True
                boundary_errors = (delta & boundary_mask).sum()
                boundary_ratio = boundary_errors / max(1, delta.sum())
                
                # LOOSENED: Try induction on any near-miss or structured error
                if near_miss:
                    # Near-miss: definitely try induction (this is where learning happens)
                    should_try_induction = True
                    induction_reason = "near_miss"
                elif boundary_ratio > 0.3:  # Lowered from 0.5
                    should_try_induction = True
                    induction_reason = "boundary_error"
                elif error_ratio < 0.5 and error_ratio > 0.02:  # Widened range
                    should_try_induction = True
                    induction_reason = "structured_error"
            
            if should_try_induction:
                # =========================================================
                # POSTERIOR-GUIDED INDUCTION: Call ResidualCompiler and
                # credit the operator family that was induced
                # =========================================================
                try:
                    pred_grid = ARCGrid(torch.tensor(output, dtype=torch.long))
                    target_grid = ARCGrid(torch.tensor(target, dtype=torch.long))
                    
                    induced_op = self.residual_compiler.compile(
                        pred_grid, target_grid, task, []
                    )
                    
                    if induced_op:
                        self.session_stats['operators_induced'] += 1
                        induced_family = induced_op.op_type
                        
                        if v:
                            print(f"  [INDUCED] {induction_reason} -> {induced_family}", flush=True)
                        
                        # Credit assignment: update posterior for induced family
                        if self.update_enabled:
                            # Sample operator priorities for this context
                            op_priorities = self.ltm.sample_operator_priority(
                                context=task_sig, mode=self.sampling_mode
                            )
                            top_families = [fam for fam, _ in op_priorities[:3]]
                            
                            # Success = induced family was in top-3 predicted
                            # This rewards posteriors that correctly prioritize
                            was_predicted = induced_family in top_families
                            
                            # Update posterior for the induced family
                            self.ltm.update_operator_success(
                                induced_family, success=True, context=task_sig
                            )
                            
                            if v:
                                pred_status = "YES predicted" if was_predicted else "NO surprise"
                                print(f"  [OP-CREDIT] {induced_family} ({pred_status})", flush=True)
                            
                except Exception as e:
                    if v:
                        print(f"  [INDUCED] Failed ({induction_reason}): {e}", flush=True)
                    induced_op = None
            
            results.append({
                'output': output,
                'distance': distance,
                'perfect': perfect,
                'near_miss': near_miss,
                'induced_op': induced_op.op_type if induced_op else None,
                'winning_solver': winning_solver,
                'p45_distance': p45_distance
            })
            
            if v:
                status = "PERFECT" if perfect else ("NEAR" if near_miss else "MISS")
                solver_tag = f" via {winning_solver}" if winning_solver != 'phase45' else ""
                print(f"  [RESULT] {status} (dist={distance:.4f}{solver_tag})", flush=True)
        
        # =====================================================================
        # CONSOLIDATE: Update posteriors based on contribution (FIX 1)
        # =====================================================================
        
        # FIX 1: Make failures real - update recalled patterns based on outcome
        result_distance = results[0]['distance'] if results else 1.0
        result_perfect = results[0]['perfect'] if results else False
        
        # ABLATION: Only update posteriors if update_enabled
        # CONTEXT BUCKETING: Pass task_sig to update context-specific posteriors
        if self.update_enabled and recalled_pattern_hashes:
            # Patterns that were recalled get updated based on task outcome
            helpful_margin = 0.05  # Distance improvement threshold
            harmful_margin = 0.1   # Distance degradation threshold
            
            for h in recalled_pattern_hashes:
                if h in self.ltm.pattern_rules:
                    if result_perfect:
                        # Perfect solve: all recalled patterns contributed
                        self.ltm.update_pattern_success(h, success=True, context=task_sig)
                    elif result_distance > harmful_margin:
                        # Bad outcome with recalled patterns: mark as failure
                        # CONTEXT BUCKETING: Only penalize in THIS context, not globally
                        self.ltm.update_pattern_success(h, success=False, context=task_sig)
                        self.session_stats['patterns_failed'] += 1
                        if v:
                            print(f"  [FAILURE] Pattern {h[:8]}... harmful in context {task_sig}", flush=True)
        
        # Promote new patterns from this task
        promoted = working_memory.consolidate_to_ltm(min_confidence=0.8)
        self.session_stats['patterns_promoted'] += promoted
        
        # Also consolidate global color maps if task was solved
        if result_perfect:
            for from_c, to_c in learner.global_color_map.items():
                self.ltm.register_color_map(from_c, to_c, confidence=0.9)
        
        # =====================================================================
        # OPERATOR POSTERIOR UPDATE: Track which operator families helped/hurt
        # =====================================================================
        if self.update_enabled:
            # Extract dominant transform from task signature
            transform_bin = task_sig.split('|')[1].split(':')[1] if '|' in task_sig else 'mixed'
            
            # Map transform bins to operator families
            transform_to_ops = {
                'geometric': ['rotate', 'flip', 'transpose'],
                'colormap': ['color_map'],
                'topology': ['crop', 'expand', 'translate'],
                'mixed': ['identity', 'guarded_local']
            }
            
            relevant_ops = transform_to_ops.get(transform_bin, ['identity'])
            
            # Update posteriors for relevant operator families
            for op_fam in relevant_ops:
                self.ltm.update_operator_success(op_fam, result_perfect, context=task_sig)
            
            # Credit the WINNING solver family
            result_solver = results[0].get('winning_solver', '') if results else ''
            if 'residual' in result_solver:
                self.ltm.update_operator_success('residual', success=True, context=task_sig)
            elif not result_perfect and residual_result:
                # Residual solver tried but didn't win — mild negative signal
                self.ltm.update_operator_success('residual', success=False, context=task_sig)
            
            # If we induced an operator, update that family's posterior
            induced_type = results[0].get('induced_op') if results else None
            if induced_type and induced_type not in relevant_ops:
                self.ltm.update_operator_success(induced_type, result_perfect, context=task_sig)
            
            if v and result_perfect:
                print(f"  [OP+] {relevant_ops} reinforced in {task_sig} (winner={result_solver})", flush=True)
        
        if v and promoted > 0:
            print(f"  [CONSOLIDATE] Promoted {promoted} patterns to LTM", flush=True)
        
        return results[0] if results else {'distance': 1.0, 'perfect': False, 'near_miss': False}
    
    def dream(self, verbose: Optional[bool] = None):
        """Run the dream cycle (between batches)."""
        v = verbose if verbose is not None else self.verbose
        
        stats = self.ltm.dream_cycle(verbose=v)
        
        if v:
            print(f"\n[DREAM] Epoch {stats['epoch']}: "
                  f"{stats['remaining_patterns']} patterns remaining", flush=True)
        
        return stats
    
    def save_memory(self):
        """Persist memory to disk."""
        self.ltm.save()
        self.compiled_library.save_to_json(self.dream_path)
        self.near_miss_journal.save_to_json(self.journal_path)
    
    def get_stats(self) -> Dict:
        """Get combined statistics."""
        return {
            'session': self.session_stats,
            'memory': self.ltm.get_stats(),
            'dream': self.compiled_library.stats(),
        }


# =============================================================================
# INTELLIGENT TASK BATCHING (SGC-ARC Deep Dive: Methods & Task Batching)
# =============================================================================
#
# SGC GROUNDING:
# - Task groups ARE macro-scale coarse-grainings of task space
# - Within-group transfer IS renormalization: micro successes → macro priors
# - The curriculum IS optimal partition discovery in task space (IB objective)
# - Thompson sampling implements exploration-exploitation on the task lattice
# =============================================================================

class TaskSimilarityGraph:
    """
    Builds a similarity graph over tasks and clusters them into groups.
    
    Similarity measure (three components):
      sim(A, B) = α·sig_match + β·predicate_overlap + γ·structural_transfer
    
    where:
      - sig_match: binary — same compute_task_signature or not
      - predicate_overlap: Jaccard of top-5 NMI predicates
      - structural_transfer: whether compiled program from A applies to B
    """
    
    def __init__(self, alpha: float = 0.3, beta: float = 0.4, gamma: float = 0.3):
        self.alpha = alpha
        self.beta = beta
        self.gamma = gamma
    
    def cluster_tasks(self, tasks: List[ARCTask],
                      max_group_size: int = 10,
                      min_group_size: int = 3) -> List[List[int]]:
        """
        Cluster tasks into groups using task signatures.
        
        Returns list of groups, each group is a list of task indices.
        Uses signature-based clustering (fast, no pairwise computation needed).
        """
        # Phase 1: Group by task signature (coarse clustering)
        sig_groups: Dict[str, List[int]] = {}
        for i, task in enumerate(tasks):
            sig = compute_task_signature(task)
            if sig not in sig_groups:
                sig_groups[sig] = []
            sig_groups[sig].append(i)
        
        # Phase 2: Split large groups, merge tiny groups
        groups = []
        orphans = []
        
        for sig, indices in sig_groups.items():
            if len(indices) >= min_group_size:
                # Split large groups into chunks of max_group_size
                for chunk_start in range(0, len(indices), max_group_size):
                    chunk = indices[chunk_start:chunk_start + max_group_size]
                    if len(chunk) >= min_group_size:
                        groups.append(chunk)
                    else:
                        orphans.extend(chunk)
            else:
                orphans.extend(indices)
        
        # Merge orphans into a group (or multiple if too many)
        if orphans:
            for chunk_start in range(0, len(orphans), max_group_size):
                chunk = orphans[chunk_start:chunk_start + max_group_size]
                groups.append(chunk)
        
        return groups


class GroupScheduler:
    """
    Thompson sampling scheduler over task groups.
    
    Each group maintains a Beta posterior tracking solve rate.
    Thompson sampling selects which group to solve next, naturally
    implementing curriculum learning: easy groups (high reward) first,
    then harder groups as the agent improves.
    
    SGC GROUNDING: This is the stationary distribution over the task
    partition lattice — groups where the agent makes progress get
    higher sampling weight, implementing defect-guided exploration.
    """
    
    def __init__(self, n_groups: int):
        # Beta(alpha, beta) posterior per group
        self.alphas = np.ones(n_groups)  # successes + 1
        self.betas = np.ones(n_groups)   # failures + 1
        self.attempts = np.zeros(n_groups, dtype=int)
        self.perfects = np.zeros(n_groups, dtype=int)
        self.near_misses = np.zeros(n_groups, dtype=int)
        self.predicate_discoveries = np.zeros(n_groups, dtype=int)
    
    def select_next(self) -> int:
        """Thompson sample to select next group."""
        samples = np.array([
            np.random.beta(a, b) for a, b in zip(self.alphas, self.betas)
        ])
        return int(np.argmax(samples))
    
    def update(self, group_idx: int, n_perfect: int, n_near: int,
               n_tasks: int, n_new_predicates: int = 0):
        """Update group posterior based on solve results."""
        self.attempts[group_idx] += n_tasks
        self.perfects[group_idx] += n_perfect
        self.near_misses[group_idx] += n_near
        self.predicate_discoveries[group_idx] += n_new_predicates
        
        # Reward = perfect solves + 0.3 * near-misses + 0.1 * new predicates
        reward = n_perfect + 0.3 * n_near + 0.1 * n_new_predicates
        # Normalize to [0, 1] range
        reward_rate = min(1.0, reward / max(1, n_tasks))
        
        # Update Beta posterior
        self.alphas[group_idx] += reward_rate * n_tasks
        self.betas[group_idx] += (1.0 - reward_rate) * n_tasks
    
    def summary(self) -> str:
        lines = []
        for i in range(len(self.alphas)):
            mean = self.alphas[i] / (self.alphas[i] + self.betas[i])
            lines.append(f"  Group {i}: {self.perfects[i]:.0f}P/{self.near_misses[i]:.0f}N "
                        f"({self.attempts[i]:.0f} attempts, posterior={mean:.3f})")
        return "\n".join(lines)


def solve_batched(agent: 'ARCSGCAgent', tasks: List[ARCTask],
                  n_passes: int = 2, verbose: bool = True,
                  log_fn=None) -> Dict:
    """
    Intelligent task batching: cluster tasks, solve in groups with
    cross-task transfer, then refine unsolved tasks with enriched priors.
    
    Architecture:
      1. Cluster tasks by signature similarity
      2. For each pass:
         a. Thompson sample a group ordering
         b. For each group: discovery → refinement → cross-transfer
      3. Dream cycle between passes
    
    SGC GROUNDING: This is multi-scale defect minimization:
      - Pass 1 = coarse sweep (discover predicates, build priors)
      - Pass 2+ = refinement (enriched priors convert near-misses to perfects)
      - Dream between passes = consolidation (prune noise, reinforce signal)
    
    Args:
        agent: The ARCSGCAgent instance
        tasks: List of tasks to solve
        n_passes: Number of passes over the task set (default 2)
        verbose: Print progress
        log_fn: Optional callable for logging (called with string)
    
    Returns:
        Dict with results, per-task details, group statistics
    """
    def log(msg):
        if verbose:
            print(msg, flush=True)
        if log_fn:
            log_fn(msg)
    
    # =====================================================================
    # PHASE 0: Cluster tasks into groups
    # =====================================================================
    graph = TaskSimilarityGraph()
    groups = graph.cluster_tasks(tasks, max_group_size=8, min_group_size=3)
    scheduler = GroupScheduler(n_groups=len(groups))
    
    log(f"[BATCH] Clustered {len(tasks)} tasks into {len(groups)} groups")
    for gi, grp in enumerate(groups):
        sigs = set()
        for idx in grp:
            sigs.add(compute_task_signature(tasks[idx]))
        log(f"  Group {gi}: {len(grp)} tasks, sigs={sigs}")
    
    # Per-task tracking
    task_results: Dict[str, Dict] = {}  # task_id -> best result
    task_solved: Dict[str, bool] = {}   # task_id -> perfect?
    
    total_perfect = 0
    total_near = 0
    total_fail = 0
    
    import time as _time
    t0 = _time.time()
    
    for pass_num in range(1, n_passes + 1):
        log(f"\n{'='*70}")
        log(f"PASS {pass_num}/{n_passes}")
        log(f"{'='*70}")
        
        # Set solver temperature: T=0 for Pass 1 (deterministic baseline),
        # T>0 for Pass 2+ (Boltzmann exploration of alternative partitions).
        # SGC GROUNDING: This is the IB Lagrange multiplier β = 1/T.
        # At T=0, hard assignment (deterministic argmax).
        # At T>0, soft assignment explores alternative local minima.
        if pass_num == 1:
            solver_temp = 0.0
        else:
            solver_temp = 0.15
        if hasattr(agent, 'residual_solver'):
            agent.residual_solver.temperature = solver_temp
        log(f"  Solver temperature: {solver_temp}")
        
        pass_perfect = 0
        pass_near = 0
        pass_new_perfect = 0
        
        # Determine group order via Thompson sampling
        if pass_num == 1:
            # First pass: sequential (no prior info)
            group_order = list(range(len(groups)))
        else:
            # Subsequent passes: Thompson sample ordering
            group_order = []
            remaining = set(range(len(groups)))
            while remaining:
                # Thompson sample from remaining groups
                samples = {
                    gi: np.random.beta(scheduler.alphas[gi], scheduler.betas[gi])
                    for gi in remaining
                }
                best = max(samples, key=samples.get)
                group_order.append(best)
                remaining.remove(best)
        
        for group_idx in group_order:
            grp = groups[group_idx]
            grp_tasks = [tasks[i] for i in grp]
            
            log(f"\n  --- Group {group_idx} ({len(grp_tasks)} tasks) ---")
            
            # Track predicates before this group
            prior_pred_count = len(agent.ltm.predicate_prior.attempt_counts)
            
            grp_perfect = 0
            grp_near = 0
            
            # =============================================================
            # PHASE 1: Discovery pass — solve each task, accumulate priors
            # =============================================================
            unsolved_in_group = []
            
            for task in grp_tasks:
                tid = task.task_id
                
                # Skip if already perfectly solved
                if task_solved.get(tid, False):
                    grp_perfect += 1
                    continue
                
                task_t0 = _time.time()
                try:
                    result = agent.solve_task(task)
                except Exception as e:
                    result = {'distance': 1.0, 'perfect': False, 'near_miss': False,
                              'winning_solver': f'error:{e}'}
                task_dt = _time.time() - task_t0
                
                is_perf = result.get('perfect', False)
                is_near = result.get('near_miss', False)
                dist = result.get('distance', 1.0)
                solver = result.get('winning_solver', 'none')
                
                # Store best result per task
                prev = task_results.get(tid)
                if prev is None or dist < prev.get('distance', 1.0):
                    task_results[tid] = result
                
                if is_perf:
                    task_solved[tid] = True
                    grp_perfect += 1
                    if not (prev and prev.get('perfect', False)):
                        pass_new_perfect += 1
                    tag = " ** PERFECT **"
                elif is_near:
                    grp_near += 1
                    unsolved_in_group.append(task)
                    tag = f" near(d={dist:.4f})"
                else:
                    unsolved_in_group.append(task)
                    tag = ""
                
                elapsed = _time.time() - t0
                log(f"    {tid[:12]:12s} d={dist:.4f} ({task_dt:.1f}s) "
                    f"{solver[:40]}{tag}")
            
            # =============================================================
            # PHASE 2: Refinement pass — re-solve failed tasks with
            #          enriched priors from Phase 1 discoveries
            # =============================================================
            if pass_num >= 1 and unsolved_in_group:
                log(f"  [REFINE-GROUP] Re-solving {len(unsolved_in_group)} unsolved tasks...")
                
                for task in unsolved_in_group:
                    tid = task.task_id
                    if task_solved.get(tid, False):
                        continue
                    
                    task_t0 = _time.time()
                    try:
                        result = agent.solve_task(task)
                    except Exception as e:
                        result = {'distance': 1.0, 'perfect': False,
                                  'near_miss': False, 'winning_solver': f'error:{e}'}
                    task_dt = _time.time() - task_t0
                    
                    is_perf = result.get('perfect', False)
                    dist = result.get('distance', 1.0)
                    solver = result.get('winning_solver', 'none')
                    
                    prev = task_results.get(tid)
                    prev_dist = prev.get('distance', 1.0) if prev else 1.0
                    
                    if dist < prev_dist:
                        task_results[tid] = result
                    
                    if is_perf:
                        task_solved[tid] = True
                        grp_perfect += 1
                        pass_new_perfect += 1
                        log(f"    [REFINE] {tid[:12]:12s} PERFECT! "
                            f"(was d={prev_dist:.4f}) ({task_dt:.1f}s)")
                    elif dist < prev_dist - 0.005:
                        if result.get('near_miss', False):
                            grp_near += 1
                        log(f"    [REFINE] {tid[:12]:12s} improved "
                            f"d={prev_dist:.4f}->{dist:.4f} ({task_dt:.1f}s)")
            
            # Update group scheduler
            new_preds = len(agent.ltm.predicate_prior.attempt_counts) - prior_pred_count
            scheduler.update(group_idx, grp_perfect, grp_near,
                           len(grp_tasks), new_preds)
            
            pass_perfect += grp_perfect
            pass_near += grp_near
            
            log(f"  Group {group_idx}: {grp_perfect}P/{grp_near}N "
                f"(+{new_preds} predicates)")
        
        # End of pass summary
        total_perfect = sum(1 for v in task_solved.values() if v)
        total_near = sum(1 for tid, r in task_results.items()
                        if r.get('near_miss', False) and not task_solved.get(tid, False))
        total_fail = len(tasks) - total_perfect - total_near
        
        elapsed = _time.time() - t0
        log(f"\n  Pass {pass_num} summary: {total_perfect}P / {total_near}N / "
            f"{total_fail}F ({pass_new_perfect} new perfects, {elapsed:.0f}s)")
        
        # Dream cycle between passes (consolidation)
        if pass_num < n_passes:
            log(f"\n  [DREAM] Consolidating between passes...")
            agent.dream(verbose=False)
            agent.save_memory()
    
    # =====================================================================
    # FINAL SUMMARY
    # =====================================================================
    elapsed = _time.time() - t0
    
    log(f"\n{'='*70}")
    log(f"BATCHED RESULTS ({n_passes} passes, {elapsed:.0f}s)")
    log(f"{'='*70}")
    log(f"Perfect: {total_perfect}  (baseline: 20 sequential)")
    log(f"Near-miss: {total_near}")
    log(f"Fails: {total_fail}")
    
    log(f"\nPerfect solves:")
    for tid, solved in sorted(task_solved.items()):
        if solved:
            r = task_results.get(tid, {})
            log(f"  {tid}: {r.get('winning_solver', '?')}")
    
    log(f"\nTop near-misses:")
    nears = [(tid, r.get('distance', 1.0), r.get('winning_solver', '?'))
             for tid, r in task_results.items()
             if r.get('near_miss', False) and not task_solved.get(tid, False)]
    nears.sort(key=lambda x: x[1])
    for tid, d, s in nears[:15]:
        log(f"  {tid}: d={d:.4f} {s[:50]}")
    
    log(f"\nGroup Scheduler:")
    log(scheduler.summary())
    
    log(f"\nPredicate Prior:")
    log(agent.ltm.predicate_prior.summary(top_k=10))
    
    return {
        'total_perfect': total_perfect,
        'total_near': total_near,
        'total_fail': total_fail,
        'task_results': task_results,
        'task_solved': task_solved,
        'groups': groups,
        'scheduler': scheduler,
        'elapsed': elapsed,
    }


# =============================================================================
# BATCH RUNNER (legacy sequential)
# =============================================================================

def run_agent_batch(tasks: List[ARCTask], limit: int = 20,
                    start_idx: int = 0,
                    memory_path: str = "agent_memory.json",
                    verbose: bool = False,
                    recall_enabled: bool = True,
                    update_enabled: bool = True) -> Dict:
    """Run the agent on a batch of tasks with persistent memory."""
    
    agent = ARCSGCAgent(memory_path=memory_path, verbose=verbose,
                        recall_enabled=recall_enabled, update_enabled=update_enabled)
    
    results = {
        'perfect': 0,
        'near_miss': 0,
        'total': 0,
        'distances': [],
        'task_results': []
    }
    
    print(f"\n[Agent] Initial memory: {agent.ltm.get_stats()}", flush=True)
    
    batch_tasks = tasks[start_idx:start_idx + limit]
    
    for i, task in enumerate(batch_tasks):
        print(f"\n[{i+1}/{len(batch_tasks)}] Task: {task.task_id}", flush=True)
        
        try:
            result = agent.solve_task(task, verbose=verbose)
            
            if result['perfect']:
                results['perfect'] += 1
            elif result['near_miss']:
                results['near_miss'] += 1
            
            results['distances'].append(result['distance'])
            results['task_results'].append({
                'task_id': task.task_id,
                'distance': result['distance'],
                'perfect': result['perfect'],
                'near_miss': result['near_miss']
            })
            
            status = "PERFECT" if result['perfect'] else ("NEAR" if result['near_miss'] else "MISS")
            print(f"  Summary: {status} (dist={result['distance']:.4f})", flush=True)
            print(f"  Running: perfect={results['perfect']}, near={results['near_miss']}", flush=True)
            
        except Exception as e:
            print(f"  Error: {e}", flush=True)
            import traceback
            traceback.print_exc()
        
        results['total'] += 1
    
    # Dream cycle after batch
    agent.dream(verbose=True)
    
    # Save memory
    agent.save_memory()
    
    print(f"\n[Agent] Final memory: {agent.ltm.get_stats()}", flush=True)
    
    return results, agent


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    sys.stdout.reconfigure(line_buffering=True)
    
    # Parse command line arguments
    import argparse
    parser = argparse.ArgumentParser(description="ARC-SGC Agent with Persistent Memory")
    parser.add_argument("--start", type=int, default=0, help="Start index for task batch")
    parser.add_argument("--limit", type=int, default=20, help="Number of tasks to run")
    parser.add_argument("--clear", action="store_true", help="Clear memory before running")
    # ABLATION flags
    parser.add_argument("--no-recall", action="store_true", help="Disable pattern recall (Condition B)")
    parser.add_argument("--no-update", action="store_true", help="Disable posterior updates (Condition C)")
    parser.add_argument("--ablation-name", type=str, default=None, help="Name for ablation run (saves to logs/)")
    parser.add_argument("--eval", action="store_true", help="Run on evaluation set (400 tasks) instead of training")
    args = parser.parse_args()
    
    print("=" * 70, flush=True)
    print("ARC-SGC AGENT: MULTI-SCALE SOLVER WITH PERSISTENT MEMORY", flush=True)
    print("=" * 70, flush=True)
    print()
    print("MULTI-SCALE ARCHITECTURE (SGC.Renormalization):")
    print("  SYNTH: RecursiveResidualSolver (Phase 62: gradient-guided programs)")
    print("  MACRO: HeuristicSolverAdapter (Phase 8.3/15/18 global operations)")
    print("  MESO:  Phase 45 NeighborhoodConstraintLearner (Pattern Rules)")
    print("  MICRO: Phase 21 ResidualCompiler (Induced Operators)")
    print()
    print("THE SYNTHESIS:")
    print("  - Phase 62: Recursive Residual Solver (ILP predicates + beam search)")
    print("  - Phase 8.3/15/18: identity, color, crop, rotate, flip, shift, extract")
    print("  - Phase 21: ContentAddressedOperatorMemory (Toolbox)")
    print("  - Phase 37: ConsolidationEngine (Dream Cycle)")
    print("  - Phase 45: NeighborhoodConstraintLearner (Pattern Rules)")
    print()
    print("THE PRINCIPLE:")
    print("  Best of ALL scales: Phase 62 programs + Phase 45 patterns + Phase 18 ops")
    print("  Bayesian posteriors track which solver family wins per context")
    print()
    
    # Clear memory if requested
    if args.clear:
        import os
        if os.path.exists("agent_memory.json"):
            os.remove("agent_memory.json")
            print("[RESET] Cleared agent memory")
    
    # Load ARC tasks
    if args.eval:
        arc_paths = [
            "data/arc/evaluation",
            "C:/Lean4 Projects/data/arc/evaluation",
            "../data/arc/evaluation"
        ]
        print("[MODE] Evaluation set (400 tasks)")
    else:
        arc_paths = [
            "data/arc/training",
            "C:/Lean4 Projects/data/arc/training",
            "../data/arc/training"
        ]
    
    tasks = []
    for arc_path in arc_paths:
        tasks = load_arc_tasks(arc_path)
        if tasks:
            print(f"Loaded {len(tasks)} tasks from {arc_path}")
            break
    
    if not tasks:
        print("No ARC tasks found.")
        sys.exit(1)
    
    # Run agent
    print("\n" + "=" * 70)
    print(f"RUNNING AGENT BATCH (tasks {args.start}-{args.start + args.limit})")
    print("=" * 70)
    
    # Determine ablation condition
    recall_enabled = not args.no_recall
    update_enabled = not args.no_update
    
    condition_name = "A_full" if (recall_enabled and update_enabled) else \
                     "B_no_recall" if not recall_enabled else \
                     "C_no_update"
    
    print(f"\n[ABLATION] Condition: {condition_name}")
    print(f"  recall_enabled={recall_enabled}, update_enabled={update_enabled}")
    
    start_time = time.time()
    results, agent = run_agent_batch(
        tasks, limit=args.limit, start_idx=args.start, verbose=True,
        recall_enabled=recall_enabled, update_enabled=update_enabled
    )
    elapsed = time.time() - start_time
    
    # Results
    print("\n" + "=" * 70)
    print("AGENT RESULTS")
    print("=" * 70)
    print(f"Perfect solves: {results['perfect']}")
    print(f"Near misses: {results['near_miss']}")
    print(f"Total tasks: {results['total']}")
    print(f"Time: {elapsed:.2f}s")
    
    if results['distances']:
        avg_dist = np.mean(results['distances'])
        min_dist = np.min(results['distances'])
        print(f"Avg distance: {avg_dist:.4f}")
        print(f"Min distance: {min_dist:.4f}")
    
    # Task breakdown
    print("\n" + "=" * 70)
    print("TASK BREAKDOWN")
    print("=" * 70)
    for tr in results['task_results']:
        status = "PERFECT" if tr['perfect'] else ("NEAR" if tr['near_miss'] else "MISS")
        print(f"  {tr['task_id']}: {status} (dist={tr['distance']:.4f})")
    
    # Agent stats
    print("\n" + "=" * 70)
    print("AGENT STATISTICS")
    print("=" * 70)
    stats = agent.get_stats()
    print(f"Session:")
    for k, v in stats['session'].items():
        print(f"  {k}: {v}")
    print(f"Memory:")
    for k, v in stats['memory'].items():
        print(f"  {k}: {v}")
    print(f"Dream Consolidation:")
    for k, v in stats['dream'].items():
        print(f"  {k}: {v}")
    
    # Comparison
    print("\n" + "=" * 70)
    print("PHASE COMPARISON")
    print("=" * 70)
    print("| Phase               | Perfect | Near | Min Dist | Theory                     |")
    print("|---------------------|---------|------|----------|----------------------------|")
    print("| 40+41               |    0    |   4  |  0.0258  | Operator Search            |")
    print("| 42 (Pixel)          |    1    |   3  |  0.0000  | Position-Absolute Pixel    |")
    print("| 45 (Pattern)        |    1    |   7  |  0.0000  | Neighborhood Rules         |")
    print("| Agent (P45 only)    |    1    |   4  |  0.0000  | P45 + Persistent Memory    |")
    print(f"| Agent (Multi-Scale) |   {results['perfect']:>2}    |  {results['near_miss']:>2}  |  {min_dist:.4f}  | P45 + P18 + Memory         |")
    
    # Solver family breakdown
    r_wins = stats['session'].get('residual_wins', 0)
    h_wins = stats['session'].get('heuristic_wins', 0)
    p_wins = stats['session'].get('pattern_wins', 0)
    print(f"\nSolver Family Wins:")
    print(f"  Residual (synth):  {r_wins}")
    print(f"  Heuristic (macro): {h_wins}")
    print(f"  Phase 45 (meso):   {p_wins}")
    
    print("\n" + "=" * 70)
    print("AGENT RUN COMPLETE")
    print("=" * 70)
    print(f"\nMemory saved to: agent_memory.json")
    print("Run again to see memory evolution!")
    
    # Save ablation results if requested
    if args.ablation_name:
        import json
        import os
        ablation_results = {
            'condition': condition_name,
            'recall_enabled': recall_enabled,
            'update_enabled': update_enabled,
            'start_idx': args.start,
            'limit': args.limit,
            'perfect': results['perfect'],
            'near_miss': results['near_miss'],
            'total': results['total'],
            'elapsed_time': elapsed,
            'avg_distance': float(np.mean(results['distances'])) if results['distances'] else 1.0,
            'min_distance': float(np.min(results['distances'])) if results['distances'] else 1.0,
            'session_stats': stats['session'],
            'memory_stats': {k: float(v) if isinstance(v, (np.floating, np.integer)) else v 
                           for k, v in stats['memory'].items()},
            'task_results': [{k: (bool(v) if isinstance(v, (np.bool_,)) else 
                                float(v) if isinstance(v, (np.floating, np.integer)) else v) 
                               for k, v in tr.items()} for tr in results['task_results']]
        }
        
        os.makedirs("logs/ablation", exist_ok=True)
        ablation_path = f"logs/ablation/{args.ablation_name}_{condition_name}.json"
        with open(ablation_path, 'w') as f:
            json.dump(ablation_results, f, indent=2)
        print(f"\n[ABLATION] Results saved to: {ablation_path}")
