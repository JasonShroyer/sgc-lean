# ARC-SGC Agent: Bayesian Memory Upgrade

**Date:** February 12, 2026  
**Status:** Implemented and Tested

## Summary

Upgraded `arc_sgc_agent.py` with:
1. **Bayesian Memory** - Beta-Binomial posteriors with Thompson sampling
2. **Induced Generators** - Phase 21 ResidualCompiler integration
3. **Grokking Detection** - Posterior variance collapse as certainty measure

## The Bayesian Upgrade

### Theory (from arXiv paper "From Classical to Topological Neural Networks Under Uncertainty")

The paper confirms our approach: treat confidence as a **posterior distribution**, not a point estimate.

| Old Approach | Bayesian Approach |
|--------------|-------------------|
| `confidence = 0.9` (point estimate) | `P(success) ~ Beta(α, β)` (distribution) |
| Utility ranking | Thompson sampling / UCB |
| Ad-hoc thresholds | Posterior variance collapse |

### Implementation

```python
@dataclass
class PatternOperator:
    # Beta-Binomial conjugate prior
    alpha_prior: float = 1.0   # Uniform prior
    beta_prior: float = 1.0
    success_count: int = 0     # Updates alpha
    failure_count: int = 0     # Updates beta
    
    def posterior_mean(self) -> float:
        a = self.alpha_prior + self.success_count
        b = self.beta_prior + self.failure_count
        return a / (a + b)
    
    def thompson_sample(self) -> float:
        """Sample from posterior for explore/exploit balance."""
        return np.random.beta(self.posterior_alpha(), self.posterior_beta())
    
    def is_grokked(self, threshold=0.01) -> bool:
        """Has posterior collapsed? (Low uncertainty = grokked)."""
        return self.posterior_variance() < threshold
```

### Selection Modes

```python
# Thompson sampling (default) - explore/exploit balance
agent = ARCSGCAgent(sampling_mode='thompson')

# UCB - optimistic exploration
agent = ARCSGCAgent(sampling_mode='ucb')

# Greedy - pure exploitation
agent = ARCSGCAgent(sampling_mode='greedy')
```

## Induced Generators (Phase 21 Integration)

### Theory

When Phase 45 gets a near-miss or shape mismatch, the **ResidualCompiler** attempts to induce an operator from the residual:

```
Δ = target - prediction → ResidualCompiler → Operator
```

### Operator Types Detected

| Family | Example | Detection Method |
|--------|---------|------------------|
| `rotate90/180/270` | Grid rotation | `np.rot90(pred) == target` |
| `flip_h/flip_v` | Mirror | `np.fliplr(pred) == target` |
| `translate` | Shift | Centroid comparison |
| `color_map` | Recolor | Consistent pixel changes |
| `crop/expand` | Shape change | Size ratio analysis |

### Integration Point

```python
# In solve_task(), after Phase 45 solve:
if not perfect and (near_miss or output.shape != target.shape):
    induced_op = self.residual_compiler.compile(pred, target, task, [])
    if induced_op:
        # Operator discovered from residual!
        self.session_stats['operators_induced'] += 1
```

## Test Results

### Batch 1 (Tasks 0-20)
- **Perfect:** 1, **Near Miss:** 7
- **Patterns promoted:** 36
- **Memory:** avg_posterior_mean=0.667, grokked_patterns=0

### Batch 2 (Tasks 20-40) - Using Prior Memory
- **Perfect:** 1 (Task `1190e5a7` solved via **27 prior patterns**)
- **Near Miss:** 4
- **Memory:** 40 tasks seen, 2 total perfect solves

### Transfer Learning Confirmed
Task `1190e5a7` was solved **perfectly** using patterns learned from tasks 0-20 (different task batch).

## Memory Statistics

```json
{
  "pattern_rules": 36,
  "global_color_maps": 11,
  "current_epoch": 2,
  "total_tasks_seen": 40,
  "total_perfect_solves": 2,
  "avg_posterior_mean": 0.667,
  "avg_posterior_variance": 0.056,
  "grokked_patterns": 0
}
```

## Usage

```bash
# Run with Thompson sampling (default)
python arc_sgc_agent.py --limit 20

# Run on different batch (transfer learning)
python arc_sgc_agent.py --start 20 --limit 20

# Clear memory and start fresh
python arc_sgc_agent.py --clear

# Run with UCB exploration
# (requires code change: sampling_mode='ucb')
```

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    ARCSGCAgent                          │
├─────────────────────────────────────────────────────────┤
│  ┌─────────────────┐  ┌──────────────────────────────┐ │
│  │  LongTermMemory │  │    ResidualCompiler          │ │
│  │  (Bayesian)     │  │    (Phase 21)                │ │
│  │                 │  │                              │ │
│  │  Pattern Rules  │  │  Induce operators from       │ │
│  │  + Beta priors  │  │  near-misses/shape mismatch  │ │
│  │                 │  │                              │ │
│  │  Thompson/UCB   │  │  rotate, flip, translate,    │ │
│  │  selection      │  │  color_map, crop, expand     │ │
│  └─────────────────┘  └──────────────────────────────┘ │
│                                                         │
│  ┌─────────────────────────────────────────────────┐   │
│  │           Phase 45 Solver                        │   │
│  │  NeighborhoodConstraintLearner + Harmonic Fill   │   │
│  └─────────────────────────────────────────────────┘   │
│                                                         │
│  Dream Cycle: decay + prune + consolidate               │
└─────────────────────────────────────────────────────────┘
```

## Future Work

1. **Run ablation experiments** comparing Thompson vs UCB vs Greedy
2. **Increase pattern usage** to observe posterior collapse (grokking)
3. **Wire Phase 38** as probability flow controller
4. **Log posterior entropy traces** for grokking detection visualization

## Files Modified

- `c:\Lean4 Projects\demos\arc_sgc_agent.py` - Main agent with Bayesian upgrade

## References

- arXiv paper: "From Classical to Topological Neural Networks Under Uncertainty" (Feb 2026)
- Phase 21: `arc_sgc_phase21.py` - ContentAddressedOperatorMemory, ResidualCompiler
- Phase 45: `arc_sgc_phase45.py` - NeighborhoodConstraintLearner
