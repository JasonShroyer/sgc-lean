"""
Quick test of Tensor Logic predicate discovery on synthetic + real data.
Tests the core algorithm without running the full solver.
"""
import numpy as np
import sys
import time
sys.path.insert(0, '.')

from arc_tensor_logic import TensorPredicateLearner, make_tensor_predicate_expr, encode_pixel_features

print("=" * 60, flush=True)
print("TENSOR LOGIC QUICK TEST", flush=True)
print("=" * 60, flush=True)

# ---- Test 1: Synthetic task - fill enclosed region ----
print("\n--- Test 1: Synthetic 'fill enclosed region' ---", flush=True)

# Input: 5x5 grid with a frame of color 1 and background interior
grid1 = np.array([
    [1, 1, 1, 1, 1],
    [1, 0, 0, 0, 1],
    [1, 0, 0, 0, 1],
    [1, 0, 0, 0, 1],
    [1, 1, 1, 1, 1],
])
# Target: interior filled with color 2
target1 = np.array([
    [1, 1, 1, 1, 1],
    [1, 2, 2, 2, 1],
    [1, 2, 2, 2, 1],
    [1, 2, 2, 2, 1],
    [1, 1, 1, 1, 1],
])
# Prediction (wrong): all background stays as 0
pred1 = grid1.copy()

# Second example - different frame
grid2 = np.array([
    [3, 3, 3, 3],
    [3, 0, 0, 3],
    [3, 0, 0, 3],
    [3, 3, 3, 3],
])
target2 = np.array([
    [3, 3, 3, 3],
    [3, 2, 2, 3],
    [3, 2, 2, 3],
    [3, 3, 3, 3],
])
pred2 = grid2.copy()

# Can't batch different shapes, so test each individually
learner = TensorPredicateLearner(n_factors=3, lr=0.05, steps=200, min_f1=0.25)

t0 = time.time()
discovered = learner.discover_predicates(
    [grid1], [target1], [pred1], verbose=True)
elapsed = time.time() - t0
print(f"\nDiscovered {len(discovered)} predicates in {elapsed:.1f}s", flush=True)

for dp in discovered:
    tp = make_tensor_predicate_expr(dp, dp.weights, dp.bias)
    mask = tp.evaluate(grid1)
    residual = (pred1 != target1)
    print(f"  {tp.name}", flush=True)
    print(f"  F1={dp.f1:.3f}, mask covers {mask.sum()} pixels, "
          f"{(mask & residual).sum()}/{residual.sum()} wrong pixels", flush=True)

# ---- Test 2: Synthetic task - border fill ----
print("\n--- Test 2: Synthetic 'fill border pixels' ---", flush=True)

grid3 = np.array([
    [0, 2, 0, 0, 0],
    [0, 0, 0, 2, 0],
    [0, 0, 0, 0, 0],
    [0, 2, 0, 0, 0],
    [0, 0, 0, 2, 0],
])
# Target: border pixels become color 5
target3 = np.zeros((5, 5), dtype=int)
target3[0, :] = 5; target3[-1, :] = 5; target3[:, 0] = 5; target3[:, -1] = 5
# Keep interior non-border non-zero pixels
for r in range(5):
    for c in range(5):
        if grid3[r, c] != 0 and target3[r, c] == 0:
            target3[r, c] = grid3[r, c]
# Prediction: just the input (wrong)
pred3 = grid3.copy()

t0 = time.time()
discovered = learner.discover_predicates(
    [grid3], [target3], [pred3], verbose=True)
elapsed = time.time() - t0
print(f"\nDiscovered {len(discovered)} predicates in {elapsed:.1f}s", flush=True)

for dp in discovered:
    tp = make_tensor_predicate_expr(dp, dp.weights, dp.bias)
    mask = tp.evaluate(grid3)
    residual = (pred3 != target3)
    print(f"  {tp.name}", flush=True)
    print(f"  F1={dp.f1:.3f}, mask covers {mask.sum()} pixels, "
          f"{(mask & residual).sum()}/{residual.sum()} wrong pixels", flush=True)

# ---- Test 3: Cross-shaped fill (adjacency predicate) ----
print("\n--- Test 3: 'fill adjacent to color 5' ---", flush=True)

grid4 = np.zeros((7, 7), dtype=int)
grid4[3, 3] = 5  # Center pixel is color 5
# Target: pixels adjacent (4-conn) to 5 become color 1
target4 = grid4.copy()
target4[2, 3] = 1; target4[4, 3] = 1; target4[3, 2] = 1; target4[3, 4] = 1
pred4 = grid4.copy()

t0 = time.time()
discovered = learner.discover_predicates(
    [grid4], [target4], [pred4], verbose=True)
elapsed = time.time() - t0
print(f"\nDiscovered {len(discovered)} predicates in {elapsed:.1f}s", flush=True)

for dp in discovered:
    tp = make_tensor_predicate_expr(dp, dp.weights, dp.bias)
    mask = tp.evaluate(grid4)
    residual = (pred4 != target4)
    print(f"  {tp.name}", flush=True)
    print(f"  F1={dp.f1:.3f}, mask={mask.sum()} pixels, "
          f"covers {(mask & residual).sum()}/{residual.sum()} wrong", flush=True)

# ---- Test 4: Real ARC task (if available) ----
print("\n--- Test 4: Real ARC task ---", flush=True)
try:
    from arc_sgc_phase8_3 import load_arc_tasks
    tasks = load_arc_tasks('../data/arc/training')
    # Pick task 00d62c1b (known: fill enclosed by fg)
    task_ids = {t.task_id: t for t in tasks}

    # Try a few known near-miss tasks
    test_tasks = ['00d62c1b', '3aa6fb7a', '4258a5f9']
    for tid in test_tasks:
        if tid not in task_ids:
            continue
        task = task_ids[tid]
        grids = [ex.input_grid.data.numpy() for ex in task.train_examples]
        targets = [ex.output_grid.data.numpy() for ex in task.train_examples]

        # Check all same shape
        shapes = set(g.shape for g in grids)
        if len(shapes) > 1:
            print(f"  {tid}: different shapes, skipping", flush=True)
            continue

        print(f"\n  Task {tid}:", flush=True)
        t0 = time.time()
        discovered = learner.discover_predicates(
            grids, targets, verbose=True)
        elapsed = time.time() - t0
        print(f"  {len(discovered)} predicates in {elapsed:.1f}s", flush=True)
        for dp in discovered[:3]:
            tp = make_tensor_predicate_expr(dp, dp.weights, dp.bias)
            print(f"    {tp.name} F1={dp.f1:.3f}", flush=True)
except Exception as e:
    print(f"  Could not load real tasks: {e}", flush=True)

print(f"\n{'='*60}", flush=True)
print("TENSOR LOGIC QUICK TEST COMPLETE", flush=True)
print("="*60, flush=True)
