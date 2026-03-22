"""Quick analysis of task 1b60fb0c to find the true transformation pattern."""
import numpy as np
import json
from pathlib import Path

arc_dir = Path(__file__).parent.parent / "data" / "arc" / "training"
task_file = arc_dir / "1b60fb0c.json"

with open(task_file) as f:
    task = json.load(f)

for idx, ex in enumerate(task['train']):
    inp = np.array(ex['input'])
    out = np.array(ex['output'])
    
    print(f"\n{'='*50}")
    print(f"EXAMPLE {idx+1}")
    print(f"{'='*50}")
    
    source = (inp == 1)
    added = (out == 2) & (inp == 0)
    
    print("\nRow-by-row mapping (source -> added):")
    for i in range(len(inp)):
        src_cols = list(np.where(source[i])[0])
        add_cols = list(np.where(added[i])[0])
        if src_cols or add_cols:
            # Analyze the relationship
            if add_cols and src_cols:
                # For each added col, which source col maps to it?
                # If axis is at position A, then j -> 2A - j - 1
                # So A = (j + mirror_j + 1) / 2
                implied_axes = []
                for add_j in add_cols:
                    for src_j in src_cols:
                        axis = (src_j + add_j + 1) / 2
                        implied_axes.append(axis)
                unique_axes = list(set(implied_axes))
                print(f"  Row {i}: {src_cols} -> {add_cols}  (implied axis: {unique_axes})")
            else:
                print(f"  Row {i}: {src_cols} -> {add_cols}")

print("\n" + "="*50)
print("ANALYSIS: Looking for consistent axis")
print("="*50)

# Collect all implied axes across all examples
all_axes = []
for ex in task['train']:
    inp = np.array(ex['input'])
    out = np.array(ex['output'])
    source = (inp == 1)
    added = (out == 2) & (inp == 0)
    
    for i in range(len(inp)):
        src_cols = list(np.where(source[i])[0])
        add_cols = list(np.where(added[i])[0])
        if add_cols and src_cols:
            for add_j in add_cols:
                for src_j in src_cols:
                    axis = (src_j + add_j + 1) / 2
                    if axis == int(axis):  # Only integer axes
                        all_axes.append(int(axis))

from collections import Counter
axis_counts = Counter(all_axes)
print(f"\nAxis frequency: {axis_counts.most_common(5)}")

# The most common axis is likely the true reflection axis
if axis_counts:
    best_axis = axis_counts.most_common(1)[0][0]
    print(f"\nMost likely axis: {best_axis}")
    
    # Verify: for each example, which source pixels map to added pixels with this axis?
    print("\nVerification with axis =", best_axis)
    for idx, ex in enumerate(task['train']):
        inp = np.array(ex['input'])
        out = np.array(ex['output'])
        source = (inp == 1)
        added = (out == 2) & (inp == 0)
        
        # For axis A: j -> 2A - j - 1
        predicted_add = np.zeros_like(source)
        for i in range(len(inp)):
            for j in range(len(inp[0])):
                if source[i, j]:
                    mirror_j = 2 * best_axis - j - 1
                    if 0 <= mirror_j < len(inp[0]):
                        predicted_add[i, mirror_j] = True
        
        # Compare
        overlap = (predicted_add & added).sum()
        predicted_total = predicted_add.sum()
        actual_total = added.sum()
        
        print(f"  Ex {idx+1}: predicted {predicted_total} additions, actual {actual_total}, overlap {overlap}")
