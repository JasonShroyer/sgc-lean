"""Test emergent diffusion fill on ARC tasks"""
import numpy as np
import json
from emergent_sheaf_engine import EmergentSheafEngine

# Task 00d62c1b - test emergent diffusion fill
task = json.load(open('../data/arc/training/00d62c1b.json'))

print("Task 00d62c1b - Testing emergent diffusion fill")
print("=" * 50)

for i, ex in enumerate(task['train']):
    inp = np.array(ex['input'], dtype=np.float32)
    out = np.array(ex['output'], dtype=np.float32)
    
    engine = EmergentSheafEngine(inp, out)
    result = engine.solve(verbose=False)
    
    success = result.get('success', False)
    energy = result.get('final_energy', 'N/A')
    method = result.get('method', 'none')
    
    print(f"Example {i+1}: Success={success}, Energy={energy}, Method={method}")
