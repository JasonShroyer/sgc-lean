"""
ARC-SGC Phase 27.5: The Forensic Pathologist

DIAGNOSIS: Phase 27 Object Abstraction failed to convert near-misses.
HYPOTHESIS: Model mismatch - our geometric "object" != task relational "object"

This tool dissects near-miss failures to reveal the ACTUAL missing operators.

Three failure modes to detect:
1. GHOST OBJECTS - We found the object but applied wrong rule
2. INVISIBLE OBJECTS - Our extractor failed to segment correctly  
3. PATTERN MISMATCH - Task needs pattern fill, not flat fill
"""

import sys
import os
import time
import numpy as np
import torch
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Any, Tuple, Optional

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent))

from arc_sgc_phase21 import (
    Phase21Solver, RuleRegistry, ARCPhase83Config, 
    load_arc_tasks, ARCTask, ARCExample, ARCGrid, 
    ObjectExtractor, ARCObject, DiscoveredPhysics
)


def print_grid_ascii(grid: ARCGrid, label: str, max_width: int = 30):
    """Print a grid in a readable ASCII format with color symbols."""
    print(f"\n--- {label} ---")
    data = grid.data.numpy()
    h, w = data.shape
    
    # Color map for better visualization
    color_chars = {
        0: '.',  # Black/background
        1: '1',  # Blue
        2: '2',  # Red
        3: '3',  # Green
        4: '4',  # Yellow
        5: '5',  # Grey
        6: '6',  # Magenta
        7: '7',  # Orange
        8: '8',  # Cyan
        9: '9',  # Brown
    }
    
    # Column headers
    header = "   " + "".join([f"{c%10}" for c in range(min(w, max_width))])
    if w > max_width:
        header += f"... ({w} cols)"
    print(header)
    
    for r in range(min(h, 20)):  # Limit rows for readability
        row_str = f"{r:2d} "
        for c in range(min(w, max_width)):
            val = int(data[r, c])
            row_str += color_chars.get(val, str(val))
        if w > max_width:
            row_str += "..."
        print(row_str)
    
    if h > 20:
        print(f"... ({h} rows total)")


def print_diff_grid(pred: ARCGrid, target: ARCGrid, label: str = "DIFF"):
    """Print a diff grid showing where prediction differs from target."""
    if pred.shape != target.shape:
        print(f"\n--- {label} (SHAPE MISMATCH) ---")
        print(f"Pred: {pred.shape}, Target: {target.shape}")
        return
    
    print(f"\n--- {label} (X = wrong, . = correct) ---")
    pred_data = pred.data.numpy()
    target_data = target.data.numpy()
    h, w = pred_data.shape
    
    # Column headers
    print("   " + "".join([f"{c%10}" for c in range(min(w, 30))]))
    
    for r in range(min(h, 20)):
        row_str = f"{r:2d} "
        for c in range(min(w, 30)):
            if pred_data[r, c] != target_data[r, c]:
                row_str += "X"  # Error
            else:
                row_str += "."  # Correct
        print(row_str)


def analyze_diff_detailed(pred: ARCGrid, target: ARCGrid) -> Dict[str, Any]:
    """Deep analysis of prediction vs target differences."""
    analysis = {
        'shape_match': pred.shape == target.shape,
        'error_count': 0,
        'error_positions': [],
        'error_region': None,
        'pred_error_values': [],
        'target_error_values': [],
        'hypothesis': 'unknown'
    }
    
    if not analysis['shape_match']:
        analysis['hypothesis'] = 'SHAPE_TRANSFORM_NEEDED'
        return analysis
    
    pred_data = pred.data.numpy()
    target_data = target.data.numpy()
    diff_mask = (pred_data != target_data)
    
    analysis['error_count'] = int(np.sum(diff_mask))
    total_pixels = diff_mask.size
    analysis['error_ratio'] = analysis['error_count'] / total_pixels
    
    if analysis['error_count'] == 0:
        analysis['hypothesis'] = 'PERFECT_MATCH'
        return analysis
    
    # Find error positions
    rows, cols = np.where(diff_mask)
    analysis['error_positions'] = list(zip(rows.tolist(), cols.tolist()))
    
    # Bounding box of errors
    r_min, r_max = rows.min(), rows.max()
    c_min, c_max = cols.min(), cols.max()
    analysis['error_region'] = {
        'r_min': int(r_min), 'r_max': int(r_max),
        'c_min': int(c_min), 'c_max': int(c_max),
        'height': int(r_max - r_min + 1),
        'width': int(c_max - c_min + 1)
    }
    
    # What values are wrong?
    analysis['pred_error_values'] = sorted(set(pred_data[diff_mask].tolist()))
    analysis['target_error_values'] = sorted(set(target_data[diff_mask].tolist()))
    
    # Generate hypothesis based on error pattern
    err_region = analysis['error_region']
    
    # Check if errors form a rectangle
    err_h, err_w = err_region['height'], err_region['width']
    expected_rect_errors = err_h * err_w
    
    if analysis['error_count'] == expected_rect_errors:
        # Errors fill a complete rectangle
        if len(analysis['target_error_values']) == 1:
            analysis['hypothesis'] = f'FILL_RECT_WITH_{analysis["target_error_values"][0]}'
        else:
            analysis['hypothesis'] = 'FILL_RECT_WITH_PATTERN'
    elif analysis['error_count'] < expected_rect_errors * 0.5:
        # Sparse errors - might be boundary or specific pixels
        analysis['hypothesis'] = 'SPARSE_MODIFICATION'
    else:
        # Errors mostly fill region but with gaps
        analysis['hypothesis'] = 'PARTIAL_FILL_OR_MASK'
    
    # Check for interior pattern (errors surrounded by object)
    if err_h > 2 and err_w > 2:
        # Check if there's a frame around the error region
        h, w = target_data.shape
        if (r_min > 0 and r_max < h-1 and c_min > 0 and c_max < w-1):
            frame_vals = []
            if r_min > 0:
                frame_vals.extend(target_data[r_min-1, c_min:c_max+1].tolist())
            if r_max < h-1:
                frame_vals.extend(target_data[r_max+1, c_min:c_max+1].tolist())
            if c_min > 0:
                frame_vals.extend(target_data[r_min:r_max+1, c_min-1].tolist())
            if c_max < w-1:
                frame_vals.extend(target_data[r_min:r_max+1, c_max+1].tolist())
            
            frame_color = max(set(frame_vals), key=frame_vals.count) if frame_vals else 0
            if frame_color != 0:
                analysis['hypothesis'] = f'FILL_INTERIOR_OF_COLOR_{frame_color}'
    
    return analysis


def dump_object_model(grid: ARCGrid) -> List[Dict[str, Any]]:
    """Extract objects and return detailed info."""
    objects_info = []
    
    modes = ['connected_color', 'foreground']
    
    for mode in modes:
        try:
            objects = ObjectExtractor.extract(grid.data, mode=mode)
            for i, obj in enumerate(objects):
                info = {
                    'mode': mode,
                    'index': i,
                    'color': obj.color,
                    'position': obj.position,
                    'bbox': obj.bbox,
                    'size': f"{obj.bbox[2]}x{obj.bbox[3]}",
                    'mass': obj.mass,
                    'is_hollow': obj.is_hollow,
                    'is_solid': obj.is_solid
                }
                objects_info.append(info)
        except Exception as e:
            objects_info.append({'mode': mode, 'error': str(e)})
    
    return objects_info


def check_enclosure_status(grid: ARCGrid) -> Dict[str, Any]:
    """Check what DiscoveredPhysics sees in terms of enclosures."""
    try:
        enc_mask, bound_mask, n_enc = DiscoveredPhysics.detect_enclosures(grid.data)
        enc_colors = DiscoveredPhysics.get_enclosure_colors(grid.data)
        
        return {
            'num_enclosures': n_enc,
            'enclosure_pixels': int(enc_mask.sum()),
            'boundary_pixels': int(bound_mask.sum()),
            'enclosing_colors': enc_colors,
            'has_enclosures': n_enc > 0
        }
    except Exception as e:
        return {'error': str(e)}


def analyze_input_output_transform(inp: ARCGrid, out: ARCGrid) -> Dict[str, Any]:
    """Analyze what transformation converts input to output."""
    analysis = {
        'shape_change': inp.shape != out.shape,
        'input_shape': inp.shape,
        'output_shape': out.shape,
    }
    
    inp_data = inp.data.numpy()
    out_data = out.data.numpy()
    
    # Color analysis
    inp_colors = set(np.unique(inp_data).tolist())
    out_colors = set(np.unique(out_data).tolist())
    
    analysis['input_colors'] = sorted(inp_colors)
    analysis['output_colors'] = sorted(out_colors)
    analysis['new_colors'] = sorted(out_colors - inp_colors)
    analysis['removed_colors'] = sorted(inp_colors - out_colors)
    
    if analysis['shape_change']:
        # Check for crop/expand patterns
        ih, iw = inp.shape
        oh, ow = out.shape
        
        if oh < ih or ow < iw:
            analysis['transform_type'] = 'CROP'
        elif oh > ih or ow > iw:
            analysis['transform_type'] = 'EXPAND'
        else:
            analysis['transform_type'] = 'RESHAPE'
    else:
        # Same shape - analyze pixel changes
        diff_mask = (inp_data != out_data)
        changed_pixels = np.sum(diff_mask)
        total_pixels = diff_mask.size
        
        analysis['changed_pixels'] = int(changed_pixels)
        analysis['change_ratio'] = changed_pixels / total_pixels
        
        if changed_pixels == 0:
            analysis['transform_type'] = 'IDENTITY'
        elif changed_pixels < total_pixels * 0.1:
            analysis['transform_type'] = 'SPARSE_EDIT'
        elif changed_pixels < total_pixels * 0.5:
            analysis['transform_type'] = 'PARTIAL_EDIT'
        else:
            analysis['transform_type'] = 'MAJOR_EDIT'
        
        # Check if changes are in interior regions
        if changed_pixels > 0:
            rows, cols = np.where(diff_mask)
            r_min, r_max = rows.min(), rows.max()
            c_min, c_max = cols.min(), cols.max()
            
            # Are changes away from edges?
            h, w = inp_data.shape
            if r_min > 0 and r_max < h-1 and c_min > 0 and c_max < w-1:
                analysis['changes_in_interior'] = True
            else:
                analysis['changes_in_interior'] = False
    
    return analysis


def run_forensic_analysis(tasks: List[ARCTask], solver: Phase21Solver, top_n: int = 5):
    """Run the full forensic analysis on near-misses."""
    
    print("\n" + "="*70)
    print("PHASE 27.5: FORENSIC PATHOLOGIST")
    print("Analyzing Near-Miss Failures to Identify Missing Operators")
    print("="*70)
    
    near_misses = []
    
    print("\nPhase 1: Scanning for Near-Misses (F < 0.1, not perfect)...")
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose=False)
        
        dist = result.get('fisher_distance', 1.0)
        is_perfect = result.get('is_perfect', False)
        
        if not is_perfect and dist < 0.1:
            near_misses.append({
                'task': task,
                'result': result,
                'fisher_distance': dist
            })
        
        if (i + 1) % 20 == 0:
            print(f"  Scanned {i+1}/{len(tasks)} tasks, found {len(near_misses)} near-misses")
    
    # Sort by Fisher distance (closest first = most promising)
    near_misses.sort(key=lambda x: x['fisher_distance'])
    
    print(f"\nPhase 2: Found {len(near_misses)} Near-Misses. Deep-Diving Top {top_n}...")
    
    forensic_reports = []
    
    for idx, nm in enumerate(near_misses[:top_n]):
        task = nm['task']
        result = nm['result']
        
        print("\n" + "="*70)
        print(f"CASE #{idx+1}: Task {task.task_id}")
        print(f"Best Method: {result['method']}")
        print(f"Fisher Distance: {result['fisher_distance']:.4f}")
        print("="*70)
        
        report = {
            'task_id': task.task_id,
            'method': result['method'],
            'fisher_distance': result['fisher_distance'],
            'examples': []
        }
        
        # Analyze each training example
        for ex_idx, ex in enumerate(task.train_examples[:2]):  # First 2 examples
            print(f"\n--- Training Example {ex_idx} ---")
            
            ex_report = {'example_index': ex_idx}
            
            # 1. Visualize grids
            print_grid_ascii(ex.input_grid, f"INPUT (Ex {ex_idx})")
            print_grid_ascii(ex.output_grid, f"TARGET OUTPUT (Ex {ex_idx})")
            
            # 2. Generate prediction using the solver's method
            try:
                pred = solver._apply_method_to_example(result['method'], ex)
                if pred is not None:
                    print_grid_ascii(pred, f"PREDICTION via '{result['method']}'")
                    print_diff_grid(pred, ex.output_grid, "DIFF (X=error)")
                    
                    # Deep diff analysis
                    diff_analysis = analyze_diff_detailed(pred, ex.output_grid)
                    ex_report['diff_analysis'] = diff_analysis
                    
                    print(f"\nDIFF ANALYSIS:")
                    print(f"  Errors: {diff_analysis['error_count']} pixels ({diff_analysis.get('error_ratio', 0):.1%})")
                    if diff_analysis['error_region']:
                        er = diff_analysis['error_region']
                        print(f"  Error Region: rows {er['r_min']}-{er['r_max']}, cols {er['c_min']}-{er['c_max']}")
                    print(f"  Predicted values in errors: {diff_analysis['pred_error_values']}")
                    print(f"  Target values needed: {diff_analysis['target_error_values']}")
                    print(f"  HYPOTHESIS: {diff_analysis['hypothesis']}")
                else:
                    print(f"\n[Could not generate prediction for method '{result['method']}']")
                    ex_report['prediction_failed'] = True
            except Exception as e:
                print(f"\n[Prediction error: {e}]")
                ex_report['prediction_error'] = str(e)
            
            # 3. Input-Output Transform Analysis
            transform = analyze_input_output_transform(ex.input_grid, ex.output_grid)
            ex_report['transform_analysis'] = transform
            
            print(f"\nTRANSFORM ANALYSIS (Input -> Target):")
            print(f"  Shape: {transform['input_shape']} -> {transform['output_shape']}")
            print(f"  Colors In: {transform['input_colors']}")
            print(f"  Colors Out: {transform['output_colors']}")
            if transform.get('new_colors'):
                print(f"  NEW colors: {transform['new_colors']}")
            print(f"  Transform Type: {transform.get('transform_type', 'unknown')}")
            if 'changes_in_interior' in transform:
                print(f"  Changes in Interior: {transform['changes_in_interior']}")
            
            # 4. Object Model Dump
            print(f"\nOBJECT MODEL (What ObjectExtractor sees in INPUT):")
            objects_info = dump_object_model(ex.input_grid)
            ex_report['input_objects'] = objects_info
            
            for obj in objects_info:
                if 'error' in obj:
                    print(f"  [{obj['mode']}] Error: {obj['error']}")
                else:
                    hollow_str = "HOLLOW" if obj['is_hollow'] else "SOLID"
                    print(f"  [{obj['mode']}] Obj {obj['index']}: "
                          f"Color={obj['color']}, Pos={obj['position']}, "
                          f"Size={obj['size']}, {hollow_str}")
            
            # 5. Enclosure Analysis
            enclosure = check_enclosure_status(ex.input_grid)
            ex_report['enclosure_analysis'] = enclosure
            
            print(f"\nENCLOSURE ANALYSIS (DiscoveredPhysics view):")
            if 'error' in enclosure:
                print(f"  Error: {enclosure['error']}")
            else:
                print(f"  Enclosures Found: {enclosure['num_enclosures']}")
                print(f"  Enclosure Pixels: {enclosure['enclosure_pixels']}")
                print(f"  Enclosing Colors: {enclosure['enclosing_colors']}")
            
            report['examples'].append(ex_report)
        
        # Generate overall hypothesis for this task
        print(f"\n{'='*40}")
        print(f"FORENSIC SUMMARY FOR {task.task_id}")
        print(f"{'='*40}")
        
        # Synthesize hypotheses from examples
        hypotheses = []
        for ex_rep in report['examples']:
            if 'diff_analysis' in ex_rep:
                hypotheses.append(ex_rep['diff_analysis'].get('hypothesis', 'unknown'))
        
        if hypotheses:
            print(f"Hypotheses from examples: {hypotheses}")
            
            # Check for consistent hypothesis
            if len(set(hypotheses)) == 1:
                print(f"CONSISTENT HYPOTHESIS: {hypotheses[0]}")
                report['final_hypothesis'] = hypotheses[0]
            else:
                print(f"INCONSISTENT - task may have example-specific logic")
                report['final_hypothesis'] = 'EXAMPLE_CONDITIONAL'
        
        forensic_reports.append(report)
    
    # Final Summary
    print("\n" + "="*70)
    print("FORENSIC SUMMARY: MISSING OPERATORS")
    print("="*70)
    
    hypothesis_counts = {}
    for report in forensic_reports:
        h = report.get('final_hypothesis', 'unknown')
        hypothesis_counts[h] = hypothesis_counts.get(h, 0) + 1
    
    print("\nHypothesis Distribution:")
    for h, count in sorted(hypothesis_counts.items(), key=lambda x: -x[1]):
        print(f"  {h}: {count} tasks")
    
    print("\nRECOMMENDED PHASE 28 OPERATORS:")
    for h in hypothesis_counts:
        if 'FILL_INTERIOR' in h:
            print(f"  - fill_interior_with_adjacent_color()")
        elif 'FILL_RECT' in h:
            print(f"  - fill_rectangle_region()")
        elif 'PATTERN' in h:
            print(f"  - fill_with_pattern() or copy_pattern()")
        elif 'SPARSE' in h:
            print(f"  - modify_specific_pixels()")
    
    return forensic_reports


def main():
    """Main entry point for forensic analysis."""
    print("Initializing Phase 27.5: The Forensic Pathologist...")
    
    # Initialize solver infrastructure
    config = ARCPhase83Config()
    registry = RuleRegistry(persist=True)
    solver = Phase21Solver(config, registry)
    
    # Find data path
    possible_paths = [
        "data/arc/training",
        "C:/Lean4 Projects/data/arc/training",
        "../data/arc/training",
    ]
    
    data_path = None
    for p in possible_paths:
        if Path(p).exists():
            data_path = p
            break
    
    if data_path is None:
        print("ERROR: Could not find ARC training data.")
        print("Tried paths:", possible_paths)
        return
    
    print(f"Loading tasks from: {data_path}")
    tasks = load_arc_tasks(data_path, 'cpu')
    print(f"Loaded {len(tasks)} tasks.")
    
    # Run forensic analysis
    reports = run_forensic_analysis(tasks, solver, top_n=5)
    
    print("\n" + "="*70)
    print("FORENSIC ANALYSIS COMPLETE")
    print("="*70)


if __name__ == "__main__":
    main()
