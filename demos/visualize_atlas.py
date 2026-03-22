"""
Real-Time Sheaf Atlas Visualization

This script provides a live dashboard showing:
1. Atlas growth over iterations (predicates, charts)
2. Gauge transfer statistics (identity vs non-identity)
3. Manifold structure as a graph (charts as nodes, transitions as edges)
4. Task solve progress

Usage:
  python visualize_atlas.py          # One-time snapshot
  python visualize_atlas.py --watch  # Auto-refresh every 5 seconds
"""

import os
import sys
import json
import time
import argparse
from pathlib import Path
from collections import defaultdict

# ASCII art for console visualization
CLEAR = "\033[2J\033[H" if os.name != 'nt' else ""

ATLAS_DIR = Path(__file__).parent.parent / "data" / "atlas"
ATLAS_FILE = ATLAS_DIR / "sheaf_atlas.json"
PROGRESS_FILE = ATLAS_DIR / "iteration_progress.json"


def load_atlas():
    """Load atlas state from disk."""
    if not ATLAS_FILE.exists():
        return None
    with open(ATLAS_FILE, 'r') as f:
        return json.load(f)


def load_progress():
    """Load iteration progress."""
    if not PROGRESS_FILE.exists():
        return None
    with open(PROGRESS_FILE, 'r') as f:
        return json.load(f)


def render_bar(value, max_value, width=40, filled='#', empty='-'):
    """Render a progress bar."""
    if max_value == 0:
        return empty * width
    fill_count = int(width * value / max_value)
    return filled * fill_count + empty * (width - fill_count)


def render_manifold_ascii(atlas_data):
    """
    Render the manifold structure as ASCII art.
    
    Charts are nodes, transitions are edges.
    This shows the topological structure of the learned semantic space.
    """
    if not atlas_data:
        return "  (no atlas data)"
    
    charts = atlas_data.get('charts', {})
    transitions = atlas_data.get('transitions', [])
    
    if not charts:
        return "  (no charts yet)"
    
    lines = []
    lines.append("  MANIFOLD STRUCTURE (Charts as nodes)")
    lines.append("  " + "-" * 50)
    
    # Build adjacency from transitions
    adjacency = defaultdict(set)
    gauge_counts = defaultdict(lambda: defaultdict(int))
    
    for t in transitions:
        src = t.get('source_task_id', '')[:8]
        tgt = t.get('target_task_id', '')[:8]
        gauge = t.get('gauge_element', 'e')
        adjacency[src].add(tgt)
        gauge_counts[src][gauge] += 1
    
    # Show each chart
    for chart_id, chart_data in list(charts.items())[:10]:  # Limit to 10 charts
        sig = chart_data.get('signature_center', [])
        n_preds = len(chart_data.get('sections', {}))
        n_tasks = len(chart_data.get('task_ids', []))
        
        # Format signature
        if sig:
            sig_str = f"({sig[0]:.1f},{sig[1]:.1f},{sig[2]:.1f},...)"
        else:
            sig_str = "(unknown)"
        
        lines.append(f"  [CHART] {sig_str}")
        lines.append(f"    Predicates: {n_preds}  |  Tasks: {n_tasks}")
        
        # Show tasks in this chart
        for task_id in list(chart_data.get('task_ids', []))[:3]:
            lines.append(f"      - {task_id}")
        if n_tasks > 3:
            lines.append(f"      ... and {n_tasks - 3} more")
        lines.append("")
    
    if len(charts) > 10:
        lines.append(f"  ... and {len(charts) - 10} more charts")
    
    # Show gauge transfer graph
    if transitions:
        lines.append("")
        lines.append("  GAUGE TRANSFER GRAPH")
        lines.append("  " + "-" * 50)
        
        # Count gauge element usage
        gauge_totals = defaultdict(int)
        for t in transitions:
            gauge_totals[t.get('gauge_element', 'e')] += 1
        
        for gauge, count in sorted(gauge_totals.items(), key=lambda x: -x[1])[:5]:
            bar = render_bar(count, max(gauge_totals.values()), width=30)
            marker = "*" if gauge != 'e' else " "
            lines.append(f"  {marker} {gauge:10s} [{bar}] {count}")
    
    return "\n".join(lines)


def render_dashboard(atlas_data, progress_data):
    """Render the full dashboard."""
    lines = []
    
    # Header
    lines.append("=" * 70)
    lines.append("        SHEAF ATLAS LIVE VISUALIZATION")
    lines.append("        Real-Time Learning on the Semantic Manifold")
    lines.append("=" * 70)
    lines.append("")
    
    # Iteration progress
    if progress_data and progress_data.get('iterations'):
        iterations = progress_data['iterations']
        current = iterations[-1] if iterations else {}
        
        lines.append("  ITERATION PROGRESS")
        lines.append("  " + "-" * 50)
        lines.append(f"  Current Iteration: {current.get('iteration', 0)}")
        lines.append(f"  Perfect Solves:    {current.get('perfect', 0)} / {current.get('total_tasks', 0)}")
        lines.append(f"  Best Ever:         {progress_data.get('best_perfect', 0)} (iter {progress_data.get('best_iteration', 0)})")
        lines.append("")
        
        # Progress chart
        lines.append("  LEARNING CURVE")
        lines.append("  " + "-" * 50)
        max_perfect = max(it.get('perfect', 0) for it in iterations) if iterations else 1
        for it in iterations[-10:]:  # Show last 10 iterations
            bar = render_bar(it.get('perfect', 0), max_perfect, width=30)
            lines.append(f"  Iter {it.get('iteration', 0):2d}: [{bar}] {it.get('perfect', 0)}")
        lines.append("")
    
    # Atlas statistics
    if atlas_data:
        stats = atlas_data.get('statistics', {})
        charts = atlas_data.get('charts', {})
        transitions = atlas_data.get('transitions', [])
        
        total_preds = sum(len(c.get('sections', {})) for c in charts.values())
        
        lines.append("  ATLAS STATISTICS")
        lines.append("  " + "-" * 50)
        lines.append(f"  Total Predicates:    {total_preds}")
        lines.append(f"  Number of Charts:    {len(charts)}")
        lines.append(f"  Total Transitions:   {len(transitions)}")
        lines.append(f"  Successful Lookups:  {stats.get('successful_transfers', 0)}")
        lines.append(f"    - Identity (g=e):  {stats.get('identity_transfers', 0)}")
        lines.append(f"    - Gauge (g!=e):    {stats.get('gauge_transfers', 0)}")
        lines.append("")
        
        # Gauge transfer ratio
        total_transfers = stats.get('successful_transfers', 0)
        gauge_transfers = stats.get('gauge_transfers', 0)
        if total_transfers > 0:
            ratio = gauge_transfers / total_transfers
            bar = render_bar(gauge_transfers, total_transfers, width=30, filled='G', empty='I')
            lines.append(f"  GAUGE vs IDENTITY: [{bar}]")
            lines.append(f"  Gauge Ratio: {100*ratio:.1f}% (higher = more holonomy)")
            lines.append("")
    
    # Manifold visualization
    lines.append(render_manifold_ascii(atlas_data))
    
    # Footer
    lines.append("")
    lines.append("=" * 70)
    lines.append(f"  Last updated: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append("  Press Ctrl+C to exit")
    lines.append("=" * 70)
    
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description='Visualize Sheaf Atlas')
    parser.add_argument('--watch', action='store_true', help='Auto-refresh every 5 seconds')
    parser.add_argument('--interval', type=int, default=5, help='Refresh interval in seconds')
    args = parser.parse_args()
    
    try:
        while True:
            # Load current state
            atlas_data = load_atlas()
            progress_data = load_progress()
            
            # Clear screen and render
            if CLEAR:
                print(CLEAR, end='')
            
            dashboard = render_dashboard(atlas_data, progress_data)
            print(dashboard)
            
            if not args.watch:
                break
            
            time.sleep(args.interval)
            
    except KeyboardInterrupt:
        print("\n\nVisualization stopped.")


if __name__ == "__main__":
    main()
