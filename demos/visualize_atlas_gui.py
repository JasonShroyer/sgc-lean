"""
Graphical Sheaf Atlas Visualization

Real-time matplotlib dashboard showing:
1. Learning curve (perfect solves per iteration)
2. Atlas growth (predicates and charts over time)
3. Manifold graph (charts as nodes, gauge transitions as edges)
4. Gauge distribution pie chart (identity vs non-identity transfers)

Usage:
  python visualize_atlas_gui.py          # One-time snapshot
  python visualize_atlas_gui.py --live   # Auto-refresh every 5 seconds
"""

import os
import sys
import json
import time
import argparse
from pathlib import Path
from collections import defaultdict

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.animation import FuncAnimation
import networkx as nx

ATLAS_DIR = Path(__file__).parent.parent / "data" / "atlas"
ATLAS_FILE = ATLAS_DIR / "sheaf_atlas.json"
PROGRESS_FILE = ATLAS_DIR / "iteration_progress.json"


def load_atlas():
    """Load atlas state from disk."""
    if not ATLAS_FILE.exists():
        return None
    try:
        with open(ATLAS_FILE, 'r') as f:
            return json.load(f)
    except:
        return None


def load_progress():
    """Load iteration progress."""
    if not PROGRESS_FILE.exists():
        return None
    try:
        with open(PROGRESS_FILE, 'r') as f:
            return json.load(f)
    except:
        return None


def create_dashboard(fig, axes):
    """Create the dashboard layout."""
    atlas_data = load_atlas()
    progress_data = load_progress()
    
    # Clear all axes
    for ax in axes.flat:
        ax.clear()
    
    # === Panel 1: Learning Curve ===
    ax1 = axes[0, 0]
    ax1.set_title('Learning Curve (Perfect Solves)', fontsize=12, fontweight='bold')
    
    if progress_data and progress_data.get('iterations'):
        iterations = progress_data['iterations']
        x = [it.get('iteration', i+1) for i, it in enumerate(iterations)]
        y_perfect = [it.get('perfect', 0) for it in iterations]
        y_total = [it.get('total_tasks', 97) for it in iterations]
        
        ax1.fill_between(x, y_perfect, alpha=0.3, color='green')
        ax1.plot(x, y_perfect, 'go-', linewidth=2, markersize=8, label='Perfect')
        ax1.axhline(y=max(y_perfect) if y_perfect else 0, color='green', linestyle='--', alpha=0.5)
        
        ax1.set_xlabel('Iteration')
        ax1.set_ylabel('Tasks Solved')
        ax1.set_ylim(0, max(y_total) * 1.1 if y_total else 100)
        ax1.legend(loc='upper left')
        ax1.grid(True, alpha=0.3)
    else:
        ax1.text(0.5, 0.5, 'No iteration data yet', ha='center', va='center', fontsize=14)
        ax1.set_xlim(0, 1)
        ax1.set_ylim(0, 1)
    
    # === Panel 2: Atlas Growth ===
    ax2 = axes[0, 1]
    ax2.set_title('Atlas Growth', fontsize=12, fontweight='bold')
    
    if progress_data and progress_data.get('iterations'):
        iterations = progress_data['iterations']
        x = [it.get('iteration', i+1) for i, it in enumerate(iterations)]
        y_preds = [it.get('atlas_size', 0) for it in iterations]
        y_charts = [it.get('num_charts', 0) for it in iterations]
        
        ax2.bar([i - 0.2 for i in x], y_preds, width=0.4, label='Predicates', color='blue', alpha=0.7)
        ax2.bar([i + 0.2 for i in x], y_charts, width=0.4, label='Charts', color='orange', alpha=0.7)
        
        ax2.set_xlabel('Iteration')
        ax2.set_ylabel('Count')
        ax2.legend()
        ax2.grid(True, alpha=0.3, axis='y')
    else:
        ax2.text(0.5, 0.5, 'No atlas data yet', ha='center', va='center', fontsize=14)
        ax2.set_xlim(0, 1)
        ax2.set_ylim(0, 1)
    
    # === Panel 3: Manifold Graph ===
    ax3 = axes[1, 0]
    ax3.set_title('Manifold Structure (Chart Graph)', fontsize=12, fontweight='bold')
    
    if atlas_data and atlas_data.get('charts'):
        G = nx.Graph()
        
        # Add chart nodes
        charts = atlas_data.get('charts', {})
        for chart_id, chart_data in charts.items():
            sig = chart_data.get('signature_center', [0, 0, 0])
            n_preds = len(chart_data.get('sections', {}))
            short_id = chart_id[:20] + '...' if len(chart_id) > 20 else chart_id
            G.add_node(short_id, size=max(100, n_preds * 50), sig=sig)
        
        # Add transition edges
        transitions = atlas_data.get('transitions', [])
        edge_gauges = defaultdict(list)
        for t in transitions:
            src = t.get('source_task_id', '')[:8]
            tgt = t.get('target_task_id', '')[:8]
            gauge = t.get('gauge_element', 'e')
            # Map to chart if possible
            edge_gauges[(src, tgt)].append(gauge)
        
        for (src, tgt), gauges in edge_gauges.items():
            if src in G.nodes and tgt in G.nodes:
                # Color by gauge type
                has_non_identity = any(g != 'e' for g in gauges)
                G.add_edge(src, tgt, color='red' if has_non_identity else 'gray', weight=len(gauges))
        
        if G.number_of_nodes() > 0:
            pos = nx.spring_layout(G, seed=42)
            node_sizes = [G.nodes[n].get('size', 200) for n in G.nodes]
            
            # Draw edges
            edge_colors = [G.edges[e].get('color', 'gray') for e in G.edges]
            nx.draw_networkx_edges(G, pos, ax=ax3, edge_color=edge_colors, alpha=0.6)
            
            # Draw nodes
            nx.draw_networkx_nodes(G, pos, ax=ax3, node_size=node_sizes, 
                                   node_color='lightblue', edgecolors='blue', linewidths=2)
            nx.draw_networkx_labels(G, pos, ax=ax3, font_size=8)
            
            ax3.axis('off')
        else:
            ax3.text(0.5, 0.5, 'No chart connections yet', ha='center', va='center', fontsize=14)
            ax3.set_xlim(0, 1)
            ax3.set_ylim(0, 1)
    else:
        ax3.text(0.5, 0.5, 'No manifold data yet', ha='center', va='center', fontsize=14)
        ax3.set_xlim(0, 1)
        ax3.set_ylim(0, 1)
    
    # === Panel 4: Gauge Distribution ===
    ax4 = axes[1, 1]
    ax4.set_title('Gauge Transport Distribution', fontsize=12, fontweight='bold')
    
    if atlas_data:
        stats = atlas_data.get('statistics', {})
        identity = stats.get('identity_transfers', 0)
        gauge = stats.get('gauge_transfers', 0)
        
        if identity + gauge > 0:
            sizes = [identity, gauge]
            labels = [f'Identity (g=e)\n{identity}', f'Gauge (g≠e)\n{gauge}']
            colors = ['lightgray', 'coral']
            explode = (0, 0.1)  # Highlight gauge transfers
            
            ax4.pie(sizes, explode=explode, labels=labels, colors=colors,
                   autopct='%1.1f%%', shadow=True, startangle=90)
            ax4.axis('equal')
            
            # Add annotation
            if gauge > 0:
                ax4.annotate('Holonomy!\n(Non-trivial transport)', 
                           xy=(0.7, -0.3), fontsize=10, color='red', fontweight='bold')
        else:
            ax4.text(0.5, 0.5, 'No gauge transfers yet', ha='center', va='center', fontsize=14)
            ax4.set_xlim(0, 1)
            ax4.set_ylim(0, 1)
    else:
        ax4.text(0.5, 0.5, 'No gauge data yet', ha='center', va='center', fontsize=14)
        ax4.set_xlim(0, 1)
        ax4.set_ylim(0, 1)
    
    # Overall title
    fig.suptitle('Sheaf Atlas: Real-Time Learning on the Semantic Manifold', 
                fontsize=14, fontweight='bold')
    
    plt.tight_layout(rect=[0, 0, 1, 0.96])
    return fig


def update(frame):
    """Update function for animation."""
    global fig, axes
    create_dashboard(fig, axes)
    return []


def main():
    global fig, axes
    
    parser = argparse.ArgumentParser(description='Graphical Sheaf Atlas Visualization')
    parser.add_argument('--live', action='store_true', help='Auto-refresh every 5 seconds')
    parser.add_argument('--interval', type=int, default=5000, help='Refresh interval in ms')
    args = parser.parse_args()
    
    # Create figure
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    if args.live:
        # Animated dashboard
        ani = FuncAnimation(fig, update, interval=args.interval, blit=False, cache_frame_data=False)
        plt.show()
    else:
        # Static snapshot
        create_dashboard(fig, axes)
        plt.show()


if __name__ == "__main__":
    main()
