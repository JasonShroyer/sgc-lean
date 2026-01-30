#!/usr/bin/env python3
"""
SGC Metabolic Core Validator - Visualization

This script visualizes the results of the TCA cycle experiment from MetabolicCore.lean.
It demonstrates the SGC prediction: "Flux Creates Structure"

Run: python visualize_metabolic_core.py
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Circle
from matplotlib.collections import PatchCollection
import matplotlib.patches as mpatches

# Data from the Lean simulation
flux_ratios = [1.0, 2.0, 5.0, 10.0, 20.0, 50.0, 100.0]
entropy_production = [0.0, 0.69, 6.44, 20.72, 56.92, 191.69, 455.91]
total_current = [0.0, 1.0, 4.0, 9.0, 19.0, 49.0, 99.0]
conductance = [0.333] * 7  # Constant for uniform distribution

# Create figure with multiple subplots
fig = plt.figure(figsize=(16, 12))
fig.suptitle('SGC Metabolic Core Validator: TCA Cycle Experiment\n"Does Flux Create Structure?"', 
             fontsize=16, fontweight='bold')

# ============================================================================
# Plot 1: Entropy Production vs Flux Ratio (Log scale)
# ============================================================================
ax1 = fig.add_subplot(2, 3, 1)
ax1.semilogy(flux_ratios, [max(0.01, e) for e in entropy_production], 'b-o', linewidth=2, markersize=8)
ax1.axhline(y=0.01, color='green', linestyle='--', alpha=0.7, label='Equilibrium (σ ≈ 0)')
ax1.fill_between([0, 110], [0.01, 0.01], [0.001, 0.001], alpha=0.2, color='green')
ax1.set_xlabel('Flux Ratio (k_fwd / k_bwd)', fontsize=11)
ax1.set_ylabel('Entropy Production Rate σ', fontsize=11)
ax1.set_title('Diagnostic 1: Entropy Production\n(Signature of Non-Equilibrium)', fontsize=12)
ax1.set_xlim([0, 105])
ax1.grid(True, alpha=0.3)
ax1.legend(loc='lower right')

# Add annotations
ax1.annotate('DEAD\n(Equilibrium)', xy=(1, 0.01), xytext=(5, 0.05),
            fontsize=9, ha='center', color='green',
            arrowprops=dict(arrowstyle='->', color='green', alpha=0.7))
ax1.annotate('ALIVE\n(Driven)', xy=(100, 455.91), xytext=(70, 100),
            fontsize=9, ha='center', color='red',
            arrowprops=dict(arrowstyle='->', color='red', alpha=0.7))

# ============================================================================
# Plot 2: Total Current vs Flux Ratio
# ============================================================================
ax2 = fig.add_subplot(2, 3, 2)
ax2.plot(flux_ratios, total_current, 'r-s', linewidth=2, markersize=8)
ax2.axhline(y=0, color='green', linestyle='--', alpha=0.7)
ax2.set_xlabel('Flux Ratio (k_fwd / k_bwd)', fontsize=11)
ax2.set_ylabel('Total Probability Current |J|', fontsize=11)
ax2.set_title('Diagnostic 2: Net Flux\n(Directed Flow)', fontsize=12)
ax2.set_xlim([0, 105])
ax2.grid(True, alpha=0.3)

# Linear fit to show J ≈ (k_fwd - k_bwd) relationship
ax2.plot(flux_ratios, [r - 1 for r in flux_ratios], 'k--', alpha=0.5, label='J = k_fwd - k_bwd')
ax2.legend()

# ============================================================================
# Plot 3: Phase Diagram (Entropy vs Current)
# ============================================================================
ax3 = fig.add_subplot(2, 3, 3)
colors = plt.cm.RdYlGn_r(np.linspace(0, 1, len(flux_ratios)))
for i, (e, j, r) in enumerate(zip(entropy_production, total_current, flux_ratios)):
    ax3.scatter(j, e, c=[colors[i]], s=150, edgecolors='black', linewidth=1, zorder=5)
    ax3.annotate(f'r={int(r)}', xy=(j, e), xytext=(5, 5), textcoords='offset points', fontsize=8)

ax3.set_xlabel('Total Current |J|', fontsize=11)
ax3.set_ylabel('Entropy Production σ', fontsize=11)
ax3.set_title('Phase Space: σ vs |J|\n(Thermodynamic State)', fontsize=12)
ax3.grid(True, alpha=0.3)

# Add regions
ax3.axvspan(-5, 0.5, alpha=0.1, color='green', label='Equilibrium')
ax3.axvspan(0.5, 110, alpha=0.1, color='red', label='NESS')
ax3.legend(loc='upper left')

# ============================================================================
# Plot 4: TCA Cycle Schematic - DEAD
# ============================================================================
ax4 = fig.add_subplot(2, 3, 4)
ax4.set_aspect('equal')
ax4.set_xlim(-1.5, 1.5)
ax4.set_ylim(-1.5, 1.5)
ax4.axis('off')
ax4.set_title('DEAD: k_fwd = k_bwd = 1\n(Detailed Balance)', fontsize=12, color='green')

# Draw cycle nodes
metabolites = ['Citrate', 'Isocitrate', 'α-KG', 'Suc-CoA', 'Succ', 'OAA']
angles = np.linspace(np.pi/2, np.pi/2 - 2*np.pi, 7)[:-1]
positions = [(np.cos(a), np.sin(a)) for a in angles]

for i, (pos, name) in enumerate(zip(positions, metabolites)):
    circle = Circle(pos, 0.15, facecolor='lightblue', edgecolor='black', linewidth=2)
    ax4.add_patch(circle)
    ax4.text(pos[0], pos[1], str(i), ha='center', va='center', fontsize=10, fontweight='bold')
    ax4.text(pos[0]*1.35, pos[1]*1.35, name, ha='center', va='center', fontsize=7)

# Draw bidirectional arrows (equal both ways)
for i in range(6):
    j = (i + 1) % 6
    dx = positions[j][0] - positions[i][0]
    dy = positions[j][1] - positions[i][1]
    mid_x = (positions[i][0] + positions[j][0]) / 2
    mid_y = (positions[i][1] + positions[j][1]) / 2
    # Forward and backward arrows
    ax4.annotate('', xy=(mid_x + dx*0.15, mid_y + dy*0.15), 
                xytext=(mid_x - dx*0.15, mid_y - dy*0.15),
                arrowprops=dict(arrowstyle='<->', color='gray', lw=1.5))

ax4.text(0, -1.4, 'Net Flux: J = 0\nEntropy Production: σ = 0', ha='center', fontsize=9, 
         bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8))

# ============================================================================
# Plot 5: TCA Cycle Schematic - ALIVE  
# ============================================================================
ax5 = fig.add_subplot(2, 3, 5)
ax5.set_aspect('equal')
ax5.set_xlim(-1.5, 1.5)
ax5.set_ylim(-1.5, 1.5)
ax5.axis('off')
ax5.set_title('ALIVE: k_fwd = 100, k_bwd = 1\n(Driven Cycle)', fontsize=12, color='red')

for i, (pos, name) in enumerate(zip(positions, metabolites)):
    circle = Circle(pos, 0.15, facecolor='lightyellow', edgecolor='red', linewidth=3)
    ax5.add_patch(circle)
    ax5.text(pos[0], pos[1], str(i), ha='center', va='center', fontsize=10, fontweight='bold')
    ax5.text(pos[0]*1.35, pos[1]*1.35, name, ha='center', va='center', fontsize=7)

# Draw thick clockwise arrows (dominant direction)
for i in range(6):
    j = (i + 1) % 6
    start = np.array(positions[i])
    end = np.array(positions[j])
    direction = end - start
    direction = direction / np.linalg.norm(direction)
    start_adj = start + direction * 0.18
    end_adj = end - direction * 0.18
    ax5.annotate('', xy=end_adj, xytext=start_adj,
                arrowprops=dict(arrowstyle='->', color='red', lw=4, mutation_scale=20))

ax5.text(0, -1.4, 'Net Flux: J = 99\nEntropy Production: σ = 455.91', ha='center', fontsize=9,
         bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

# ============================================================================
# Plot 6: Summary Bar Chart
# ============================================================================
ax6 = fig.add_subplot(2, 3, 6)

categories = ['Dead\n(r=1)', 'Moderate\n(r=10)', 'Alive\n(r=100)']
entropy_vals = [0, 20.72, 455.91]
current_vals = [0, 9, 99]

x = np.arange(len(categories))
width = 0.35

bars1 = ax6.bar(x - width/2, [e/10 for e in entropy_vals], width, label='σ / 10', color='blue', alpha=0.7)
bars2 = ax6.bar(x + width/2, current_vals, width, label='|J|', color='red', alpha=0.7)

ax6.set_ylabel('Value', fontsize=11)
ax6.set_title('Comparison: Dead vs Alive\n(Normalized)', fontsize=12)
ax6.set_xticks(x)
ax6.set_xticklabels(categories)
ax6.legend()
ax6.grid(True, alpha=0.3, axis='y')

# Add value labels on bars
for bar, val in zip(bars1, entropy_vals):
    height = bar.get_height()
    ax6.annotate(f'σ={val:.0f}', xy=(bar.get_x() + bar.get_width()/2, height),
                xytext=(0, 3), textcoords='offset points', ha='center', va='bottom', fontsize=8)
for bar, val in zip(bars2, current_vals):
    height = bar.get_height()
    ax6.annotate(f'J={val}', xy=(bar.get_x() + bar.get_width()/2, height),
                xytext=(0, 3), textcoords='offset points', ha='center', va='bottom', fontsize=8)

plt.tight_layout(rect=[0, 0.03, 1, 0.95])

# Add footer
fig.text(0.5, 0.01, 
         '✓ SGC Prediction Confirmed: Flux Creates Structure — Entropy production is the thermodynamic cost of "aliveness"',
         ha='center', fontsize=11, style='italic', 
         bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

# Save figure
plt.savefig('metabolic_core_results.png', dpi=150, bbox_inches='tight')
plt.savefig('metabolic_core_results.svg', bbox_inches='tight')
print("Figures saved: metabolic_core_results.png, metabolic_core_results.svg")

plt.show()
