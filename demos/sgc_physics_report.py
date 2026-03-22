#!/usr/bin/env python3
"""
SGC Physics Report Generator
=============================
Takes a RelationalRule (from the engine) and DataMetadata (from the loader)
and produces a human-readable physics report + JSON summary.
"""
import numpy as np
import json
from typing import Optional
from dataclasses import asdict

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from sgc_relational_engine import RelationalRule
from sgc_universal_loader import DataMetadata


def generate_report(rule: RelationalRule, meta: Optional[DataMetadata] = None,
                    noise_rule: Optional[RelationalRule] = None) -> str:
    """Generate a human-readable physics report from an SGC result."""
    lines = []
    lines.append("=" * 70)
    lines.append("SGC PHYSICS DISCOVERY REPORT")
    lines.append("=" * 70)

    if meta:
        lines.append(f"\nSource: {meta.source_path}")
        lines.append(f"Format: {meta.source_format}")
        lines.append(f"Dimensions: T={meta.T}, D={meta.D}")
        lines.append(f"Variables: {', '.join(meta.columns)}")

    # Section 1: Topology Certificate
    lines.append(f"\n{'=' * 70}")
    lines.append("SECTION 1: TOPOLOGY CERTIFICATE")
    lines.append(f"{'=' * 70}")
    lines.append(f"  Betti number b1 = {rule.b1}")
    if rule.b1 == 0:
        lines.append("  RESULT: No conservation laws detected (b1 = 0)")
        lines.append("  The system does not exhibit closed coupling loops.")
    elif rule.b1 == 1:
        lines.append("  RESULT: One conservation law detected (b1 = 1)")
        lines.append("  The system has a single conserved quantity.")
    else:
        lines.append(f"  RESULT: {rule.b1} independent conservation loops detected")
    lines.append(f"  Crystallized edges: {rule.crystallized_edges}")
    lines.append(f"  MDL: {rule.mdl_bits:.0f} bits ({int(rule.mdl_bits/32)} parameters)")

    # Section 2: Conservation Laws
    lines.append(f"\n{'=' * 70}")
    lines.append("SECTION 2: DISCOVERED CONSERVATION LAWS")
    lines.append(f"{'=' * 70}")

    R = rule.R_self
    d = rule.state_dim
    col_names = meta.columns if meta else [f'x{i}' for i in range(d)]

    # Find coupling loops: off-diagonal entries of R
    adj = np.abs(R) > 1e-10
    np.fill_diagonal(adj, False)

    if rule.b1 >= 1:
        # Find the coupling structure
        lines.append(f"\n  Transition matrix R ({d}x{d}):")
        for i in range(d):
            row = '  '.join(f'{R[i,j]:+8.4f}' for j in range(d))
            lines.append(f"    [{row}]  <- {col_names[i]}")

        # Identify coupled pairs
        lines.append(f"\n  Coupling structure:")
        for i in range(d):
            for j in range(d):
                if i != j and abs(R[i, j]) > 0.01:
                    sign = "+" if R[i, j] > 0 else "-"
                    lines.append(f"    {col_names[i]} <- {sign}{abs(R[i,j]):.4f} * {col_names[j]}")

        # Conservation law interpretation
        lines.append(f"\n  Conservation law interpretation:")
        lines.append(f"    The coupling graph has {rule.b1} cycle(s).")
        if rule.b1 >= 1 and d >= 2:
            # For 2-cycle: variables i and j couple in both directions
            for i in range(d):
                for j in range(i+1, d):
                    if abs(R[i, j]) > 0.01 and abs(R[j, i]) > 0.01:
                        ratio = abs(R[i, j] / R[j, i]) if abs(R[j, i]) > 1e-10 else float('inf')
                        lines.append(f"    Feedback loop: {col_names[i]} <-> {col_names[j]} "
                                     f"(ratio |R[{i},{j}]/R[{j},{i}]| = {ratio:.4f})")
    else:
        lines.append("  No conservation laws found.")
        lines.append(f"\n  Transition matrix R ({d}x{d}):")
        for i in range(d):
            row = '  '.join(f'{R[i,j]:+8.4f}' for j in range(d))
            lines.append(f"    [{row}]")

    # Section 3: Comparison Baseline
    lines.append(f"\n{'=' * 70}")
    lines.append("SECTION 3: COMPARISON BASELINE (OLS)")
    lines.append(f"{'=' * 70}")
    lines.append(f"  SGC functional defect: {rule.functional_defect:.6e}")
    lines.append(f"  SGC validity horizon T* = {rule.validity_horizon:.2f}")
    lines.append(f"  ||R - I||_F = {np.linalg.norm(R - np.eye(d)):.6f}")

    # Section 4: Confidence Assessment
    lines.append(f"\n{'=' * 70}")
    lines.append("SECTION 4: CONFIDENCE ASSESSMENT")
    lines.append(f"{'=' * 70}")
    lines.append(f"  Defect cost: {rule.functional_defect:.6e}")
    if rule.functional_defect < 1e-4:
        lines.append("  Confidence: HIGH (defect < 1e-4)")
    elif rule.functional_defect < 1e-2:
        lines.append("  Confidence: MEDIUM (defect < 1e-2)")
    else:
        lines.append("  Confidence: LOW (defect >= 1e-2)")

    if meta and meta.T < 100:
        lines.append(f"  WARNING: Low sample size (T={meta.T} < 100)")

    # Noise sensitivity
    if noise_rule is not None:
        b1_changed = noise_rule.b1 != rule.b1
        lines.append(f"\n  Noise sensitivity (10% added noise):")
        lines.append(f"    b1 original: {rule.b1}")
        lines.append(f"    b1 with noise: {noise_rule.b1}")
        if b1_changed:
            lines.append("    WARNING: Result is SENSITIVE to noise")
        else:
            lines.append("    Result is ROBUST to noise")

    lines.append(f"\n{'=' * 70}")
    lines.append("END OF REPORT")
    lines.append(f"{'=' * 70}")

    return '\n'.join(lines)


def generate_json_summary(rule: RelationalRule, meta: Optional[DataMetadata] = None) -> dict:
    """Generate a JSON-serializable summary."""
    summary = {
        'b1': rule.b1,
        'functional_defect': rule.functional_defect,
        'validity_horizon': rule.validity_horizon,
        'mdl_bits': rule.mdl_bits,
        'crystallized_edges': rule.crystallized_edges,
        'state_dim': rule.state_dim,
        'R_self': rule.R_self.tolist(),
    }
    if meta:
        summary['source'] = meta.source_path
        summary['columns'] = meta.columns
        summary['T'] = meta.T
        summary['D'] = meta.D
    return summary
