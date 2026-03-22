#!/usr/bin/env python3
"""
Real Market Analysis: SPX, VIX, GLD (5-year daily data from xlsx)
"""
import numpy as np
import sys, os
from datetime import datetime

sys.path.insert(0, os.path.dirname(__file__))
from sgc_universal import crystallize_universal, LIFT_LIBRARY, score_lift, _lift_degree
from sgc_zero_param import discover

import openpyxl


def load_xlsx(path: str) -> dict:
    """Load OHLCV from xlsx, return {date_str: close_price}."""
    wb = openpyxl.load_workbook(path, read_only=True)
    ws = wb.active
    data = {}
    for row in ws.iter_rows(min_row=2, values_only=True):
        if row[0] is None:
            continue
        dt = row[0]
        if isinstance(dt, datetime):
            date_str = dt.strftime('%Y-%m-%d')
        else:
            date_str = str(dt)
        close = row[4]  # Close column
        if close is None or close == '-':
            continue
        try:
            data[date_str] = float(close)
        except (ValueError, TypeError):
            continue
    wb.close()
    return data


def main():
    data_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'Market Data'))

    print("#" * 70)
    print("# SGC REAL MARKET ANALYSIS")
    print("# Data: SPX, VIX, GLD — 5 years daily")
    print(f"# Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print("#" * 70)

    # Load each ticker
    spx = load_xlsx(os.path.join(data_dir, 'SPX 5yr.xlsx'))
    vix = load_xlsx(os.path.join(data_dir, 'VIX 5yr.xlsx'))
    gld = load_xlsx(os.path.join(data_dir, 'GLD 5yr.xlsx'))

    print(f"\n  SPX: {len(spx)} trading days")
    print(f"  VIX: {len(vix)} trading days")
    print(f"  GLD: {len(gld)} trading days")

    # Align by common dates
    common = sorted(set(spx.keys()) & set(vix.keys()) & set(gld.keys()))
    print(f"  Common dates: {len(common)}")
    print(f"  Range: {common[0]} to {common[-1]}")

    spx_arr = np.array([spx[d] for d in common])
    vix_arr = np.array([vix[d] for d in common])
    gld_arr = np.array([gld[d] for d in common])

    print(f"\n  SPX: {spx_arr[0]:.2f} -> {spx_arr[-1]:.2f}")
    print(f"  VIX: {vix_arr[0]:.2f} -> {vix_arr[-1]:.2f}")
    print(f"  GLD: {gld_arr[0]:.2f} -> {gld_arr[-1]:.2f}")

    # Compute log returns
    spx_ret = np.diff(np.log(spx_arr))
    vix_ret = np.diff(np.log(vix_arr))
    gld_ret = np.diff(np.log(gld_arr))

    # Build state vectors — two versions to test
    # Version A: Raw prices (3D)
    X_prices = np.column_stack([spx_arr[1:], vix_arr[1:], gld_arr[1:]])
    price_names = ['SPX', 'VIX', 'GLD']

    # Version B: Prices + returns (6D)
    X_full = np.column_stack([spx_arr[1:], vix_arr[1:], gld_arr[1:],
                               spx_ret, vix_ret, gld_ret])
    full_names = ['SPX', 'VIX', 'GLD', 'SPX_ret', 'VIX_ret', 'GLD_ret']

    # Version C: Returns only (3D) — stationary
    X_returns = np.column_stack([spx_ret, vix_ret, gld_ret])
    ret_names = ['SPX_ret', 'VIX_ret', 'GLD_ret']

    # Normalize all versions
    for X in [X_prices, X_full, X_returns]:
        X[:] = (X - X.mean(0)) / X.std(0)

    # ================================================================
    # ANALYSIS A: RAW PRICES (3D)
    # ================================================================
    print(f"\n{'='*60}")
    print("ANALYSIS A: RAW PRICES [SPX, VIX, GLD] (3D)")
    print(f"{'='*60}")
    rA = discover(X_prices, price_names, verbose=True)

    print(f"\n  MDL LIFT TOURNAMENT (prices):")
    rAu = crystallize_universal(X_prices, k=1, lambda_mdl=0.01)

    # ================================================================
    # ANALYSIS B: RETURNS ONLY (3D, stationary)
    # ================================================================
    print(f"\n{'='*60}")
    print("ANALYSIS B: LOG RETURNS [SPX_ret, VIX_ret, GLD_ret] (3D)")
    print(f"{'='*60}")
    rB = discover(X_returns, ret_names, verbose=True)

    print(f"\n  MDL LIFT TOURNAMENT (returns):")
    rBu = crystallize_universal(X_returns, k=1, lambda_mdl=0.01)

    # ================================================================
    # ANALYSIS C: PRICES + RETURNS (6D)
    # ================================================================
    print(f"\n{'='*60}")
    print("ANALYSIS C: PRICES + RETURNS (6D)")
    print(f"{'='*60}")
    rC = discover(X_full, full_names, verbose=True)

    # ================================================================
    # VARIANCE-VS-DEGREE PROFILE (on returns, most stationary)
    # ================================================================
    print(f"\n{'='*60}")
    print("VARIANCE-VS-DEGREE PROFILE (returns)")
    print(f"{'='*60}")
    print(f"  {'Degree':>6s}  {'Lift':>15s}  {'Variance':>12s}  {'MDL':>10s}")
    print(f"  {'-'*6}  {'-'*15}  {'-'*12}  {'-'*10}")

    degree_results = []
    for name, fn in LIFT_LIBRARY.items():
        try:
            mdl, _, vars_, _ = score_lift(X_returns, fn, k=1, lambda_mdl=0.01, lift_name=name)
            degree = _lift_degree(name)
            v = vars_[0] if vars_ else float('inf')
            degree_results.append((degree, name, v, mdl))
        except Exception:
            pass

    degree_results.sort(key=lambda x: x[3])
    for deg, name, v, mdl in degree_results:
        print(f"  {deg:>6d}  {name:>15s}  {v:>12.4e}  {mdl:>10.4f}")

    # ================================================================
    # FINAL VERDICT
    # ================================================================
    print(f"\n{'#'*70}")
    print("# REAL MARKET PHYSICS VERDICT")
    print(f"{'#'*70}")
    print(f"\n  {'Analysis':<35s} {'T*':>8s}  {'b1':>3s}  {'q':>6s}  {'Manifold':>10s}")
    print(f"  {'-'*35} {'-'*8}  {'-'*3}  {'-'*6}  {'-'*10}")
    print(f"  {'A. Raw prices (3D)':<35s} {rA.validity_horizon:>8.2f}  {rA.b1:>3d}  {rA.spectral_profile.tsallis_q:>6.3f}  {'YES' if rA.manifold_wins else 'NO':>10s}")
    print(f"  {'B. Log returns (3D)':<35s} {rB.validity_horizon:>8.2f}  {rB.b1:>3d}  {rB.spectral_profile.tsallis_q:>6.3f}  {'YES' if rB.manifold_wins else 'NO':>10s}")
    print(f"  {'C. Prices + returns (6D)':<35s} {rC.validity_horizon:>8.2f}  {rC.b1:>3d}  {rC.spectral_profile.tsallis_q:>6.3f}  {'YES' if rC.manifold_wins else 'NO':>10s}")

    print(f"\n  MDL Winners:")
    print(f"    Prices:  {rAu.winning_lift} (var={rAu.variances[0]:.4e})")
    print(f"    Returns: {rBu.winning_lift} (var={rBu.variances[0]:.4e})")

    # Interpretation
    best_T = max(rA.validity_horizon, rB.validity_horizon, rC.validity_horizon)
    if best_T > 10:
        print(f"\n  ** STRUCTURE DETECTED: best T* = {best_T:.1f} **")
    elif best_T > 1:
        print(f"\n  WEAK STRUCTURE: best T* = {best_T:.2f} (EFT regime)")
    else:
        print(f"\n  H0 SUPPORTED: best T* = {best_T:.2f} < 1")
        print(f"  No conservation law at any polynomial degree 1-8.")

    any_low_var = False
    for label, ru in [("Prices", rAu), ("Returns", rBu)]:
        if ru.variances and min(ru.variances) < 0.01:
            print(f"\n  ** {label}: low variance {min(ru.variances):.4e} at {ru.winning_lift} **")
            any_low_var = True

    if not any_low_var:
        print(f"\n  All variances > 0.01 across all lifts — no approximate conservation law.")
        print(f"  The market (SPX/VIX/GLD) is a genuinely non-conservative, open system.")


if __name__ == '__main__':
    main()
