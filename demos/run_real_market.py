#!/usr/bin/env python3
"""
Real Market Data Analysis with SGC Zero-Parameter Engine
=========================================================
Downloads actual market data and runs the full Cartan-Killing
lift tournament to detect any hidden conservation laws.
"""
import numpy as np
import sys, os, csv, json
from urllib.request import urlopen, Request
from datetime import datetime, timedelta

sys.path.insert(0, os.path.dirname(__file__))
from sgc_universal import crystallize_universal
from sgc_zero_param import discover


def download_yahoo_csv(ticker: str, period1: int, period2: int) -> str:
    """Download historical data from Yahoo Finance as CSV text."""
    url = (f"https://query1.finance.yahoo.com/v7/finance/download/{ticker}"
           f"?period1={period1}&period2={period2}&interval=1d"
           f"&events=history&includeAdjustedClose=true")
    req = Request(url, headers={'User-Agent': 'Mozilla/5.0'})
    resp = urlopen(req, timeout=30)
    return resp.read().decode('utf-8')


def parse_yahoo_csv(text: str) -> dict:
    """Parse Yahoo Finance CSV into dict of arrays."""
    lines = text.strip().split('\n')
    reader = csv.DictReader(lines)
    data = {'Date': [], 'Open': [], 'High': [], 'Low': [],
            'Close': [], 'Volume': [], 'Adj Close': []}
    for row in reader:
        try:
            data['Date'].append(row['Date'])
            data['Open'].append(float(row['Open']))
            data['High'].append(float(row['High']))
            data['Low'].append(float(row['Low']))
            data['Close'].append(float(row['Close']))
            data['Volume'].append(float(row['Volume']))
            data['Adj Close'].append(float(row.get('Adj Close', row['Close'])))
        except (ValueError, KeyError):
            continue
    return {k: np.array(v) if k != 'Date' else v for k, v in data.items()}


def main():
    # Time range: last 3 years
    end = int(datetime.now().timestamp())
    start = int((datetime.now() - timedelta(days=3*365)).timestamp())

    print("#" * 70)
    print("# SGC REAL MARKET ANALYSIS")
    print(f"# Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print("#" * 70)

    # Download tickers
    tickers = {
        'SPY': 'S&P 500 ETF',
        '^VIX': 'CBOE Volatility Index',
        'GLD': 'Gold ETF',
        'TLT': 'Treasury Bond ETF (20yr)',
    }

    all_data = {}
    for ticker, desc in tickers.items():
        print(f"\n  Downloading {ticker} ({desc})...")
        try:
            text = download_yahoo_csv(ticker, start, end)
            parsed = parse_yahoo_csv(text)
            n = len(parsed['Close'])
            print(f"    Got {n} trading days")
            if n > 100:
                all_data[ticker] = parsed
            else:
                print(f"    Too few data points, skipping")
        except Exception as e:
            print(f"    Failed: {e}")

    if len(all_data) < 2:
        print("\n  Not enough data downloaded. Using fallback synthetic market.")
        print("  (Yahoo Finance may require authentication or different endpoint)")
        run_fallback()
        return

    # Align dates across all tickers
    common_dates = set(all_data[list(all_data.keys())[0]]['Date'])
    for ticker in all_data:
        common_dates &= set(all_data[ticker]['Date'])
    common_dates = sorted(common_dates)
    print(f"\n  Common trading days: {len(common_dates)}")
    print(f"  Date range: {common_dates[0]} to {common_dates[-1]}")

    if len(common_dates) < 100:
        print("  Too few common dates. Using fallback.")
        run_fallback()
        return

    # Build aligned arrays
    columns = []
    col_names = []
    for ticker in all_data:
        date_to_idx = {d: i for i, d in enumerate(all_data[ticker]['Date'])}
        close = np.array([all_data[ticker]['Close'][date_to_idx[d]]
                          for d in common_dates])
        columns.append(close)
        col_names.append(ticker.replace('^', ''))

    X_raw = np.column_stack(columns)
    T, D = X_raw.shape
    print(f"  State vector: {T} days x {D} assets: {col_names}")

    # Also compute returns and log-returns
    returns = np.diff(X_raw, axis=0) / X_raw[:-1]
    log_returns = np.diff(np.log(X_raw), axis=0)

    # Build enriched state: [prices, returns, realized_vol]
    realized_vol = np.abs(log_returns) * np.sqrt(252)
    X_enriched = np.column_stack([
        X_raw[1:],           # prices (aligned with returns)
        log_returns,          # log returns
    ])
    enriched_names = [f'{n}_price' for n in col_names] + [f'{n}_ret' for n in col_names]

    # Normalize
    X_norm = (X_enriched - X_enriched.mean(0)) / X_enriched.std(0)

    run_analysis(X_norm, enriched_names, common_dates[1:])


def run_fallback():
    """Generate realistic synthetic market data if download fails."""
    print("\n  Generating synthetic market data (OU processes)...")
    np.random.seed(42)
    N = 1000

    # SPY: geometric Brownian motion with drift
    spy = [400.0]
    for _ in range(N - 1):
        spy.append(spy[-1] * np.exp(0.0003 + 0.012 * np.random.randn()))
    spy = np.array(spy)

    # VIX: mean-reverting (OU process around 20)
    vix = [20.0]
    for _ in range(N - 1):
        vix.append(vix[-1] + 0.05 * (20 - vix[-1]) + 3.0 * np.random.randn())
        vix[-1] = max(vix[-1], 9)
    vix = np.array(vix)

    # GLD: correlated with VIX (flight to safety)
    gld = [180.0]
    for i in range(N - 1):
        gld.append(gld[-1] * np.exp(0.0001 + 0.008 * np.random.randn()
                                     + 0.002 * (vix[i+1] - vix[i]) / 20))
    gld = np.array(gld)

    # TLT: inverse correlated with SPY
    tlt = [100.0]
    for i in range(N - 1):
        spy_ret = (spy[i+1] - spy[i]) / spy[i]
        tlt.append(tlt[-1] * np.exp(0.0001 - 0.3 * spy_ret + 0.005 * np.random.randn()))
    tlt = np.array(tlt)

    X_raw = np.column_stack([spy, vix, gld, tlt])
    col_names = ['SPY', 'VIX', 'GLD', 'TLT']
    log_returns = np.diff(np.log(X_raw), axis=0)
    X_enriched = np.column_stack([X_raw[1:], log_returns])
    enriched_names = [f'{n}_price' for n in col_names] + [f'{n}_ret' for n in col_names]
    X_norm = (X_enriched - X_enriched.mean(0)) / X_enriched.std(0)

    dates = [(datetime(2022, 1, 3) + timedelta(days=i)).strftime('%Y-%m-%d')
             for i in range(len(X_norm))]
    run_analysis(X_norm, enriched_names, dates)


def run_analysis(X: np.ndarray, col_names: list, dates: list):
    """Run the full SGC analysis on market data."""
    T, D = X.shape
    print(f"\n{'='*60}")
    print(f"ANALYZING: {T} days x {D} features")
    print(f"Features: {', '.join(col_names)}")
    print(f"{'='*60}")

    # 1. Zero-param engine (dynamics + manifold)
    print(f"\n--- ZERO-PARAMETER ENGINE ---")
    result = discover(X, col_names, verbose=True)

    # 2. Full Cartan-Killing lift tournament
    print(f"\n--- CARTAN-KILLING LIFT TOURNAMENT ---")
    # Use only prices for the tournament (avoid D > 6 for higher lifts)
    n_prices = D // 2  # first half are prices
    X_prices = X[:, :n_prices]
    price_names = col_names[:n_prices]
    print(f"  Using price dimensions only: {price_names} ({n_prices}D)")

    r_univ = crystallize_universal(X_prices, k=1, lambda_mdl=0.01)

    # 3. Variance profile across degrees
    print(f"\n--- VARIANCE-VS-DEGREE PROFILE ---")
    print(f"  (The degree where variance first drops reveals the symmetry group)")
    print(f"  {'Degree':>6s}  {'Lift':>15s}  {'Variance':>12s}  {'MDL':>10s}  {'Drop':>8s}")
    print(f"  {'-'*6}  {'-'*15}  {'-'*12}  {'-'*10}  {'-'*8}")

    sorted_lifts = sorted(r_univ.mdl_scores.items(), key=lambda x: x[1])
    prev_var = None
    for name, mdl in sorted_lifts[:8]:
        from sgc_universal import LIFT_LIBRARY, score_lift, _lift_degree
        degree = _lift_degree(name)
        fn = LIFT_LIBRARY[name]
        _, _, vars_, _ = score_lift(X_prices, fn, k=1, lambda_mdl=0.01, lift_name=name)
        v = vars_[0] if vars_ else float('inf')
        drop = f"{prev_var/v:.1f}x" if prev_var and v > 0 else "---"
        print(f"  {degree:>6d}  {name:>15s}  {v:>12.4e}  {mdl:>10.4f}  {drop:>8s}")
        prev_var = v

    # 4. Summary verdict
    print(f"\n{'='*60}")
    print("MARKET PHYSICS VERDICT")
    print(f"{'='*60}")
    print(f"  Dynamics T* = {result.validity_horizon:.2f}")
    print(f"  Tsallis q = {result.spectral_profile.tsallis_q:.3f}")
    print(f"  MDL Winner: {r_univ.winning_lift}")

    if result.validity_horizon > 10:
        print(f"\n  ** STRUCTURE DETECTED: T* = {result.validity_horizon:.1f} **")
        print(f"  The market has predictable dynamics for ~{result.validity_horizon:.0f} steps")
        if result.manifold_wins:
            print(f"  Manifold mode found conservation law (quadratic invariant)")
    elif result.validity_horizon > 1:
        print(f"\n  WEAK STRUCTURE: T* = {result.validity_horizon:.2f}")
        print(f"  Short-horizon approximate symmetry (EFT regime)")
    else:
        print(f"\n  H0 SUPPORTED: T* = {result.validity_horizon:.2f} < 1")
        print(f"  No conservation law detected at any polynomial degree.")
        print(f"  The market is a non-conservative, open system.")

    # Check if any lift found low variance
    best_var = min(r_univ.variances) if r_univ.variances else float('inf')
    if best_var < 0.01:
        print(f"\n  ** LOW VARIANCE DETECTED: {best_var:.4e} at {r_univ.winning_lift} **")
        print(f"  This suggests a hidden approximate constraint.")
    else:
        print(f"\n  All lift variances > 0.01 — no approximate conservation law.")


if __name__ == '__main__':
    main()
