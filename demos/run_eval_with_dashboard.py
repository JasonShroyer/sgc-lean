"""
Run evaluation with console output capture for dashboard visualization.

This script runs the iterative atlas evaluation while capturing all
console output to a file that the dashboard can read.

Usage:
  python run_eval_with_dashboard.py [--limit N]
"""

import os
import sys
import subprocess
import threading
from pathlib import Path
from datetime import datetime

ATLAS_DIR = Path(__file__).parent.parent / "data" / "atlas"
LOG_FILE = ATLAS_DIR / "console_output.txt"


def run_evaluation(limit=None):
    """Run the evaluation and capture output."""
    ATLAS_DIR.mkdir(parents=True, exist_ok=True)
    
    # Clear old log
    LOG_FILE.write_text("")
    
    # Build command
    cmd = [sys.executable, "eval_iterative_atlas.py"]
    if limit:
        cmd.extend(["--limit", str(limit)])
    
    print(f"Starting evaluation...")
    print(f"Log file: {LOG_FILE}")
    print(f"Dashboard: http://localhost:5050")
    print("-" * 60)
    
    # Run with real-time output capture
    env = os.environ.copy()
    env['PYTHONUNBUFFERED'] = '1'
    env['SGFE_USE_SHEAF_ATLAS'] = '1'
    
    process = subprocess.Popen(
        cmd,
        cwd=str(Path(__file__).parent),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
        env=env
    )
    
    with open(LOG_FILE, 'w', encoding='utf-8') as log:
        for line in process.stdout:
            # Write to console
            sys.stdout.write(line)
            sys.stdout.flush()
            
            # Write to log file
            log.write(line)
            log.flush()
    
    process.wait()
    print("-" * 60)
    print(f"Evaluation complete. Exit code: {process.returncode}")


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, help="Limit number of tasks")
    args = parser.parse_args()
    
    run_evaluation(args.limit)
