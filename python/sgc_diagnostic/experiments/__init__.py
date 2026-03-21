# experiments/__init__.py
"""
Pre-defined experiments for the SGC diagnostic engine.

Imports are lazy to avoid matplotlib compatibility issues.
"""

def run_synthetic_chain(output_dir="output/"):
    from .synthetic_chain import run_synthetic_chain as _run
    return _run(output_dir)

def run_grokking_experiment(output_dir="output/"):
    from .grokking import run_grokking_experiment as _run
    return _run(output_dir)

def run_celegans_experiment(output_dir="output/"):
    from .celegans import run_celegans_experiment as _run
    return _run(output_dir)

__all__ = [
    "run_synthetic_chain",
    "run_grokking_experiment", 
    "run_celegans_experiment",
]
