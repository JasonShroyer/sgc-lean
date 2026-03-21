# __init__.py
"""
SGC Emergence Diagnostic Engine

A scientific instrument grounded in machine-verified mathematics that takes any 
dynamical system (V, L, π) and returns its complete emergence profile, with every 
number traced to a proved theorem or honestly labeled as a conjecture.

Usage:
    from sgc_diagnostic import SGCDiagnostic, SGCProfile, run_experiment
    
    # From raw generator
    diag = SGCDiagnostic(L, pi, system_name="my_system")
    profile = diag.compute_profile()
    
    # From connectivity matrix
    from sgc_diagnostic.markov import generator_from_connectivity
    L, pi = generator_from_connectivity(W)
    diag = SGCDiagnostic(L, pi, system_name="connectivity")
    profile = diag.compute_profile()
    
    # Generate report
    from sgc_diagnostic.report import generate_report
    generate_report(profile, output_dir="output/")
"""

from .core import SGCProfile, SGCDiagnostic
from .certificates import TheoremCitation, Prediction, CITATIONS, get_citation
from .partition import (
    find_optimal_partition,
    compute_projector,
    compute_defect_operator,
    defect_norm_pi,
    compute_coarse_generator
)
from .spectral import (
    compute_spectral_gap,
    compute_timescales,
    count_timescale_gaps,
    compute_dirichlet_form,
    decompose_dirichlet,
    compute_schur_correction,
    rayleigh_quotient
)
from .tsallis import (
    estimate_tsallis_q,
    compute_tsallis_entropy,
    compute_escort_distribution,
    compute_tsallis_divergence
)
from .markov import (
    generator_from_transition_matrix,
    generator_from_counts,
    generator_from_activations,
    generator_from_connectivity,
    compute_stationary_distribution,
    validate_generator,
    check_detailed_balance
)
from .report import generate_report


def run_experiment(name: str, output_dir: str = "output/"):
    """
    Run a pre-defined experiment by name.
    
    Args:
        name: One of "synthetic", "grokking", "celegans", or "all"
        output_dir: Directory for output files
        
    Returns:
        dict mapping experiment names to SGCProfile objects
    """
    results = {}
    
    if name in ("synthetic", "all"):
        from .experiments.synthetic_chain import run_synthetic_chain
        results["synthetic"] = run_synthetic_chain(output_dir)
    
    if name in ("grokking", "all"):
        from .experiments.grokking import run_grokking_experiment
        results["grokking"] = run_grokking_experiment(output_dir)
    
    if name in ("celegans", "all"):
        from .experiments.celegans import run_celegans_experiment
        results["celegans"] = run_celegans_experiment(output_dir)
    
    if not results:
        raise ValueError(f"Unknown experiment: {name}. Use 'synthetic', 'grokking', 'celegans', or 'all'.")
    
    return results


__all__ = [
    # Core classes
    "SGCProfile",
    "SGCDiagnostic",
    
    # Certificates
    "TheoremCitation",
    "Prediction", 
    "CITATIONS",
    "get_citation",
    
    # Partition
    "find_optimal_partition",
    "compute_projector",
    "compute_defect_operator",
    "defect_norm_pi",
    "compute_coarse_generator",
    
    # Spectral
    "compute_spectral_gap",
    "compute_timescales",
    "count_timescale_gaps",
    "compute_dirichlet_form",
    "decompose_dirichlet",
    "compute_schur_correction",
    "rayleigh_quotient",
    
    # Tsallis
    "estimate_tsallis_q",
    "compute_tsallis_entropy",
    "compute_escort_distribution",
    "compute_tsallis_divergence",
    
    # Markov
    "generator_from_transition_matrix",
    "generator_from_counts",
    "generator_from_activations",
    "generator_from_connectivity",
    "compute_stationary_distribution",
    "validate_generator",
    "check_detailed_balance",
    
    # Report
    "generate_report",
    
    # Experiments
    "run_experiment",
]

__version__ = "0.1.0"
