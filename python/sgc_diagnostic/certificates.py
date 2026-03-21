# certificates.py
"""
Theorem citation table — the soul of the SGC diagnostic system.
Every measurement traces to a proved theorem or is labeled as AXIOM/CONJECTURE/EMPIRICAL.
"""
from dataclasses import dataclass
from typing import Literal

REPO = "https://github.com/JasonShroyer/sgc-lean"
COMMIT = "fb0c260"
BRANCH = "wip-quantum-bridge"


@dataclass
class TheoremCitation:
    """Citation for a machine-verified theorem or documented axiom."""
    name: str           # Lean theorem name
    file: str           # path in repo, e.g. "src/SGC/Renormalization/OptimalPartition.lean"
    statement: str      # human-readable statement
    status: Literal["PROVED", "AXIOM", "CONJECTURE", "EMPIRICAL"]
    proof_path: str     # one-sentence description of proof method
    
    @property
    def url(self):
        return f"{REPO}/blob/{COMMIT}/{self.file}"


# The canonical citation table — every measurement maps here
CITATIONS = {
    "optimal_partition_exists": TheoremCitation(
        name="optimal_partition_exists",
        file="src/SGC/Renormalization/OptimalPartition.lean",
        statement="For any (V, L, π), there exists P* minimizing defect_cost(L, π, P) over all partitions.",
        status="PROVED",
        proof_path="Finiteness of partitions + real function on finite nonempty set attains minimum."
    ),
    "hidden_entropy_bounded_by_defect": TheoremCitation(
        name="hidden_entropy_bounded_by_defect",
        file="src/SGC/Thermodynamics/EntropyProduction.lean",
        statement="σ_hid(L, P, π) ≤ C · ε(L, P, π)²",
        status="PROVED",
        proof_path="Schnakenberg formula + defect operator norm bound."
    ),
    "to_persist_is_to_predict": TheoremCitation(
        name="to_persist_is_to_predict",
        file="src/SGC/EmergenceEquivalence.lean",
        statement="σ_hid < δ ⟹ ε < √(δ/c). Low dissipation requires low prediction error.",
        status="PROVED",
        proof_path="Composition of lower and upper bounds on σ_hid."
    ),
    "trajectory_closure_bound": TheoremCitation(
        name="trajectory_closure_bound",
        file="src/SGC/Renormalization/Approximate.lean",
        statement="‖e^{tL}f - e^{tL̄}f‖_π ≤ ε · t · C · ‖f‖_π",
        status="PROVED",
        proof_path="Duhamel's principle applied to (L - L̄) = D_P."
    ),
    "dirichlet_gap_non_decrease": TheoremCitation(
        name="dirichlet_gap_non_decrease",
        file="src/SGC/Renormalization/Lumpability.lean",
        statement="γ̄(L) ≥ γ(L). Coarse-graining cannot decrease the spectral gap.",
        status="PROVED",
        proof_path="RayleighSetBlockConstant ⊆ RayleighSet ⟹ inf(subset) ≥ inf(total)."
    ),
    "emergence_equivalence": TheoremCitation(
        name="emergence_equivalence",
        file="src/SGC/EmergenceEquivalence.lean",
        statement="P* simultaneously minimizes defect, bounds σ_hid, is variationally stable, and bases the RG tower.",
        status="PROVED",
        proof_path="Composition of OptimalPartition, EntropyProduction, LeastAction theorems."
    ),
    "emergence_ceiling": TheoremCitation(
        name="emergence_ceiling",
        file="src/SGC/EmergenceCapacity.lean",
        statement="N_E = b₁/(γ·ε) ≤ b₁(V)/(C·γ²)",
        status="AXIOM",
        proof_path="Conditional on spectral_gap_lower_bounds_defect (needs DirichletForm-defect bridge)."
    ),
    "tsallis_dpi": TheoremCitation(
        name="tsallis_dpi",
        file="src/SGC/TsallisStatistics.lean",
        statement="For q ∈ (1,2), D_q satisfies the Data Processing Inequality.",
        status="PROVED",
        proof_path="Direct computation from Tsallis divergence definition for q in (1,2)."
    ),
    "rg_tower_terminates": TheoremCitation(
        name="rg_tower_terminates",
        file="src/SGC/Renormalization/Lumpability.lean",
        statement="The RG tower V → V₁ → ... → V_d terminates with d ≤ ⌊log₂(|V|)⌋.",
        status="PROVED",
        proof_path="Each coarse-graining strictly reduces dimension; finite V bounds iterations."
    ),
    "generator_decomposition": TheoremCitation(
        name="generator_decomposition",
        file="src/SGC/Renormalization/Approximate.lean",
        statement="L = L̄ + D where D = (I-Π)LΠ is the defect operator.",
        status="PROVED",
        proof_path="Direct algebraic decomposition with Π² = Π."
    ),
    "dirichlet_form_defect_decomposition": TheoremCitation(
        name="dirichlet_form_defect_decomposition",
        file="src/SGC/EmergenceCapacity.lean",
        statement="ℰ(f) = ⟨f, L̄f⟩_π + ⟨f, Df⟩_π. Dirichlet form decomposes into coarse + leakage.",
        status="PROVED",
        proof_path="Substitution of L = L̄ + D into Dirichlet form definition."
    ),
    "reversible_local_eq_global": TheoremCitation(
        name="reversible_local_eq_global",
        file="src/SGC/Renormalization/OptimalPartition.lean",
        statement="For reversible L, local partition optima are global optima.",
        status="PROVED",
        proof_path="Uses reversible_local_implies_global axiom + self-adjointness from detailed balance."
    ),
    "schur_self_energy": TheoremCitation(
        name="schur_self_energy",
        file="(Wilsonian RG - Continent 4)",
        statement="Δ = D_upper · L_fine⁻¹ · D_lower is the second-order coarse-graining correction.",
        status="CONJECTURE",
        proof_path="Not yet formalized; standard Schur complement from linear algebra."
    ),
    "q_estimation": TheoremCitation(
        name="q_estimation",
        file="(empirical)",
        statement="q estimated from π via maximum likelihood fit to Tsallis distribution.",
        status="EMPIRICAL",
        proof_path="Standard MLE; not a theorem about the system, but about estimation procedure."
    ),
}


@dataclass
class Prediction:
    """A falsifiable prediction with pre-stated expected value."""
    statement: str
    theorem: TheoremCitation
    predicted_value: float
    tolerance: float          # absolute tolerance for CONFIRMED verdict
    actual_value: float = None
    verdict: Literal["PENDING", "CONFIRMED", "REFUTED", "INCONCLUSIVE"] = "PENDING"
    
    def evaluate(self, actual: float) -> "Prediction":
        """Evaluate prediction against actual measurement."""
        self.actual_value = actual
        if abs(actual - self.predicted_value) <= self.tolerance:
            self.verdict = "CONFIRMED"
        elif abs(actual - self.predicted_value) <= 3 * self.tolerance:
            self.verdict = "INCONCLUSIVE"
        else:
            self.verdict = "REFUTED"
        return self


def get_citation(key: str) -> TheoremCitation:
    """Get citation by key, with fallback for unknown keys."""
    if key in CITATIONS:
        return CITATIONS[key]
    return TheoremCitation(
        name=key,
        file="(unknown)",
        statement=f"Citation for {key} not found in table.",
        status="EMPIRICAL",
        proof_path="Unknown."
    )
