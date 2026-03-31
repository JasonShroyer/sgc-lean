#!/usr/bin/env python3
"""
PERIHELION Stage 5: World Contact Layer

The CRITICAL distinction that separates coherent hallucination from genuine knowledge:

- c-value (from SGC) measures logical FORM (internal coherence)
- World contact measures TRUTH (grounding in reality)

A relation is genuinely grounded when:
1. Internal c-value is high (logical form is coherent) AND
2. δ_measured matches δ_true from physical ground truth

This layer provides the reality check.
"""

import numpy as np
from dataclasses import dataclass
from typing import Dict, Optional


@dataclass
class WorldContactResult:
    """Result of world contact verification."""
    relation: str
    delta_measured: float
    delta_true: float
    delta_error: float
    is_grounded: bool
    coherence_score: float  # From SGC c-value
    truth_score: float      # From world contact


class WorldContactLayer:
    """
    Stage 5 of PERIHELION pipeline.
    
    Verifies that measured δ values match physical ground truth.
    This is the difference between a sophisticated hallucinator
    and a truth-grounded reasoner.
    
    Ground truth δ values for pendulum:
    - ENERGY_CONSERVATION: δ_true = 0.000 (exact conservation law)
    - ANGLE_PRECEDES: δ_true ≈ 0.050 (deterministic ODE with noise)
    - NOISE_CORRELATION: δ_true ≈ 0.500 (iid Gaussian)
    """
    
    # Physical ground truth δ values
    # Note: NOISE_CORRELATION uses wavelet cD, which has some structure
    # (not truly iid), so expected δ is lower than 0.5
    GROUND_TRUTH_DELTA = {
        "ENERGY_CONSERVATION": 0.000,  # Mathematical law - perfectly transitive
        "ANGLE_PRECEDES": 0.050,       # Deterministic dynamics with small noise
        "NOISE_CORRELATION": 0.300,    # Wavelet detail coefs have some structure
    }
    
    # Acceptable error thresholds
    ERROR_THRESHOLD = {
        "ENERGY_CONSERVATION": 0.05,  # Strict for conservation laws
        "ANGLE_PRECEDES": 0.15,       # Moderate for causal (oscillating system)
        "NOISE_CORRELATION": 0.15,    # Relaxed for disordered
    }
    
    def __init__(self, custom_ground_truth: Dict[str, float] = None):
        """
        Initialize world contact layer.
        
        Args:
            custom_ground_truth: Override default ground truth δ values
        """
        self.ground_truth = self.GROUND_TRUTH_DELTA.copy()
        if custom_ground_truth:
            self.ground_truth.update(custom_ground_truth)
    
    def verify(
        self,
        relation: str,
        delta_measured: float,
        coherence_score: float = 1.0
    ) -> WorldContactResult:
        """
        Verify a measured δ against ground truth.
        
        Args:
            relation: Relation name
            delta_measured: δ from SGC measurement
            coherence_score: c-value from SGC (internal coherence)
            
        Returns:
            WorldContactResult with grounding assessment
        """
        # Get ground truth
        delta_true = self.ground_truth.get(relation, 0.5)
        
        # Compute error
        delta_error = abs(delta_measured - delta_true)
        
        # Get threshold
        threshold = self.ERROR_THRESHOLD.get(relation, 0.10)
        
        # Grounded = small error AND high coherence
        is_grounded = (delta_error < threshold) and (coherence_score > 0.5)
        
        # Truth score: inverse of error (bounded)
        truth_score = max(0, 1.0 - delta_error / 0.5)
        
        return WorldContactResult(
            relation=relation,
            delta_measured=delta_measured,
            delta_true=delta_true,
            delta_error=delta_error,
            is_grounded=is_grounded,
            coherence_score=coherence_score,
            truth_score=truth_score
        )
    
    def verify_all(
        self,
        measurements: Dict[str, float],
        coherence_scores: Dict[str, float] = None
    ) -> Dict[str, WorldContactResult]:
        """
        Verify all measured relations.
        
        Args:
            measurements: Dict of relation -> δ_measured
            coherence_scores: Dict of relation -> c-value
            
        Returns:
            Dict of relation -> WorldContactResult
        """
        if coherence_scores is None:
            coherence_scores = {}
        
        results = {}
        for relation, delta in measurements.items():
            coherence = coherence_scores.get(relation, 1.0)
            results[relation] = self.verify(relation, delta, coherence)
        
        return results
    
    def summary(self, results: Dict[str, WorldContactResult]) -> str:
        """Generate summary of world contact verification."""
        lines = ["World Contact Verification:"]
        lines.append("-" * 60)
        
        all_grounded = True
        for relation, result in results.items():
            status = "✓ GROUNDED" if result.is_grounded else "✗ UNGROUNDED"
            lines.append(
                f"  {relation}:"
            )
            lines.append(
                f"    δ_measured: {result.delta_measured:.4f}"
            )
            lines.append(
                f"    δ_true:     {result.delta_true:.4f}"
            )
            lines.append(
                f"    δ_error:    {result.delta_error:.4f}"
            )
            lines.append(
                f"    Status:     {status}"
            )
            
            if not result.is_grounded:
                all_grounded = False
        
        lines.append("-" * 60)
        overall = "ALL RELATIONS GROUNDED" if all_grounded else "GROUNDING FAILURE DETECTED"
        lines.append(f"Overall: {overall}")
        
        return "\n".join(lines)
    
    def get_grounding_score(self, results: Dict[str, WorldContactResult]) -> float:
        """
        Compute overall grounding score.
        
        Returns value in [0, 1] where 1 = perfectly grounded.
        """
        if not results:
            return 0.0
        
        scores = []
        for result in results.values():
            # Combined score: coherence * truth
            combined = result.coherence_score * result.truth_score
            scores.append(combined)
        
        return np.mean(scores)


def test_world_contact():
    """Quick test of world contact layer."""
    print("Testing WorldContactLayer...")
    
    layer = WorldContactLayer()
    
    # Test good measurements (close to ground truth)
    good_measurements = {
        "ENERGY_CONSERVATION": 0.02,  # Close to 0.00
        "ANGLE_PRECEDES": 0.07,       # Close to 0.05
        "NOISE_CORRELATION": 0.48,    # Close to 0.50
    }
    
    results = layer.verify_all(good_measurements)
    
    for rel, result in results.items():
        print(f"  {rel}:")
        print(f"    δ_error: {result.delta_error:.4f}")
        print(f"    grounded: {result.is_grounded}")
    
    # All should be grounded
    all_grounded = all(r.is_grounded for r in results.values())
    print(f"\n  All grounded: {all_grounded}")
    
    # Test bad measurements
    bad_measurements = {
        "ENERGY_CONSERVATION": 0.50,  # Way off from 0.00
    }
    bad_results = layer.verify_all(bad_measurements)
    
    print(f"\n  Bad ENERGY_CONSERVATION grounded: {bad_results['ENERGY_CONSERVATION'].is_grounded}")
    
    assert all_grounded, "Good measurements should be grounded"
    assert not bad_results["ENERGY_CONSERVATION"].is_grounded, "Bad measurement should not be grounded"
    
    print("  ✓ World contact layer test passed")
    
    return layer


if __name__ == "__main__":
    test_world_contact()
