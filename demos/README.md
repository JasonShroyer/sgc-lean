# UPAT-Scope: The Reality X-Ray

**A mathematical microscope that highlights 'Structural Stress' in data.**

When the red light flashes, the physics is breaking.

## Overview

This demo implements the concepts formally verified in the [SGC Lean4 library](../src/SGC/):

| Python Component | Lean4 Reference |
|-----------------|-----------------|
| `HilbertMapper` | Stage 2: Hilbert ordering |
| `DiffusionWavelets` | `SGC.Measurement.Wavelets` |
| `FrameAuditor` | `SGC.Measurement.Interfaces.TightnessAudit` |
| `StressDetector` | `SGC.Thermodynamics.Evolution.CanEvolve` |
| `UPATScope` | `SGC.Evolution.Dynamics.EvolutionStep` |

## Quick Start

```bash
# Install dependencies
pip install -r requirements.txt

# Run demo with test pattern
python upat_scope.py --demo

# Scan an image
python upat_scope.py path/to/image.png --output results/

# Generate JSON audit log
python upat_scope.py image.png --json audit.json
```

## The Pipeline

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   Input     │───▶│   Hilbert   │───▶│  Diffusion  │
│   Image     │    │   Mapping   │    │  Wavelets   │
└─────────────┘    └─────────────┘    └─────────────┘
                                            │
                                            ▼
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   Surgery   │◀───│   Stress    │◀───│   Frame     │
│   Decision  │    │  Detection  │    │   Audit     │
└─────────────┘    └─────────────┘    └─────────────┘
```

## The Math (Formally Verified)

### Frame Tightness Audit

A frame `{ψ_j}` satisfies:
```
A ‖f‖² ≤ Σ_j |⟨f, ψ_j⟩|² ≤ B ‖f‖²
```

The **tightness ratio** τ = B/A - 1 bounds representation error.

**Lean theorem:** `SGC.Measurement.Interfaces.tightness_ratio_nonneg`

### Evolution Inequality (First Law of Topology)

Surgery is permitted when:
```
|Stress| > Information_Cost / Bond_Strength
```

This is Landauer's principle applied to topology change.

**Lean theorem:** `SGC.Thermodynamics.Evolution.SatisfiesEvolutionInequality`

### Diffusion Wavelets

For non-normal generators L:
```
Ψ_j(L) = exp(t_j L) - exp(t_{j-1} L)
```

These avoid eigendecomposition pitfalls for irreversible systems.

**Lean theorem:** `SGC.Measurement.Wavelets.DiffusionWavelet`

## Output Example

```
═══════════════════════════════════════════════════════════════════════
  UPAT-SCOPE AUDIT LOG
  Structural Stability Analysis
═══════════════════════════════════════════════════════════════════════
  Timestamp: 2026-01-11T14:15:00
  Input: 256x256 → Hilbert Order 8
  Scales: 5
──────────────────────────────────────────────────────────────────────

  [FRAME TIGHTNESS AUDITS]
  Scale 0: τ = 0.0234 (A=0.891, B=0.912) [✓ PASS]
  Scale 1: τ = 0.0456 (A=0.823, B=0.861) [✓ PASS]
  Scale 2: τ = 0.0892 (A=0.756, B=0.823) [✓ PASS]
  Scale 3: τ = 0.1245 (A=0.689, B=0.775) [✗ FAIL]
  Scale 4: τ = 0.2103 (A=0.612, B=0.741) [✗ FAIL]

  [STRESS DETECTION]
  Region 1: idx [1024:1280] peak=0.892 → SURGERY PERMITTED
  Region 2: idx [3840:4096] peak=0.756 → SURGERY PERMITTED

  [SUMMARY]
  Overall Stability: 78.50%
  Surgery Status: TRIGGERED

  [LEAN4 VERIFICATION]
  Verified: True
    • SGC.Measurement.Interfaces.TightnessRatio
    • SGC.Measurement.Wavelets.DiffusionWavelet
    • SGC.Thermodynamics.Evolution.SatisfiesEvolutionInequality
    • SGC.Evolution.Dynamics.EvolutionStep
    • SGC.Evolution.Dynamics.SurgeryStep
═══════════════════════════════════════════════════════════════════════
```

## Visualization

The scanner produces a 6-panel visualization:

1. **Input Image** - Original grayscale image
2. **Hilbert Curve** - The space-filling curve mapping
3. **1D Signal** - Hilbert-ordered signal with stress regions highlighted
4. **Wavelet Coefficients** - Heatmap of |W_j| across scales
5. **Stress Map** - Overlay showing detected stress regions
6. **Audit Summary** - Frame bounds and surgery decision

## The "Harmonic Snap" Future Demo

Coming soon: Sonification of the Hilbert stream where:
- **Blue zones** sound like harmonies (stable)
- **Red zones** sound like distortion (unstable)
- **Surgery** produces a satisfying "click"

## License

Apache 2.0 (same as SGC library)
