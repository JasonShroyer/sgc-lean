# SGC Multiscale Stability Analyzer

Python implementation of the frame tightness diagnostics and singularity detection
algorithms formally verified in the SGC Lean4 library.

## Overview

This analyzer implements Hilbert-ordered diffusion wavelet decomposition with
auditable frame bounds, corresponding to the following Lean4 modules:

| Python Component | Lean4 Reference |
|-----------------|-----------------|
| `HilbertMapper` | Locality-preserving 2D→1D mapping |
| `DiffusionWavelets` | `SGC.Measurement.Wavelets` |
| `FrameAuditor` | `SGC.Measurement.Interfaces.TightnessAudit` |
| `StressDetector` | `SGC.Thermodynamics.Evolution.CanEvolve` |
| `SGCAnalyzer` | `SGC.Evolution.Dynamics.EvolutionStep` |

## Quick Start

```bash
# Install dependencies
pip install -r requirements.txt

# Run demo with test pattern
python sgc_analyzer.py --demo

# Analyze an image
python sgc_analyzer.py path/to/image.png --output results/

# Generate JSON diagnostic log
python sgc_analyzer.py image.png --json diagnostic.json
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
======================================================================
  SGC STABILITY DIAGNOSTIC
  Multiscale Frame Analysis
======================================================================
  Timestamp: 2026-01-11T14:15:00
  Input: 256x256 -> Hilbert Order 8
  Scales: 5
----------------------------------------------------------------------

  [FRAME TIGHTNESS AUDITS]
  Scale 0: tau = 0.0234 (A=0.891, B=0.912) [PASS]
  Scale 1: tau = 0.0456 (A=0.823, B=0.861) [PASS]
  Scale 2: tau = 0.0892 (A=0.756, B=0.823) [PASS]
  Scale 3: tau = 0.1245 (A=0.689, B=0.775) [FAIL]
  Scale 4: tau = 0.2103 (A=0.612, B=0.741) [FAIL]

  [SINGULARITY DETECTION]
  Region 1: idx [1024:1280] peak=0.892 -> THRESHOLD EXCEEDED
  Region 2: idx [3840:4096] peak=0.756 -> THRESHOLD EXCEEDED

  [SUMMARY]
  Overall Stability: 78.50%
  Surgery Criterion: SATISFIED

  [LEAN4 VERIFICATION]
  Verified: True
    - SGC.Measurement.Interfaces.TightnessRatio
    - SGC.Measurement.Wavelets.DiffusionWavelet
    - SGC.Thermodynamics.Evolution.SatisfiesEvolutionInequality
    - SGC.Evolution.Dynamics.EvolutionStep
======================================================================
```

## Visualization

The analyzer produces a 6-panel visualization:

1. **Input Image** - Original grayscale image
2. **Hilbert Curve** - Space-filling curve mapping overlay
3. **1D Signal** - Hilbert-ordered signal with detected singularities
4. **Wavelet Coefficients** - Heatmap of |W_j| across scales
5. **Stress Map** - Detected singularities overlaid on image
6. **Diagnostic Summary** - Frame bounds and threshold status

## License

Apache 2.0 (same as SGC library)
