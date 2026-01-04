# Contributing to SGC

This repository, constructed in the style of a **verified physics paper**, acts as a 
formal specification and falsification instrument for the Spectral Geometry of Consolidation.

We distinguish between:

- **Foundational Core** (verified algebraic theorems in `Lumpability.lean`)
- **Effective Theory** (bound specifications in `Approximate.lean` supported by standard analysis axioms)

This two-tier structure allows us to rigorize the high-level architecture while explicitly 
isolating analytic assumptions. See [`ARCHITECTURE.md`](ARCHITECTURE.md) for detailed rationale.

## Technical Scope & Design Conventions

To bridge the gap between thermodynamic intuition and formal verification, the library adopts specific architectural constraints:

### 1. Finite-Dimensional Linear Algebra
We utilize explicit weighted inner products on finite graphs ($L^2(\pi)$) rather than general measure-theoretic structures. This formulation grants direct access to matrix spectral bounds (e.g., Perron-Frobenius gaps) which are strictly required to derive the **Validity Horizon** ($T \sim 1/\epsilon$) results.

### 2. Thermodynamic Type Safety
We enforce strict typing to distinguish between **Observables** ($f \in \mathbb{R}^V$) and **Densities** ($\mu \in \mathcal{D}(V)$). This enforces the physical duality between "Work" and "Heat" terms, preventing category errors in the formulation of the Stochastic First Law (Doob-Meyer decomposition).

## Core Principle

> **We report exactly what the proof assistant verified—and what it rejected.**

The goal is readable proofs for physicists, checkable by machines.

## Directory Structure

```
/src          - Verified Core (Stable - please discuss major refactors in an Issue first)
/scripts      - Automation scripts (consistency checks, safeguards)
```

## Build & Test

To verify the library:

```bash
lake build
```

This compiles all Lean files and checks that all proofs are complete (zero unproven goals).

## Recommended Tools

Before starting a proof, check if the result exists in Mathlib:

* **Loogle:** [loogle.lean-lang.org](https://loogle.lean-lang.org/) — Semantic search for Lean theorems.
* **Moogle:** [moogle.ai](https://www.moogle.ai/) — AI-powered search for Mathlib.

## The Ironclad Rule

The proofs in `/src` are **sorry-free** and must remain that way. We enforce this via:

1. **CI Pipeline**: GitHub Actions runs `lake build` on every push and verifies no 
   active `sorry` statements exist in the source.

2. **Pre-push hook** (optional): Run `python scripts/install_safeguards.py` to install 
   a local Git hook that runs `lake build` before every push.

3. **Stability First**: Modifications to the verified core must maintain proof integrity.
   Please discuss significant changes in an issue before opening a Pull Request.

## Installing Safeguards

```bash
python scripts/install_safeguards.py
```

This installs the pre-push hook. After installation, any attempt to push code
that breaks the Lean build will be rejected with:

```
ABORT: PROOF BREAKAGE DETECTED
```

## Inputting Mathematical Symbols

New to Lean? You can type mathematical symbols using LaTeX-style abbreviations followed by `TAB` or `SPACE`.

| Input | Symbol |
|-------|--------|
| `\R` | `ℝ` |
| `\pi` | `π` |
| `\all` | `∀` |
| `\sum` | `∑` |
| `\to` | `→` |
| `\le` | `≤` |

See the [Lean 4 VSCode extension](https://github.com/leanprover/vscode-lean4) for the full abbreviation list.

## Questions?

Open an issue or contact the maintainers.
