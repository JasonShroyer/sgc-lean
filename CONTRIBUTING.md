# Contributing to SGC

This repository acts as a **formal specification and falsification instrument** for the 
Spectral Geometry of Consolidation. We distinguish between:

- **Foundational Core** (verified algebraic theorems in `Lumpability.lean`)
- **Effective Theory** (bound specifications in `Approximate.lean` reliant on standard analysis axioms)

This structure allows us to rigorize the high-level architecture while isolating 
low-level analytic assumptions.

## Core Principle

> **We report exactly what the proof assistant verified—and what it rejected.**

## Directory Structure

```
/src          - Lean 4 source files (READONLY - do not modify without authorization)
/scripts      - Automation scripts (consistency checks, safeguards)
```

## Build & Test

To verify the library:

```bash
lake build
```

This compiles all Lean files and checks that all proofs are complete (zero unproven goals).

## The Ironclad Rule

The proofs in `/src` are **sorry-free** and must remain that way. We enforce this via:

1. **CI Pipeline**: GitHub Actions runs `lake build` on every push and verifies no 
   active `sorry` statements exist in the source.

2. **Pre-push hook** (optional): Run `python scripts/install_safeguards.py` to install 
   a local Git hook that runs `lake build` before every push.

3. **No unauthorized edits**: Contributors must NOT modify any `.lean` file in `/src`
   without explicit "Refactor Authorization" from the maintainers.

## Installing Safeguards

```bash
python scripts/install_safeguards.py
```

This installs the pre-push hook. After installation, any attempt to push code
that breaks the Lean build will be rejected with:

```
ABORT: PROOF BREAKAGE DETECTED
```

## Questions?

Open an issue or contact the maintainers.
