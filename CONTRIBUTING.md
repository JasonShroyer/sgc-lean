# Contributing to SGC

This repository acts as a **formal specification and falsification instrument** for the 
Spectral Geometry of Consolidation. We distinguish between:

- **Foundational Core** (verified algebraic theorems in `Lumpability.lean`)
- **Effective Theory** (bound specifications in `Approximate.lean` reliant on standard analysis axioms)

This structure allows us to rigorize the high-level architecture while isolating 
low-level analytic assumptions.

## Core Principle

> **Every major claim in the paper must cite a formal definition or theorem in `/src`.**
> 
> **We report exactly what the proof assistant verified—and what it rejected.**

## Directory Structure

```
/src          - Lean 4 source files (READONLY - do not modify without authorization)
/paper        - LaTeX source for the living paper
/scripts      - Automation scripts (consistency checks, safeguards)
/corpus       - Supplementary materials and LLM context
```

## The Ironclad Rule

The proofs in `/src` are **sorry-free** and must remain that way. We enforce this via:

1. **Pre-push hook**: Run `python scripts/install_safeguards.py` to install a Git hook
   that runs `lake build` before every push. Failed builds block the push.

2. **No unauthorized edits**: Contributors must NOT modify any `.lean` file in `/src`
   without explicit "Refactor Authorization" from the maintainers.

## Linking Paper to Proofs

We use a **readonly linking system** to connect LaTeX claims to Lean proofs:

### 1. The `lean_map.json` file

Located at `paper/lean_map.json`, this JSON file maps LaTeX labels to Lean names:

```json
{
  "theorems": {
    "thm:info-geometry-equiv": {
      "lean_file": "SGC/Information/Equivalence.lean",
      "lean_name": "information_geometry_equivalence",
      "description": "For reversible systems, RespectsBlank ↔ IsInformationBlanketV"
    }
  }
}
```

### 2. LaTeX commands

In your LaTeX, use these commands to reference Lean files:

```latex
\leanlink{SGC/Information/Equivalence.lean}          % File link
\leanref{SGC/Information/Equivalence.lean}{Theorem}  % Custom text
```

### 3. Consistency checking

Run the consistency checker to find undocumented theorems:

```bash
python scripts/map_theorems.py
```

This reports which Lean theorems are NOT yet mentioned in the paper.

## Workflow

1. **Write proofs first** (or use existing sorry-free proofs)
2. **Add to `lean_map.json`** when you want to cite a theorem in the paper
3. **Reference in LaTeX** using `\leanlink{}` or `\leanref{}`
4. **Run consistency check** before submitting

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
