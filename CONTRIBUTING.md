# Contributing to UPAT

This repository uses a **Living Paper** workflow where the LaTeX paper in `/paper` 
is co-located with formally verified Lean 4 proofs in `/src`.

## Core Principle

> **Every major claim in the paper must cite a formal definition or theorem in `/src`.**

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
      "lean_file": "UPAT/Information/Equivalence.lean",
      "lean_name": "information_geometry_equivalence",
      "description": "For reversible systems, RespectsBlank ↔ IsInformationBlanketV"
    }
  }
}
```

### 2. LaTeX commands

In your LaTeX, use these commands to reference Lean files:

```latex
\leanlink{UPAT/Information/Equivalence.lean}          % File link
\leanref{UPAT/Information/Equivalence.lean}{Theorem}  % Custom text
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
