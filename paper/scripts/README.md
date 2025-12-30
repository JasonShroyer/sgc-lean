# Paper Scripts

This directory contains Python utilities for the **Living Paper** system — tools that bridge the formal Lean 4 proofs with the LaTeX manuscript.

## Scripts

### `compile_paper.py`
Compiles the LaTeX manuscript to PDF using pdflatex.

```bash
# From repository root:
python paper/scripts/compile_paper.py                    # Build only
python paper/scripts/compile_paper.py --publish          # Build + copy to Desktop
python paper/scripts/compile_paper.py --publish-to DIR   # Build + copy to custom dir
```

**Output:** `paper/build/main.pdf`

### `map_theorems.py`
Consistency checker that verifies Lean theorems are properly documented in the paper.

```bash
# From repository root:
python paper/scripts/map_theorems.py
```

**Reports:**
- Lean theorems NOT yet mentioned in the paper (need documentation)
- Paper references to non-existent Lean theorems (broken links)

### `install_safeguards.py`
Installs a Git pre-push hook that runs `lake build` before any push, preventing broken proofs from reaching the remote.

```bash
# From repository root:
python paper/scripts/install_safeguards.py
```

**Installs:** `.git/hooks/pre-push`

## Design: Dynamic Root Discovery

These scripts are **location-agnostic**. They use upward directory traversal to find the repository root by searching for `lakefile.lean` (or `.git/`). This means:

- ✅ Scripts work from any subdirectory
- ✅ Scripts survive directory reorganization
- ✅ No hardcoded relative paths to maintain

```python
def find_repo_root() -> Path:
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / 'lakefile.lean').exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find repository root")
```

## Dependencies

- **Python 3.8+**
- **pdflatex** (MiKTeX or TeX Live) — for `compile_paper.py`
- No external Python packages required (uses only stdlib)

## File Structure

```
paper/
├── scripts/           ← You are here
│   ├── README.md
│   ├── compile_paper.py
│   ├── map_theorems.py
│   └── install_safeguards.py
├── main.tex           ← LaTeX document root
├── lean_map.json      ← Theorem↔Lean mapping database
├── sections/          ← LaTeX section files
└── build/             ← Compiled output (gitignored)
```
