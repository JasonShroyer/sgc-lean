#!/usr/bin/env python3
"""
install_safeguards.py - Installs Git hooks to protect sorry-free Lean proofs.

This script installs a pre-push hook that:
1. Runs `lake build` to verify proofs compile
2. Checks for `sorry` statements in src/ (same pattern as CI)

If either check fails, the push is rejected.

Usage:
    python scripts/install_safeguards.py

The hook will be installed to .git/hooks/pre-push
"""

import os
import sys
import stat

# The pre-push hook script content
PRE_PUSH_HOOK = r'''#!/bin/sh
#
# SGC Pre-Push Hook
# Prevents pushing if Lean proofs fail to build OR contain sorries.
# Installed by: scripts/install_safeguards.py
#

cd "$(git rev-parse --show-toplevel)"

echo "[pre-push] Step 1/2: Running 'lake build' to verify proofs..."
echo ""

lake build 2>&1
BUILD_EXIT_CODE=$?

if [ $BUILD_EXIT_CODE -ne 0 ]; then
    echo ""
    echo "=========================================="
    echo "ERROR: Build failed. Push rejected."
    echo ""
    echo "The Lean build did not complete successfully."
    echo "Please fix all errors before pushing."
    echo "=========================================="
    exit 1
fi

echo "[pre-push] ✓ Build passed."
echo ""
echo "[pre-push] Step 2/2: Checking for sorry statements..."

# Same grep pattern as CI workflow - excludes comments, docstrings, backticked references
SORRY_COUNT=$(grep -rn --include="*.lean" -E '\bsorry\b' src/ 2>/dev/null \
  | grep -v '^\s*--' \
  | grep -v '/--' \
  | grep -v '`sorry`' \
  | grep -v 'sorry-free' \
  | grep -v 'zero.*sorry' \
  | grep -v 'unproven' \
  | wc -l || echo "0")

# Trim whitespace (portable)
SORRY_COUNT=$(echo "$SORRY_COUNT" | tr -d '[:space:]')

if [ "$SORRY_COUNT" -gt 0 ]; then
    echo ""
    echo "=========================================="
    echo "ERROR: Found $SORRY_COUNT potential 'sorry' occurrence(s):"
    echo ""
    grep -rn --include="*.lean" -E '\bsorry\b' src/ 2>/dev/null \
      | grep -v '^\s*--' \
      | grep -v '/--' \
      | grep -v '`sorry`' \
      | grep -v 'sorry-free' \
      | grep -v 'zero.*sorry' \
      | grep -v 'unproven' || true
    echo ""
    echo "Push rejected. Please remove all sorry statements."
    echo "=========================================="
    exit 1
fi

echo "[pre-push] ✓ No sorries found."
echo ""
echo "[pre-push] ✓ All checks passed. Push authorized."
echo ""

exit 0
'''


def find_git_root():
    """Find the root of the git repository."""
    current = os.path.dirname(os.path.abspath(__file__))
    while current != os.path.dirname(current):
        if os.path.isdir(os.path.join(current, '.git')):
            return current
        current = os.path.dirname(current)
    return None


def install_hook():
    """Install the pre-push hook."""
    git_root = find_git_root()
    if not git_root:
        print("ERROR: Could not find git repository root.")
        sys.exit(1)
    
    hooks_dir = os.path.join(git_root, '.git', 'hooks')
    hook_path = os.path.join(hooks_dir, 'pre-push')
    
    # Create hooks directory if it doesn't exist
    os.makedirs(hooks_dir, exist_ok=True)
    
    # Check if hook already exists
    if os.path.exists(hook_path):
        print(f"WARNING: pre-push hook already exists at {hook_path}")
        response = input("Overwrite? (y/N): ").strip().lower()
        if response != 'y':
            print("Aborted. No changes made.")
            sys.exit(0)
    
    # Write the hook
    with open(hook_path, 'w', newline='\n') as f:
        f.write(PRE_PUSH_HOOK)
    
    # Make it executable (Unix-like systems)
    try:
        st = os.stat(hook_path)
        os.chmod(hook_path, st.st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)
    except Exception:
        pass  # Windows doesn't need this
    
    print("Pre-push hook installed successfully.")
    print("")
    print("  Location: .git/hooks/pre-push")
    print("")
    print("  What this does:")
    print("  • Runs 'lake build' before every push")
    print("  • Checks for 'sorry' statements in src/")
    print("  • Rejects pushes if build fails OR sorries are found")
    print("")
    print("Your proofs are now protected from accidental breakage.")


if __name__ == '__main__':
    install_hook()
