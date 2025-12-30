#!/usr/bin/env python3
"""
install_safeguards.py - Installs Git hooks to protect sorry-free Lean proofs.

This script installs a pre-push hook that runs `lake build` before any push.
If the build fails, the push is rejected to prevent proof breakage.

Usage:
    python paper/scripts/install_safeguards.py

The hook will be installed to .git/hooks/pre-push
"""

import os
import sys
import stat

# The pre-push hook script content
PRE_PUSH_HOOK = r'''#!/bin/sh
#
# IRONCLAD PRE-PUSH HOOK
# Prevents pushing if Lean proofs fail to build.
# Installed by: scripts/install_safeguards.py
#

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  IRONCLAD SAFEGUARD: Running 'lake build' before push...    ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

# Run lake build from the repository root
cd "$(git rev-parse --show-toplevel)"

lake build 2>&1
BUILD_EXIT_CODE=$?

if [ $BUILD_EXIT_CODE -ne 0 ]; then
    echo ""
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║  ██████╗ ██████╗  ██████╗  ██████╗ ███████╗    ██████╗      ║"
    echo "║  ██╔══██╗██╔══██╗██╔═══██╗██╔═══██╗██╔════╝    ██╔══██╗     ║"
    echo "║  ██████╔╝██████╔╝██║   ██║██║   ██║█████╗      ██║  ██║     ║"
    echo "║  ██╔═══╝ ██╔══██╗██║   ██║██║   ██║██╔══╝      ██║  ██║     ║"
    echo "║  ██║     ██║  ██║╚██████╔╝╚██████╔╝██║         ██████╔╝     ║"
    echo "║  ╚═╝     ╚═╝  ╚═╝ ╚═════╝  ╚═════╝ ╚═╝         ╚═════╝      ║"
    echo "╠══════════════════════════════════════════════════════════════╣"
    echo "║                                                              ║"
    echo "║   ABORT: PROOF BREAKAGE DETECTED                            ║"
    echo "║                                                              ║"
    echo "║   The Lean build failed. Push has been REJECTED.            ║"
    echo "║   Fix all errors before pushing.                            ║"
    echo "║                                                              ║"
    echo "╚══════════════════════════════════════════════════════════════╝"
    exit 1
fi

echo ""
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  ✓ BUILD PASSED - Push authorized                           ║"
echo "╚══════════════════════════════════════════════════════════════╝"
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
    
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  IRONCLAD SAFEGUARD INSTALLED                               ║")
    print("╠══════════════════════════════════════════════════════════════╣")
    print(f"║  Hook location: .git/hooks/pre-push                         ║")
    print("║                                                              ║")
    print("║  Protection enabled:                                        ║")
    print("║  • Every push will run 'lake build' first                   ║")
    print("║  • Failed builds will BLOCK the push                        ║")
    print("║  • Your sorry-free proofs are now protected                 ║")
    print("╚══════════════════════════════════════════════════════════════╝")


if __name__ == '__main__':
    install_hook()
