#!/usr/bin/env python3
"""
compile_paper.py - Compile the Living Paper to PDF using pdflatex.

Usage:
    python paper/scripts/compile_paper.py                    # Build only
    python paper/scripts/compile_paper.py --publish          # Build + copy to Desktop
    python paper/scripts/compile_paper.py --publish-to DIR   # Build + copy to custom dir

Output:
    paper/build/main.pdf
    (optionally) Desktop/UPAT_Draft_YYYYMMDD_HHMM.pdf
"""

import argparse
import os
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path


def find_repo_root() -> Path:
    """Find the repository root (where lakefile.lean lives)."""
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / 'lakefile.lean').exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find repository root")


def find_pdflatex():
    """Find pdflatex executable on the system."""
    import shutil
    
    # Check if in PATH
    pdflatex = shutil.which('pdflatex')
    if pdflatex:
        return pdflatex
    
    # Common Windows locations
    common_paths = [
        Path(os.environ.get('LOCALAPPDATA', '')) / 'Programs' / 'MiKTeX' / 'miktex' / 'bin' / 'x64' / 'pdflatex.exe',
        Path('C:/Program Files/MiKTeX/miktex/bin/x64/pdflatex.exe'),
        Path('C:/texlive/2024/bin/windows/pdflatex.exe'),
        Path('C:/texlive/2023/bin/windows/pdflatex.exe'),
    ]
    
    for path in common_paths:
        if path.exists():
            return str(path)
    
    return None


def compile_pdf():
    """Compile the paper using pdflatex."""
    repo_root = find_repo_root()
    paper_dir = repo_root / 'paper'
    build_dir = paper_dir / 'build'
    main_tex = paper_dir / 'main.tex'
    
    # Create build directory
    build_dir.mkdir(exist_ok=True)
    
    print("=" * 60)
    print("COMPILING LIVING PAPER")
    print("=" * 60)
    print(f"Source: {main_tex}")
    print(f"Output: {build_dir / 'main.pdf'}")
    print()
    
    # Find pdflatex
    pdflatex = find_pdflatex()
    if not pdflatex:
        print("ERROR: pdflatex not found!")
        print()
        print("Please install a LaTeX distribution:")
        print("  - MiKTeX: https://miktex.org/download")
        print("  - TeX Live: https://tug.org/texlive/")
        print()
        print("Or use Overleaf (online): https://www.overleaf.com/")
        print("  1. Create new project")
        print("  2. Upload paper/ folder contents")
        print("  3. Compile online")
        return None
    
    print(f"Using: {pdflatex}")
    print()
    
    # Run pdflatex
    cmd = [
        pdflatex,
        '-interaction=nonstopmode',
        f'-output-directory={build_dir}',
        str(main_tex)
    ]
    
    print("Running pdflatex (pass 1)...")
    result = subprocess.run(
        cmd,
        cwd=str(paper_dir),
        capture_output=True,
        text=True
    )
    
    # Check if PDF was created
    pdf_path = build_dir / 'main.pdf'
    log_path = build_dir / 'main.log'
    
    if pdf_path.exists():
        print()
        print("=" * 60)
        print("SUCCESS!")
        print("=" * 60)
        print(f"PDF created at: {pdf_path}")
        return pdf_path
    else:
        print()
        print("=" * 60)
        print("BUILD FAILED")
        print("=" * 60)
        print(f"Check log at: {log_path}")
        print()
        print("STDOUT:")
        print(result.stdout[-2000:] if len(result.stdout) > 2000 else result.stdout)
        print()
        print("STDERR:")
        print(result.stderr[-1000:] if len(result.stderr) > 1000 else result.stderr)
        return None


def publish_pdf(pdf_path: Path, destination_dir: Path = None) -> Path:
    """
    Publish the compiled PDF to a user-accessible location.
    
    Args:
        pdf_path: Path to the compiled PDF
        destination_dir: Target directory (defaults to Desktop)
    
    Returns:
        Path to the published PDF
    """
    if destination_dir is None:
        # Default to Desktop
        destination_dir = Path.home() / "Desktop"
    
    destination_dir = Path(destination_dir)
    
    # Create destination if it doesn't exist
    destination_dir.mkdir(parents=True, exist_ok=True)
    
    # Generate timestamped filename
    timestamp = datetime.now().strftime("%Y%m%d_%H%M")
    published_name = f"UPAT_Draft_{timestamp}.pdf"
    published_path = destination_dir / published_name
    
    print()
    print("-" * 60)
    print("PUBLISHING...")
    print("-" * 60)
    
    try:
        shutil.copy2(pdf_path, published_path)
        print(f"[OK] Published to: {published_path}")
        return published_path
    except PermissionError as e:
        print(f"[ERROR] Permission denied: {e}")
        print("  Try running as administrator or choose a different destination.")
        return None
    except Exception as e:
        print(f"[ERROR] Failed to publish: {e}")
        return None


def main():
    parser = argparse.ArgumentParser(
        description="Compile the UPAT Living Paper to PDF",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python paper/scripts/compile_paper.py                    # Build only
  python paper/scripts/compile_paper.py --publish          # Build + copy to Desktop
  python paper/scripts/compile_paper.py --publish-to .     # Build + copy to current dir
        """
    )
    parser.add_argument(
        '--publish', '-p',
        action='store_true',
        help='Copy the PDF to Desktop with timestamp'
    )
    parser.add_argument(
        '--publish-to',
        type=str,
        metavar='DIR',
        help='Copy the PDF to a custom directory'
    )
    
    args = parser.parse_args()
    
    # Compile
    pdf_path = compile_pdf()
    
    if pdf_path is None:
        return 1
    
    # Publish if requested
    if args.publish or args.publish_to:
        dest = Path(args.publish_to) if args.publish_to else None
        published = publish_pdf(pdf_path, dest)
        if published is None:
            return 1
        print()
        print("=" * 60)
        print(f"READY: {published}")
        print("=" * 60)
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
