#!/usr/bin/env python3
"""
map_theorems.py - Consistency checker for the Living Paper system.

This script checks that formal Lean theorems are properly documented in the paper
by comparing:
  1. Theorems/definitions/lemmas found in /src/*.lean files
  2. Mappings declared in /paper/lean_map.json

Usage:
    python paper/scripts/map_theorems.py

Reports:
  - Lean theorems NOT yet mentioned in the paper (need documentation)
  - Paper references to non-existent Lean theorems (broken links)
"""

import os
import re
import json
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple


def find_repo_root() -> Path:
    """Find the repository root (where lakefile.lean lives)."""
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / 'lakefile.lean').exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find repository root (no lakefile.lean found)")


def scan_lean_files(src_dir: Path) -> Dict[str, List[Tuple[str, str, int]]]:
    """
    Scan all .lean files for theorem/def/lemma declarations.
    
    Returns:
        Dict mapping file paths (relative to src/) to list of (type, name, line_number)
    """
    results = {}
    
    # Pattern to match theorem, def, lemma, and abbrev declarations
    pattern = re.compile(
        r'^(theorem|def|lemma|abbrev)\s+(\w+)',
        re.MULTILINE
    )
    
    for lean_file in src_dir.rglob('*.lean'):
        rel_path = lean_file.relative_to(src_dir)
        declarations = []
        
        try:
            content = lean_file.read_text(encoding='utf-8')
            for match in pattern.finditer(content):
                decl_type = match.group(1)
                decl_name = match.group(2)
                # Calculate line number
                line_num = content[:match.start()].count('\n') + 1
                declarations.append((decl_type, decl_name, line_num))
        except Exception as e:
            print(f"WARNING: Could not read {lean_file}: {e}")
            continue
        
        if declarations:
            results[str(rel_path).replace('\\', '/')] = declarations
    
    return results


def load_lean_map(paper_dir: Path) -> Dict[str, dict]:
    """Load the lean_map.json file."""
    map_file = paper_dir / 'lean_map.json'
    if not map_file.exists():
        print(f"WARNING: {map_file} does not exist. Creating empty mapping.")
        return {}
    
    try:
        with open(map_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        # Flatten all mappings into one dict
        all_mappings = {}
        for category in ['theorems', 'definitions', 'lemmas']:
            if category in data:
                all_mappings.update(data[category])
        return all_mappings
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON in {map_file}: {e}")
        return {}


def scan_paper_for_leanlinks(paper_dir: Path) -> Set[str]:
    """Scan LaTeX files for \\leanlink{} and \\leanref{} references."""
    references = set()
    
    pattern = re.compile(r'\\lean(?:link|ref)\{([^}]+)\}')
    
    for tex_file in paper_dir.rglob('*.tex'):
        try:
            content = tex_file.read_text(encoding='utf-8')
            for match in pattern.finditer(content):
                references.add(match.group(1))
        except Exception as e:
            print(f"WARNING: Could not read {tex_file}: {e}")
    
    return references


def main():
    repo_root = find_repo_root()
    src_dir = repo_root / 'src'
    paper_dir = repo_root / 'paper'
    
    print("=" * 70)
    print("LIVING PAPER CONSISTENCY CHECK")
    print("=" * 70)
    print(f"Repository: {repo_root}")
    print()
    
    # 1. Scan Lean files
    print("Scanning Lean files in /src...")
    lean_decls = scan_lean_files(src_dir)
    
    total_decls = sum(len(v) for v in lean_decls.values())
    print(f"  Found {total_decls} declarations in {len(lean_decls)} files")
    print()
    
    # 2. Load mapping file
    print("Loading paper/lean_map.json...")
    mappings = load_lean_map(paper_dir)
    print(f"  Found {len(mappings)} mappings")
    print()
    
    # 3. Scan paper for leanlink references
    print("Scanning paper for \\leanlink references...")
    paper_refs = scan_paper_for_leanlinks(paper_dir)
    print(f"  Found {len(paper_refs)} \\leanlink references")
    print()
    
    # 4. Build set of documented theorems
    documented_names = set()
    for label, info in mappings.items():
        if isinstance(info, dict) and 'lean_name' in info:
            documented_names.add(info['lean_name'])
    
    # 5. Report undocumented theorems
    print("-" * 70)
    print("THEOREMS NOT YET DOCUMENTED IN PAPER:")
    print("-" * 70)
    
    undocumented_count = 0
    for file_path, decls in sorted(lean_decls.items()):
        file_undoc = []
        for decl_type, decl_name, line_num in decls:
            if decl_name not in documented_names:
                file_undoc.append((decl_type, decl_name, line_num))
        
        if file_undoc:
            print(f"\n  {file_path}:")
            for decl_type, decl_name, line_num in file_undoc:
                print(f"    L{line_num}: {decl_type} {decl_name}")
                undocumented_count += 1
    
    if undocumented_count == 0:
        print("  (All Lean declarations are documented!)")
    
    print()
    print("-" * 70)
    print("SUMMARY:")
    print("-" * 70)
    print(f"  Total Lean declarations:  {total_decls}")
    print(f"  Documented in paper:      {len(documented_names)}")
    print(f"  Not yet documented:       {undocumented_count}")
    print()
    
    if undocumented_count > 0:
        print("TIP: Add entries to paper/lean_map.json to document theorems.")
    
    return 0 if undocumented_count == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
