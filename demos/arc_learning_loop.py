"""
ARC Learning Loop: Wake/Sleep Cycle for Open-Ended Predicate Discovery
======================================================================

SGC GROUNDING: This implements the information gradient algorithm:
  1. WAKE: Solve all tasks, record near-miss residuals (information gradient)
  2. SLEEP: Cluster failures, synthesize missing abstractions
  3. MEASURE: Track compression progress (new solves per cycle)
  4. ITERATE: Each cycle expands the predicate library

The gradient is the near-miss residual. The compression is the predicate library.
The progress is measured in new solves. Open-ended because each cycle can
discover predicates inconceivable in the previous cycle.

References:
  - Schmidhuber (2009): Compression Progress as intrinsic motivation
  - Ellis et al. (2021): DreamCoder wake/sleep library learning
  - Koch-Janusz & Ringel (2018): RSMI-RG = IB = optimal coarse-graining
  - Friston (2010): Free Energy Principle / Active Inference
"""

import sys
import time
import json
import numpy as np
from pathlib import Path

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import (
    RecursiveResidualSolver, CompiledProgramLibrary, NearMissJournal
)

# Tensor Logic engine for differentiable predicate discovery
try:
    from arc_tensor_logic import tensor_dream_phase, TensorPredicateLearner
    HAS_TENSOR_LOGIC = True
except ImportError:
    HAS_TENSOR_LOGIC = False


def wake_phase(
    tasks,
    solver: RecursiveResidualSolver,
    verbose: bool = True,
) -> dict:
    """
    Wake phase: solve all tasks, record near-miss residuals.

    Returns summary dict with perfect/near/fail counts and task results.
    """
    results = {
        'perfect': 0, 'near': 0, 'fail': 0,
        'task_results': [],
        'perfect_ids': [],
        'near_ids': [],
    }

    for i, task in enumerate(tasks):
        t0 = time.time()
        try:
            result = solver.solve_task(task)
            d = result['avg_train_energy']
            method = result['method']
            elapsed = time.time() - t0

            is_perfect = result['is_perfect']
            is_near = (not is_perfect and d < 0.1)

            if is_perfect:
                results['perfect'] += 1
                results['perfect_ids'].append(task.task_id)
                status = "PERFECT"
            elif is_near:
                results['near'] += 1
                results['near_ids'].append(task.task_id)
                status = f"near(d={d:.4f})"
            else:
                results['fail'] += 1
                status = f"fail(d={d:.4f})"

            results['task_results'].append({
                'task_id': task.task_id,
                'defect': d,
                'status': status,
                'method': method[:60],
                'elapsed': elapsed,
                'has_analysis': result.get('residual_analysis') is not None,
            })

            if verbose:
                tag = "**" if is_perfect else ("  " if not is_near else "~ ")
                print(f"  [{i+1:3d}/{len(tasks)}] {task.task_id[:8]} "
                      f"d={d:.4f} ({elapsed:.1f}s) {method[:50]} {tag}",
                      flush=True)

        except Exception as e:
            results['fail'] += 1
            results['task_results'].append({
                'task_id': task.task_id,
                'defect': 1.0,
                'status': f"error: {e}",
                'method': 'error',
                'elapsed': time.time() - t0,
                'has_analysis': False,
            })
            if verbose:
                print(f"  [{i+1:3d}/{len(tasks)}] {task.task_id[:8]} ERROR: {e}",
                      flush=True)

    return results


def sleep_phase(
    journal: NearMissJournal,
    verbose: bool = True,
) -> list:
    """
    Sleep phase: cluster near-miss failures and propose new abstractions.

    Returns list of abstraction proposals.
    """
    if verbose:
        print(f"\n{'='*60}")
        print(f"SLEEP PHASE: Analyzing {len(journal.entries)} near-misses")
        print(f"{'='*60}")

    proposals = journal.sleep_phase(verbose=verbose)

    if verbose:
        print(f"\n  Total proposals: {len(proposals)}")
        for p in proposals:
            print(f"    [{p['n_tasks']} tasks] {p['description']}")
            print(f"      Key: {p['cluster_key']}")
            print(f"      Avg gap: {p['avg_predicate_gap']:.3f}")
            print(f"      Adj colors: {p['common_adjacent_colors']}")
            print(f"      Res colors: {p['common_residual_colors']}")

    return proposals


def run_learning_loop(
    data_path: str = None,
    n_cycles: int = 1,
    verbose: bool = True,
    journal_path: str = "learning_journal.json",
    dream_path: str = "learning_dreams.json",
):
    """
    Run the full wake/sleep learning loop.

    Args:
        data_path: path to ARC training data
        n_cycles: number of wake/sleep cycles to run
        verbose: print progress
        journal_path: where to persist the near-miss journal
        dream_path: where to persist compiled programs
    """
    if data_path is None:
        data_path = str(Path(__file__).parent.parent / "data" / "arc" / "training")

    # Load tasks
    print(f"Loading tasks from {data_path}...", flush=True)
    tasks = load_arc_tasks(data_path)
    print(f"Loaded {len(tasks)} tasks", flush=True)

    # Load persistent state
    journal = NearMissJournal.load_from_json(journal_path)
    compiled = CompiledProgramLibrary.load_from_json(dream_path)

    print(f"Journal: {len(journal.entries)} entries from previous sessions")
    print(f"Dreams: {compiled.size} compiled programs")

    for cycle in range(n_cycles):
        print(f"\n{'#'*60}")
        print(f"# CYCLE {cycle + 1}/{n_cycles}")
        print(f"{'#'*60}")

        # Create solver with current library and journal
        solver = RecursiveResidualSolver(
            max_depth=3, beam_width=8, verbose=False,
            compiled_library=compiled,
            near_miss_journal=journal,
        )

        # WAKE: Solve all tasks
        print(f"\n--- WAKE PHASE ---")
        t0 = time.time()
        results = wake_phase(tasks, solver, verbose=verbose)
        wake_time = time.time() - t0

        print(f"\n  Wake results: {results['perfect']}P / "
              f"{results['near']}N / {results['fail']}F "
              f"({wake_time:.1f}s)")
        print(f"  Perfect: {results['perfect_ids']}")

        # TENSOR DREAM: Differentiable predicate discovery on near-misses
        # (Domingos 2024, arXiv:2510.12269)
        # SGC: min_Pi eps(Pi,L) via gradient descent on soft predicates
        tensor_results = []
        if HAS_TENSOR_LOGIC:
            print(f"\n--- TENSOR DREAM PHASE ---")
            # Collect near-miss task data for tensor factorization
            near_miss_data = []
            for tr in results['task_results']:
                if 0.001 < tr['defect'] < 0.15 and tr['method'] != 'error':
                    # Find the matching task object
                    task_obj = None
                    for t in tasks:
                        if t.task_id == tr['task_id']:
                            task_obj = t
                            break
                    if task_obj is None:
                        continue
                    grids = [ex.input_grid.data.numpy() for ex in task_obj.train_examples]
                    targets = [ex.output_grid.data.numpy() for ex in task_obj.train_examples]
                    near_miss_data.append({
                        'task_id': tr['task_id'],
                        'grids': grids,
                        'targets': targets,
                    })

            if near_miss_data:
                try:
                    tensor_results = tensor_dream_phase(
                        near_miss_data, n_factors=4, lr=0.05, steps=250,
                        verbose=verbose)
                    n_strong = sum(1 for r in tensor_results if r['best_f1'] > 0.5)
                    print(f"\n  Tensor dream: {len(tensor_results)} tasks analyzed, "
                          f"{n_strong} with strong predicates (F1 > 0.5)")
                except Exception as e:
                    print(f"  Tensor dream error: {e}")
            else:
                print(f"  No near-miss tasks for tensor dream")

        # SLEEP: Analyze failures and propose abstractions
        print(f"\n--- SLEEP PHASE ---")
        proposals = sleep_phase(journal, verbose=verbose)

        # MEASURE: Compression progress
        progress = journal.compression_progress()
        print(f"\n--- COMPRESSION PROGRESS ---")
        print(f"  Journal entries: {len(journal.entries)}")
        print(f"  Clusters: {len(journal.cluster())}")
        print(f"  Progress rate: {progress:.3f}")

        if journal.cycle_history:
            latest = journal.cycle_history[-1]
            print(f"  Proposals this cycle: {latest['n_proposals']}")

        # Save state
        journal.save_to_json(journal_path)
        compiled.save_to_json(dream_path)
        print(f"\n  Saved journal to {journal_path}")
        print(f"  Saved dreams to {dream_path}")

    # Final report
    print(f"\n{'='*60}")
    print(f"FINAL REPORT")
    print(f"{'='*60}")
    print(f"Perfect solves: {results['perfect']}/{len(tasks)}")
    print(f"Near-misses: {results['near']}/{len(tasks)}")
    print(f"Journal entries: {len(journal.entries)}")

    clusters = journal.cluster()
    print(f"\nFailure clusters ({len(clusters)}):")
    for key, entries in clusters.items():
        print(f"  [{len(entries):2d}] {key}")
        for e in entries[:3]:
            print(f"       {e.task_id[:8]} d={e.defect:.4f} "
                  f"pred={e.best_predicate[:30] if e.best_predicate else 'none'} "
                  f"gap={e.predicate_gap:.3f}")
        if len(entries) > 3:
            print(f"       ... and {len(entries)-3} more")

    return {
        'results': results,
        'journal': journal,
        'proposals': proposals,
    }


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="ARC Learning Loop")
    parser.add_argument("--data", type=str, default=None,
                        help="Path to ARC training data")
    parser.add_argument("--cycles", type=int, default=1,
                        help="Number of wake/sleep cycles")
    parser.add_argument("--journal", type=str, default="learning_journal.json",
                        help="Journal persistence path")
    parser.add_argument("--dreams", type=str, default="learning_dreams.json",
                        help="Dream library persistence path")
    parser.add_argument("--quiet", action="store_true",
                        help="Reduce output verbosity")
    args = parser.parse_args()

    run_learning_loop(
        data_path=args.data,
        n_cycles=args.cycles,
        verbose=not args.quiet,
        journal_path=args.journal,
        dream_path=args.dreams,
    )
