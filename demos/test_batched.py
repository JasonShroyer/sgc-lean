"""Test Intelligent Task Batching on 97 ARC training tasks.

Implements the SGC-ARC Deep Dive: Methods & Task Batching recommendation.
Tasks are clustered by signature, solved in groups with cross-task transfer,
then refined with enriched priors in a second pass.

Baseline: 20 perfect (sequential agent), 19 perfect (previous session)

LOGGING: Output goes to both stdout AND a log file for real-time monitoring.
  To watch live:  Get-Content -Wait batched_run.log
"""
import os, sys, time, io

# === FORCE UNBUFFERED OUTPUT (fixes Windows logging issue) ===
os.environ['PYTHONUNBUFFERED'] = '1'
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8',
                               errors='replace', line_buffering=True)

# Tee class: write to both stdout and log file
class Tee:
    def __init__(self, stdout, log_path):
        self.stdout = stdout
        self.log_file = open(log_path, 'w', encoding='utf-8', buffering=1)
    def write(self, data):
        self.stdout.write(data)
        self.log_file.write(data)
        self.log_file.flush()
    def flush(self):
        self.stdout.flush()
        self.log_file.flush()

LOG_PATH = 'batched_run.log'
sys.stdout = Tee(sys.stdout, LOG_PATH)

sys.path.insert(0, '.')
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_agent import ARCSGCAgent, solve_batched

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
print(f'Loaded {len(tasks)} tasks', flush=True)
print(f'Log file: {os.path.abspath(LOG_PATH)}', flush=True)
print(f'Watch live: Get-Content -Wait {LOG_PATH}', flush=True)

# Use test memory file
MEMORY_PATH = 'agent_memory_batch_test.json'

agent = ARCSGCAgent(
    memory_path=MEMORY_PATH,
    verbose=False,
    recall_enabled=True,
    update_enabled=True,
)

# Report initial state
prior = agent.ltm.predicate_prior
print(f'Initial prior: {prior.total_tasks} tasks, '
      f'{len(prior.attempt_counts)} predicates', flush=True)
print(f'Compiled library: {agent.compiled_library.size} programs, '
      f'{len(agent.compiled_library.near_misses)} near-misses', flush=True)

t0 = time.time()

# Run batched solver with 2 passes
result = solve_batched(
    agent=agent,
    tasks=tasks[:97],
    n_passes=2,
    verbose=True,
)

elapsed = time.time() - t0

# Save memory
agent.save_memory()

# Final agent stats
print(f"\nAgent stats:", flush=True)
stats = agent.get_stats()
for section, data in stats.items():
    print(f"  {section}:", flush=True)
    if isinstance(data, dict):
        for k, v in data.items():
            print(f"    {k}: {v}", flush=True)
    else:
        print(f"    {data}", flush=True)

print(f"\nTotal time: {elapsed:.0f}s", flush=True)
print(f"Log saved to: {os.path.abspath(LOG_PATH)}", flush=True)
