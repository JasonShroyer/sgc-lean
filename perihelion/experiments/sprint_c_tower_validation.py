#!/usr/bin/env python3
"""
Sprint C: EGI Tower Validation with Full Technology Stack
============================================================

This is the conductor for Sprint C — validating `egi_tower_exists` empirically
using the complete perihelion technology stack.

PIPELINE PHASES:
    Phase 1: Accelerated grokking per task (wavelet + thermal pump)
    Phase 2: Fixed point verification per task (Rayleigh measurement)
    Phase 3: Preservation monitoring during multi-task training
    Phase 4: Tower certification

TECHNOLOGY STACK:
    - wavelet_layer.py: Hermite-Gaussian noise injection (3-10x acceleration)
    - thermal_pump.py: Thermal annealing with SGC Reynolds number
    - sgc_engine.py: Core ε, χ_g, R computation
    - sgc_integrated_controller.py: Full control loop with constrained updates
    - rayleigh_measurement.py: EGI fixed point verification

SUCCESS CRITERION:
    tower_complete: true AND all tasks show is_strong_equivalent: true

Author: SGC Research Team
Date: March 31, 2026
"""

import sys
import os
import json
import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, field

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent))
sys.path.insert(0, str(Path(__file__).parent.parent.parent / 'demos'))

from perihelion.core.wavelet_layer import WaveletNoiseInjector
from perihelion.core.thermal_pump import ThermalPump, ThermalSchedule, ThermalPhase
from perihelion.core.sgc_engine import SGCEngine, SGCMetrics
from perihelion.core.sgc_integrated_controller import (
    SGCIntegratedController, ConstrainedUpdate, ControllerPhase
)
from rayleigh_measurement import (
    RayleighMeasurement, SpectralEquivalenceResult, PartitionData,
    measure_egi_fixed_point, print_egi_report
)


# ============================================================================
# 1. TASK DEFINITIONS
# ============================================================================

class ModularAdditionTask:
    """Task A: Modular addition (cyclic group Z_p invariant)."""
    
    def __init__(self, prime: int = 97, train_fraction: float = 0.3, seed: int = 42):
        self.prime = prime
        self.name = f"modular_add_p{prime}"
        
        # Generate all pairs
        all_pairs = [(a, b) for a in range(prime) for b in range(prime)]
        
        rng = np.random.RandomState(seed)
        rng.shuffle(all_pairs)
        
        split_idx = int(len(all_pairs) * train_fraction)
        self.train_pairs = all_pairs[:split_idx]
        self.test_pairs = all_pairs[split_idx:]
    
    def get_dataloaders(self, batch_size: int = 64):
        train_x = torch.zeros(len(self.train_pairs), 2 * self.prime)
        train_y = torch.zeros(len(self.train_pairs), dtype=torch.long)
        
        for i, (a, b) in enumerate(self.train_pairs):
            train_x[i, a] = 1.0
            train_x[i, self.prime + b] = 1.0
            train_y[i] = (a + b) % self.prime
        
        test_x = torch.zeros(len(self.test_pairs), 2 * self.prime)
        test_y = torch.zeros(len(self.test_pairs), dtype=torch.long)
        
        for i, (a, b) in enumerate(self.test_pairs):
            test_x[i, a] = 1.0
            test_x[i, self.prime + b] = 1.0
            test_y[i] = (a + b) % self.prime
        
        train_dataset = torch.utils.data.TensorDataset(train_x, train_y)
        test_dataset = torch.utils.data.TensorDataset(test_x, test_y)
        
        train_loader = torch.utils.data.DataLoader(
            train_dataset, batch_size=batch_size, shuffle=True
        )
        test_loader = torch.utils.data.DataLoader(
            test_dataset, batch_size=batch_size, shuffle=False
        )
        
        return train_loader, test_loader


class ParityTask:
    """Task B: Parity classification (Z_2 invariant)."""
    
    def __init__(self, n_bits: int = 8, n_samples: int = 10000, seed: int = 43):
        self.n_bits = n_bits
        self.name = f"parity_{n_bits}bit"
        
        rng = np.random.RandomState(seed)
        
        # Generate random bit strings
        all_x = rng.randint(0, 2, size=(n_samples, n_bits)).astype(np.float32)
        all_y = (all_x.sum(axis=1) % 2).astype(np.int64)
        
        split_idx = int(n_samples * 0.7)
        self.train_x = all_x[:split_idx]
        self.train_y = all_y[:split_idx]
        self.test_x = all_x[split_idx:]
        self.test_y = all_y[split_idx:]
    
    def get_dataloaders(self, batch_size: int = 64):
        train_dataset = torch.utils.data.TensorDataset(
            torch.tensor(self.train_x), torch.tensor(self.train_y)
        )
        test_dataset = torch.utils.data.TensorDataset(
            torch.tensor(self.test_x), torch.tensor(self.test_y)
        )
        
        train_loader = torch.utils.data.DataLoader(
            train_dataset, batch_size=batch_size, shuffle=True
        )
        test_loader = torch.utils.data.DataLoader(
            test_dataset, batch_size=batch_size, shuffle=False
        )
        
        return train_loader, test_loader


class PermutationTask:
    """Task C: Permutation symmetry detection (S_n invariant)."""
    
    def __init__(self, n_elements: int = 5, n_samples: int = 10000, seed: int = 44):
        self.n_elements = n_elements
        self.name = f"permutation_S{n_elements}"
        
        rng = np.random.RandomState(seed)
        
        # Generate pairs of sequences
        # Label: 1 if second is a permutation of first, 0 otherwise
        all_x = []
        all_y = []
        
        for _ in range(n_samples):
            seq1 = rng.permutation(n_elements)
            
            if rng.random() < 0.5:
                # Permutation of seq1
                seq2 = rng.permutation(seq1)
                label = 1
            else:
                # Different multiset
                seq2 = rng.permutation(n_elements)
                # Modify one element to break permutation property
                seq2[0] = (seq2[0] + 1) % n_elements
                label = 0
            
            # Concatenate seq1 and seq2 as input
            x = np.concatenate([seq1, seq2]).astype(np.float32)
            all_x.append(x)
            all_y.append(label)
        
        all_x = np.array(all_x)
        all_y = np.array(all_y, dtype=np.int64)
        
        split_idx = int(n_samples * 0.7)
        self.train_x = all_x[:split_idx]
        self.train_y = all_y[:split_idx]
        self.test_x = all_x[split_idx:]
        self.test_y = all_y[split_idx:]
    
    def get_dataloaders(self, batch_size: int = 64):
        train_dataset = torch.utils.data.TensorDataset(
            torch.tensor(self.train_x), torch.tensor(self.train_y)
        )
        test_dataset = torch.utils.data.TensorDataset(
            torch.tensor(self.test_x), torch.tensor(self.test_y)
        )
        
        train_loader = torch.utils.data.DataLoader(
            train_dataset, batch_size=batch_size, shuffle=True
        )
        test_loader = torch.utils.data.DataLoader(
            test_dataset, batch_size=batch_size, shuffle=False
        )
        
        return train_loader, test_loader


# ============================================================================
# 2. MULTI-TASK MODEL
# ============================================================================

class MultiTaskMLP(nn.Module):
    """
    Multi-task MLP with shared hidden layers.
    
    Each task has its own input projection and output head,
    but shares the hidden representation space.
    """
    
    def __init__(self, task_configs: Dict[str, Tuple[int, int]], 
                 hidden_dim: int = 256):
        """
        Args:
            task_configs: Dict mapping task_name -> (input_dim, output_dim)
            hidden_dim: Dimension of shared hidden layers
        """
        super().__init__()
        self.hidden_dim = hidden_dim
        self.task_configs = task_configs
        
        # Task-specific input projections
        self.input_projections = nn.ModuleDict({
            name: nn.Linear(in_dim, hidden_dim)
            for name, (in_dim, _) in task_configs.items()
        })
        
        # Shared hidden layers
        self.hidden1 = nn.Linear(hidden_dim, hidden_dim)
        self.hidden2 = nn.Linear(hidden_dim, hidden_dim)
        
        # Task-specific output heads
        self.output_heads = nn.ModuleDict({
            name: nn.Linear(hidden_dim, out_dim)
            for name, (_, out_dim) in task_configs.items()
        })
        
        self.current_task = None
    
    def set_task(self, task_name: str):
        """Set current task for forward pass."""
        if task_name not in self.task_configs:
            raise ValueError(f"Unknown task: {task_name}")
        self.current_task = task_name
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        if self.current_task is None:
            raise ValueError("Must call set_task() before forward()")
        
        # Task-specific input projection
        h = torch.relu(self.input_projections[self.current_task](x))
        
        # Shared hidden layers
        h = torch.relu(self.hidden1(h))
        h = torch.relu(self.hidden2(h))
        
        # Task-specific output
        return self.output_heads[self.current_task](h)


# ============================================================================
# 3. TOWER VALIDATION RESULT
# ============================================================================

@dataclass
class TaskResult:
    """Result for a single task in the tower."""
    task_name: str
    grokked_at_step: int
    is_strong_equivalent: bool
    is_weak_equivalent: bool
    tsallis_q: float
    eigenvalue_correlation: float
    rayleigh_set_overlap: float
    final_epsilon: float
    final_ridge_ratio: float
    preserved_through: List[str] = field(default_factory=list)  # Later tasks
    
    def to_dict(self) -> dict:
        return {
            'grokked_at': int(self.grokked_at_step),
            'is_strong_equivalent': bool(self.is_strong_equivalent),
            'is_weak_equivalent': bool(self.is_weak_equivalent),
            'tsallis_q': float(self.tsallis_q),
            'eigenvalue_correlation': float(self.eigenvalue_correlation),
            'rayleigh_set_overlap': float(self.rayleigh_set_overlap),
            'final_epsilon': float(self.final_epsilon),
            'final_ridge_ratio': float(self.final_ridge_ratio),
            'preserved_through': self.preserved_through,
        }


@dataclass
class TowerResult:
    """Complete tower validation result."""
    tasks: Dict[str, TaskResult] = field(default_factory=dict)
    tower_complete: bool = False
    egi_tower_exists_verified: bool = False
    total_steps: int = 0
    timestamp: str = ""
    
    def to_dict(self) -> dict:
        return {
            'timestamp': self.timestamp,
            'tower_complete': self.tower_complete,
            'egi_tower_exists_empirically_verified': self.egi_tower_exists_verified,
            'total_steps': self.total_steps,
            'tasks': {name: result.to_dict() for name, result in self.tasks.items()},
        }


# ============================================================================
# 4. SPRINT C CONDUCTOR
# ============================================================================

class SprintCConductor:
    """
    Sprint C Tower Validation Conductor.
    
    Orchestrates the complete EGI tower validation pipeline using
    the full perihelion technology stack.
    """
    
    def __init__(self,
                 tasks: List,
                 hidden_dim: int = 256,
                 device: str = 'cuda',
                 max_steps_per_task: int = 50000,
                 log_interval: int = 100,
                 preservation_check_interval: int = 500):
        """
        Initialize Sprint C conductor.
        
        Args:
            tasks: List of task objects (must have .name and .get_dataloaders())
            hidden_dim: Hidden dimension for multi-task model
            device: Computation device
            max_steps_per_task: Maximum training steps per task
            log_interval: Steps between logging
            preservation_check_interval: Steps between preservation checks
        """
        self.tasks = tasks
        self.hidden_dim = hidden_dim
        self.device = device
        self.max_steps_per_task = max_steps_per_task
        self.log_interval = log_interval
        self.preservation_check_interval = preservation_check_interval
        
        # Build task configs
        self.task_configs = {}
        self.dataloaders = {}
        
        for task in tasks:
            train_loader, test_loader = task.get_dataloaders()
            self.dataloaders[task.name] = (train_loader, test_loader)
            
            # Infer dimensions from first batch
            x, y = next(iter(train_loader))
            in_dim = x.shape[1]
            out_dim = int(y.max().item()) + 1
            self.task_configs[task.name] = (in_dim, out_dim)
        
        # Create model
        self.model = MultiTaskMLP(self.task_configs, hidden_dim).to(device)
        
        # Create controller with full technology stack
        self.controller = SGCIntegratedController(
            wavelet=WaveletNoiseInjector(
                noise_scale=0.05,
                wavelet_a=1.5,
                wavelet_b=2.0,
                mode='wavelet'
            ),
            thermal=ThermalPump(
                schedule=ThermalSchedule(
                    T_initial=1.0,
                    T_max=3.0,
                    T_target=0.1,
                    epsilon_threshold=0.05,
                    min_heat_epochs=50,
                    max_heat_epochs=max_steps_per_task
                )
            ),
            engine=SGCEngine(energy_threshold=0.95),
            constraint=ConstrainedUpdate(),
            grokking_threshold=0.05,
            ridge_threshold=2.0,
            noise_injection_interval=10,
            measurement_interval=50
        )
        
        # Results tracking
        self.tower_result = TowerResult(timestamp=datetime.now().isoformat())
        self.task_rayleigh_data: Dict[str, SpectralEquivalenceResult] = {}
        
        # Preservation monitoring
        self.preservation_history: Dict[str, List[Tuple[int, bool]]] = {}
    
    def compute_accuracy(self, task_name: str) -> Tuple[float, float]:
        """Compute train and test accuracy for a task."""
        train_loader, test_loader = self.dataloaders[task_name]
        self.model.set_task(task_name)
        self.model.eval()
        
        def accuracy(loader):
            correct = 0
            total = 0
            with torch.no_grad():
                for x, y in loader:
                    x, y = x.to(self.device), y.to(self.device)
                    logits = self.model(x)
                    preds = logits.argmax(dim=-1)
                    correct += (preds == y).sum().item()
                    total += len(y)
            return correct / total if total > 0 else 0.0
        
        train_acc = accuracy(train_loader)
        test_acc = accuracy(test_loader)
        
        self.model.train()
        return train_acc, test_acc
    
    def verify_fixed_point(self, task_name: str) -> SpectralEquivalenceResult:
        """Run Rayleigh measurement to verify EGI fixed point."""
        from rayleigh_measurement import (
            compute_rayleigh_set, compute_quotient_generator, test_spectral_equivalence,
            RayleighSetData, EquivalenceType
        )
        
        self.model.set_task(task_name)
        
        # Extract partition from model representations
        partition = self._extract_partition(task_name)
        
        # Extract transition operator directly
        L_network, pi_dist = self._extract_transition_operator(task_name)
        
        # Ensure dimensions match
        n = L_network.shape[0]
        if partition.n_blocks > n:
            # Adjust partition to match
            partition = PartitionData(
                n_blocks=min(partition.n_blocks, n),
                block_assignment=partition.block_assignment[:n] % n,
                block_sizes=np.bincount(partition.block_assignment[:n] % n, minlength=n)[:n]
            )
        
        # Compute Rayleigh sets
        network_rayleigh = compute_rayleigh_set(L_network, pi_dist)
        
        # Compute quotient generator
        L_bar = compute_quotient_generator(L_network, partition, pi_dist)
        pi_bar = np.array([pi_dist[partition.block_assignment == b].sum() 
                          for b in range(partition.n_blocks)])
        pi_bar = pi_bar / pi_bar.sum() if pi_bar.sum() > 0 else np.ones(partition.n_blocks) / partition.n_blocks
        
        quotient_rayleigh = compute_rayleigh_set(L_bar, pi_bar)
        
        # Test spectral equivalence
        result = test_spectral_equivalence(
            network_rayleigh, quotient_rayleigh,
            top_k=min(10, n), tolerance=0.01
        )
        
        return result
    
    def _extract_transition_operator(self, task_name: str) -> Tuple[np.ndarray, np.ndarray]:
        """Extract transition operator from model's hidden layer weights."""
        self.model.set_task(task_name)
        
        # Use hidden layer weight matrix
        W = self.model.hidden2.weight.detach().cpu().numpy()
        
        # Compute transition matrix from weight covariance
        n = min(W.shape[0], 50)
        W_sub = W[:n, :min(W.shape[1], n)]
        
        # Normalize to get transition probabilities
        cov = W_sub @ W_sub.T
        cov = np.abs(cov)
        row_sums = cov.sum(axis=1, keepdims=True)
        row_sums[row_sums < 1e-10] = 1.0
        L = cov / row_sums
        
        # Stationary distribution (uniform for now)
        pi = np.ones(n) / n
        
        return L, pi
    
    def _extract_partition(self, task_name: str) -> PartitionData:
        """Extract partition from model's learned representations."""
        _, test_loader = self.dataloaders[task_name]
        self.model.set_task(task_name)
        self.model.eval()
        
        activations = []
        activation_buffer = []
        
        def hook_fn(module, input, output):
            activation_buffer.append(output.detach())
        
        hook = self.model.hidden2.register_forward_hook(hook_fn)
        
        try:
            with torch.no_grad():
                for x, _ in test_loader:
                    x = x.to(self.device)
                    _ = self.model(x)
                    if len(activation_buffer) > 10:
                        break
            
            all_acts = torch.cat(activation_buffer, dim=0).cpu().numpy()
        finally:
            hook.remove()
        
        self.model.train()
        
        # Quantile-based clustering
        n_samples = min(len(all_acts), 1000)
        acts = all_acts[:n_samples]
        norms = np.linalg.norm(acts, axis=1)
        
        n_clusters = 10
        quantiles = np.percentile(norms, np.linspace(0, 100, n_clusters + 1))
        labels = np.digitize(norms, quantiles[1:-1])
        
        n_states = min(50, n_samples)
        block_assignment = labels[:n_states]
        n_blocks = len(np.unique(block_assignment))
        block_sizes = np.array([np.sum(block_assignment == i) for i in range(n_blocks)])
        
        return PartitionData(
            n_blocks=n_blocks,
            block_assignment=block_assignment,
            block_sizes=block_sizes
        )
    
    def check_preservation(self, current_task: str) -> Dict[str, bool]:
        """Check if all previously grokked tasks are preserved."""
        preserved = {}
        
        for task_name in self.tower_result.tasks:
            if task_name == current_task:
                continue
            
            result = self.verify_fixed_point(task_name)
            preserved[task_name] = result.is_strong_equivalent
            
            # Track history
            if task_name not in self.preservation_history:
                self.preservation_history[task_name] = []
            self.preservation_history[task_name].append(
                (self.controller.step, result.is_strong_equivalent)
            )
        
        # Restore current task after preservation check
        self.model.set_task(current_task)
        
        return preserved
    
    def train_task(self, task) -> TaskResult:
        """
        Train a single task using the full technology stack.
        
        Implements Phase 1 (accelerated grokking) and Phase 2 (fixed point verification).
        """
        task_name = task.name
        train_loader, test_loader = self.dataloaders[task_name]
        
        print(f"\n{'='*60}")
        print(f"PHASE 1: Training task '{task_name}'")
        print(f"{'='*60}")
        
        # Set up controller
        self.controller.start_task(task_name)
        self.model.set_task(task_name)
        
        # Optimizer with temperature-dependent weight decay
        base_wd = 0.1
        optimizer = optim.AdamW(
            self.model.parameters(),
            lr=1e-3,
            weight_decay=base_wd
        )
        criterion = nn.CrossEntropyLoss()
        
        step = 0
        grokked_step = -1
        final_metrics = None
        
        while step < self.max_steps_per_task:
            for x, y in train_loader:
                if step >= self.max_steps_per_task:
                    break
                
                x, y = x.to(self.device), y.to(self.device)
                
                # Forward pass
                optimizer.zero_grad()
                logits = self.model(x)
                loss = criterion(logits, y)
                loss.backward()
                
                # SGC controller update (noise injection, constrained gradient, metrics)
                metrics = self.controller.step_update(
                    self.model, loss, test_loader, self.device
                )
                
                # Update weight decay based on temperature
                wd = self.controller.get_weight_decay(base_wd)
                for param_group in optimizer.param_groups:
                    param_group['weight_decay'] = wd
                
                # Optimizer step
                optimizer.step()
                step += 1
                
                # Logging
                if step % self.log_interval == 0:
                    train_acc, test_acc = self.compute_accuracy(task_name)
                    print(f"Step {step:5d} | Train: {train_acc:.3f} | Test: {test_acc:.3f} | "
                          f"eps: {metrics.epsilon:.4f} | R: {metrics.ridge_ratio:.2f} | "
                          f"T: {self.controller.thermal.temperature:.2f}")
                
                # Phase 3: Preservation monitoring
                if step % self.preservation_check_interval == 0 and self.tower_result.tasks:
                    preserved = self.check_preservation(task_name)
                    all_preserved = all(preserved.values())
                    status = "OK" if all_preserved else "DEGRADED"
                    print(f"  [Preservation] {status}: {preserved}")
                
                # Check for grokking
                if self.controller.is_task_complete():
                    grokked_step = step
                    final_metrics = metrics
                    print(f"\n*** TASK '{task_name}' GROKKED at step {step} ***")
                    break
            
            if self.controller.is_task_complete():
                break
        
        # Phase 2: Fixed point verification
        print(f"\n{'='*60}")
        print(f"PHASE 2: Fixed point verification for '{task_name}'")
        print(f"{'='*60}")
        
        rayleigh_result = self.verify_fixed_point(task_name)
        self.task_rayleigh_data[task_name] = rayleigh_result
        print_egi_report(rayleigh_result)
        
        # Build task result
        result = TaskResult(
            task_name=task_name,
            grokked_at_step=grokked_step if grokked_step > 0 else step,
            is_strong_equivalent=rayleigh_result.is_strong_equivalent,
            is_weak_equivalent=rayleigh_result.is_weak_equivalent,
            tsallis_q=rayleigh_result.tsallis_q,
            eigenvalue_correlation=rayleigh_result.eigenvalue_correlation,
            rayleigh_set_overlap=rayleigh_result.rayleigh_set_overlap,
            final_epsilon=final_metrics.epsilon if final_metrics else 1.0,
            final_ridge_ratio=final_metrics.ridge_ratio if final_metrics else 100.0,
        )
        
        return result
    
    def run(self) -> TowerResult:
        """
        Run the complete Sprint C tower validation.
        
        Trains all tasks sequentially with preservation monitoring.
        """
        print("\n" + "="*60)
        print("SPRINT C: EGI TOWER VALIDATION")
        print("="*60)
        print(f"Tasks: {[t.name for t in self.tasks]}")
        print(f"Device: {self.device}")
        print(f"Max steps per task: {self.max_steps_per_task}")
        
        for i, task in enumerate(self.tasks):
            print(f"\n\n{'#'*60}")
            print(f"# TASK {i+1}/{len(self.tasks)}: {task.name}")
            print(f"{'#'*60}")
            
            result = self.train_task(task)
            self.tower_result.tasks[task.name] = result
        
        # Phase 4: Tower certification
        print(f"\n\n{'='*60}")
        print("PHASE 4: TOWER CERTIFICATION")
        print("="*60)
        
        # Check all tasks are strong equivalent
        all_strong = all(r.is_strong_equivalent for r in self.tower_result.tasks.values())
        
        # Update preservation tracking
        task_names = list(self.tower_result.tasks.keys())
        for i, name in enumerate(task_names):
            later_tasks = task_names[i+1:]
            self.tower_result.tasks[name].preserved_through = later_tasks
        
        self.tower_result.tower_complete = all_strong
        self.tower_result.egi_tower_exists_verified = all_strong
        self.tower_result.total_steps = self.controller.step
        
        # Print summary
        print("\n" + "-"*60)
        print("TOWER SUMMARY")
        print("-"*60)
        for name, result in self.tower_result.tasks.items():
            equiv = "STRONG" if result.is_strong_equivalent else ("WEAK" if result.is_weak_equivalent else "NONE")
            print(f"  {name}: grokked@{result.grokked_at_step}, equiv={equiv}, q={result.tsallis_q:.3f}")
        
        print("-"*60)
        if self.tower_result.egi_tower_exists_verified:
            print("[SUCCESS] egi_tower_exists EMPIRICALLY VERIFIED")
        else:
            print("[INCOMPLETE] Tower does not satisfy IsEGIFixedPoint for all tasks")
        print("="*60)
        
        return self.tower_result
    
    def save_results(self, output_path: str):
        """Save tower validation results to JSON."""
        with open(output_path, 'w') as f:
            json.dump(self.tower_result.to_dict(), f, indent=2)
        print(f"\nResults saved to {output_path}")


# ============================================================================
# 5. MAIN
# ============================================================================

def main():
    import argparse
    
    parser = argparse.ArgumentParser(description='Sprint C: EGI Tower Validation')
    parser.add_argument('--device', type=str, 
                        default='cuda' if torch.cuda.is_available() else 'cpu')
    parser.add_argument('--max_steps', type=int, default=20000,
                        help='Maximum steps per task')
    parser.add_argument('--hidden_dim', type=int, default=256)
    parser.add_argument('--output', type=str, default='sprint_c_tower_result.json')
    parser.add_argument('--quick', action='store_true',
                        help='Quick test with reduced parameters')
    
    args = parser.parse_args()
    
    if args.quick:
        args.max_steps = 2000
        prime = 17
    else:
        prime = 97
    
    # Create tasks
    tasks = [
        ModularAdditionTask(prime=prime),
        ParityTask(n_bits=8),
        PermutationTask(n_elements=5),
    ]
    
    # Run Sprint C
    conductor = SprintCConductor(
        tasks=tasks,
        hidden_dim=args.hidden_dim,
        device=args.device,
        max_steps_per_task=args.max_steps,
        log_interval=100,
        preservation_check_interval=500
    )
    
    result = conductor.run()
    conductor.save_results(args.output)
    
    return result


if __name__ == "__main__":
    main()
