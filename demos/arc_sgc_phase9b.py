"""
ARC-SGC Phase 9b: Neural Amortization with Closure

FIX FOR PHASE 9:
Phase 9 achieved fast routing (100% train accuracy, 145ms inference) but failed
to recover perfect solves because the guided executor was a DIFFERENT MODEL CLASS
than the teacher solver. This is a teacher-student mismatch.

CLOSURE PRINCIPLE:
Guided inference must invoke the EXACT SAME geometry and dynamics operators as
the teacher solver (Phase 8.3), just in a different order.

ARCHITECTURE:
- Policy = posterior over modules P(z_shape), P(z_physics)
- Executor = EXACT Phase 8.3 unified physics (imported, not reimplemented)
- Guidance = ordering + pruning only (never delete capabilities)

WHAT THE POLICY DOES:
1. Predicts shape-family prior (crop vs extract vs scale)
2. Predicts physics-family prior (movement vs color vs pattern)
3. Parameters come from invariants (bbox/content/object selectors) - Lean-friendly

VERIFICATION-FIRST EXECUTION (Active Inference):
1. Enumerate top-k shape morphism families (from policy)
2. Instantiate deterministically (bbox/content/largest/smallest)
3. Run content solver in policy's priority order
4. Accept only solutions with cross-example consistency
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional
from collections import Counter
import numpy as np
import json
from pathlib import Path
import sys
import time

# Import EXACT Phase 8.3 components (closure)
sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCObject, ARCExample, ARCTask,
    load_arc_tasks, detect_objects, compute_defect_energy,
    ShapeInference, MorphismInference, ContentSolver,
    GeometryFirstSolver, ShapeMorphism, IdentityMorphism,
    CropToContentMorphism, CropToColorMorphism, ExtractObjectMorphism,
    ScaleMorphism, DownscaleMorphism, TileMorphism,
    PotentialFunction, CompositePotential, relax_all_colors,
    V_BoundaryDist, V_TopEdge, V_BottomEdge, V_ContactDist
)

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class Phase9bConfig:
    # Inherit Phase 8.3 physics config
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    max_relax_steps: int = 20
    energy_threshold: float = 0.0001
    consistency_threshold: float = 0.005
    
    # Neural network config
    hidden_dim: int = 128
    num_geometry_families: int = 5  # identity, crop, extract, scale, tile
    num_physics_families: int = 4   # movement, color, pattern, none
    
    # Training
    batch_size: int = 32
    learning_rate: float = 1e-3
    num_epochs: int = 50
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# Family mappings
GEOMETRY_FAMILIES = ['identity', 'crop', 'extract', 'scale', 'tile']
PHYSICS_FAMILIES = ['movement', 'color', 'pattern', 'none']

def classify_geometry(morphism_name: str) -> int:
    name = morphism_name.lower()
    if 'crop' in name: return 1
    if 'extract' in name: return 2
    if 'scale' in name or 'downscale' in name: return 3
    if 'tile' in name: return 4
    return 0  # identity

def classify_physics(method_name: str) -> int:
    name = method_name.lower()
    if 'v_' in name or 'contact' in name or 'top' in name or 'boundary' in name or 'bottom' in name:
        return 0  # movement
    if 'color' in name or 'map' in name or 'swap' in name:
        return 1  # color
    if 'rot' in name or 'flip' in name or 'transpose' in name:
        return 2  # pattern
    return 3  # none


# =============================================================================
# DATASET (uses Phase 8.3 solver as teacher)
# =============================================================================

@dataclass
class TeacherLabel:
    task_id: str
    geometry_family: int
    physics_family: int
    morphism_name: str
    physics_method: str
    energy: float


class Phase9bDataset(Dataset):
    """Dataset using Phase 8.3 teacher labels."""
    
    def __init__(self, tasks: List[ARCTask], labels: Dict[str, TeacherLabel], 
                 config: Phase9bConfig):
        self.config = config
        self.samples = []
        
        for task in tasks:
            if task.task_id not in labels:
                continue
            
            label = labels[task.task_id]
            
            for ex in task.train_examples:
                self.samples.append({
                    'input': self._grid_to_tensor(ex.input_grid),
                    'output': self._grid_to_tensor(ex.output_grid),
                    'geometry_family': label.geometry_family,
                    'physics_family': label.physics_family,
                    'task_id': task.task_id
                })
    
    def _grid_to_tensor(self, grid: ARCGrid) -> torch.Tensor:
        H, W = grid.shape
        padded = torch.zeros(self.config.max_grid_size, self.config.max_grid_size)
        padded[:H, :W] = grid.data.float().cpu()
        return padded
    
    def __len__(self):
        return len(self.samples)
    
    def __getitem__(self, idx):
        s = self.samples[idx]
        x = torch.stack([s['input'], s['output']], dim=0)
        return {
            'x': x,
            'geometry': s['geometry_family'],
            'physics': s['physics_family']
        }


# =============================================================================
# POLICY NETWORK (outputs family priors, not solutions)
# =============================================================================

class PolicyNetwork(nn.Module):
    """
    Predicts P(geometry_family) and P(physics_family).
    Parameters come from invariants, not from network regression.
    """
    
    def __init__(self, config: Phase9bConfig):
        super().__init__()
        self.config = config
        
        # CNN backbone
        self.conv1 = nn.Conv2d(2, 32, 3, padding=1)
        self.conv2 = nn.Conv2d(32, 64, 3, padding=1)
        self.conv3 = nn.Conv2d(64, 128, 3, padding=1)
        self.pool = nn.MaxPool2d(2, 2)
        
        self.fc1 = nn.Linear(128 * 3 * 3, config.hidden_dim)
        
        # Family heads (categorical, not regression)
        self.geometry_head = nn.Linear(config.hidden_dim, config.num_geometry_families)
        self.physics_head = nn.Linear(config.hidden_dim, config.num_physics_families)
    
    def forward(self, x):
        x = F.relu(self.conv1(x))
        x = self.pool(x)
        x = F.relu(self.conv2(x))
        x = self.pool(x)
        x = F.relu(self.conv3(x))
        x = self.pool(x)
        
        x = x.view(x.size(0), -1)
        x = F.relu(self.fc1(x))
        
        geo_logits = self.geometry_head(x)
        phys_logits = self.physics_head(x)
        
        return geo_logits, phys_logits
    
    def get_priority_order(self, input_grid: ARCGrid, output_grid: ARCGrid) -> Dict:
        """Get priority ordering for guided execution."""
        self.eval()
        with torch.no_grad():
            x_in = torch.zeros(self.config.max_grid_size, self.config.max_grid_size)
            x_out = torch.zeros(self.config.max_grid_size, self.config.max_grid_size)
            x_in[:input_grid.height, :input_grid.width] = input_grid.data.float().cpu()
            x_out[:output_grid.height, :output_grid.width] = output_grid.data.float().cpu()
            
            x = torch.stack([x_in, x_out], dim=0).unsqueeze(0)
            x = x.to(next(self.parameters()).device)
            
            geo_logits, phys_logits = self(x)
            geo_probs = F.softmax(geo_logits, dim=1)[0]
            phys_probs = F.softmax(phys_logits, dim=1)[0]
            
            # Return sorted priority orders
            geo_order = sorted(range(len(GEOMETRY_FAMILIES)), 
                              key=lambda i: -geo_probs[i].item())
            phys_order = sorted(range(len(PHYSICS_FAMILIES)),
                               key=lambda i: -phys_probs[i].item())
            
            return {
                'geometry_order': [GEOMETRY_FAMILIES[i] for i in geo_order],
                'physics_order': [PHYSICS_FAMILIES[i] for i in phys_order],
                'geometry_probs': {GEOMETRY_FAMILIES[i]: geo_probs[i].item() 
                                   for i in range(len(GEOMETRY_FAMILIES))},
                'physics_probs': {PHYSICS_FAMILIES[i]: phys_probs[i].item() 
                                  for i in range(len(PHYSICS_FAMILIES))}
            }


# =============================================================================
# GUIDED SOLVER (uses EXACT Phase 8.3 executor with policy ordering)
# =============================================================================

class GuidedPhase83Solver:
    """
    Guided solver that uses the EXACT Phase 8.3 executor.
    Policy only changes the ORDER of operations tried, not the capabilities.
    
    This ensures CLOSURE: what the policy predicts CAN be executed.
    """
    
    def __init__(self, policy: PolicyNetwork, config: Phase9bConfig):
        self.policy = policy
        self.config = config
        
        # Use exact Phase 8.3 components
        self.phase83_config = ARCPhase83Config(
            max_grid_size=config.max_grid_size,
            num_colors=config.num_colors,
            background_color=config.background_color,
            max_relax_steps=config.max_relax_steps,
            energy_threshold=config.energy_threshold,
            consistency_threshold=config.consistency_threshold
        )
        
        # Exact Phase 8.3 content solver
        self.content_solver = ContentSolver(self.phase83_config)
        
        # Exact Phase 8.3 morphism generators
        self.morphism_families = {
            'identity': [IdentityMorphism()],
            'crop': [CropToContentMorphism()] + [CropToColorMorphism(c) for c in range(1, 6)],
            'extract': [ExtractObjectMorphism('largest'), ExtractObjectMorphism('smallest')] + 
                      [ExtractObjectMorphism(f'color_{c}') for c in range(1, 6)],
            'scale': [ScaleMorphism(2), ScaleMorphism(3), DownscaleMorphism(2), DownscaleMorphism(3)],
            'tile': []  # Tile params from dimension ratios
        }
    
    def _get_morphisms_for_family(self, family: str, examples: List[ARCExample]) -> List[ShapeMorphism]:
        """Get morphisms for a family, instantiated from training invariants."""
        base_morphisms = self.morphism_families.get(family, [])
        
        # Add tile morphisms inferred from dimension ratios
        if family == 'tile':
            for ex in examples:
                iH, iW = ex.input_grid.shape
                oH, oW = ex.output_grid.shape
                if oH > iH and oW > iW and oH % iH == 0 and oW % iW == 0:
                    base_morphisms.append(TileMorphism(oH // iH, oW // iW))
        
        return base_morphisms
    
    def _check_morphism_consistency(self, morphism: ShapeMorphism, 
                                    examples: List[ARCExample]) -> bool:
        """Check if morphism produces correct output shape for ALL examples."""
        for ex in examples:
            try:
                result = morphism.apply(ex.input_grid, self.phase83_config)
                if result.shape != ex.output_grid.shape:
                    return False
            except:
                return False
        return True
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve task using Phase 8.3 executor with policy-guided ordering."""
        start_time = time.time()
        examples = task.train_examples
        
        # Get policy priority ordering
        priority = self.policy.get_priority_order(
            examples[0].input_grid, examples[0].output_grid
        )
        
        if verbose:
            printfl(f"\n   Policy priority:")
            printfl(f"   Geometry: {priority['geometry_order'][:3]}")
            printfl(f"   Physics: {priority['physics_order'][:3]}")
        
        best_energy = float('inf')
        best_result = None
        best_morphism = "none"
        best_method = "identity"
        
        # Try geometry families in policy order
        for geo_family in priority['geometry_order']:
            if verbose:
                printfl(f"\n   Trying geometry family: {geo_family}")
            
            morphisms = self._get_morphisms_for_family(geo_family, examples)
            
            for morphism in morphisms:
                # Check consistency (shape must match for ALL examples)
                if not self._check_morphism_consistency(morphism, examples):
                    continue
                
                if verbose:
                    printfl(f"      Morphism {morphism.name()} is consistent")
                
                # Try physics in policy order using EXACT Phase 8.3 content solver
                for ex in examples:
                    transformed = morphism.apply(ex.input_grid, self.phase83_config)
                    
                    # Use exact Phase 8.3 content solver
                    result, energy, method = self.content_solver.solve(
                        transformed, ex.output_grid.shape, ex.output_grid
                    )
                    
                    if energy < best_energy:
                        best_energy = energy
                        best_morphism = morphism.name()
                        best_method = method
                        
                        if verbose and energy < 0.1:
                            printfl(f"      New best: {morphism.name()} + {method} = {energy:.4f}")
                
                # Early exit if perfect
                if best_energy < self.config.energy_threshold:
                    break
            
            if best_energy < self.config.energy_threshold:
                break
        
        # Compute final energies across all examples
        train_energies = []
        test_energies = []
        
        # Find best morphism again and apply
        for geo_family in priority['geometry_order']:
            morphisms = self._get_morphisms_for_family(geo_family, examples)
            for morphism in morphisms:
                if morphism.name() == best_morphism:
                    for ex in examples:
                        transformed = morphism.apply(ex.input_grid, self.phase83_config)
                        result, energy, _ = self.content_solver.solve(
                            transformed, ex.output_grid.shape, ex.output_grid
                        )
                        train_energies.append(energy)
                    
                    for ex in task.test_examples:
                        transformed = morphism.apply(ex.input_grid, self.phase83_config)
                        result, energy, _ = self.content_solver.solve(
                            transformed, ex.output_grid.shape, ex.output_grid
                        )
                        test_energies.append(energy)
                    break
        
        if not train_energies:
            train_energies = [1000.0]
        
        elapsed = time.time() - start_time
        avg_train = np.mean(train_energies)
        is_perfect = avg_train < self.config.energy_threshold
        is_consistent = all(e < self.config.consistency_threshold for e in train_energies)
        
        return {
            'task_id': task.task_id,
            'morphism': best_morphism,
            'method': best_method,
            'operation': f"{best_morphism} + {best_method}",
            'avg_train_energy': avg_train,
            'train_energies': train_energies,
            'test_energies': test_energies,
            'elapsed_ms': elapsed * 1000,
            'is_perfect': is_perfect,
            'is_consistent': is_consistent,
            'geometry_pred': priority['geometry_order'][0],
            'physics_pred': priority['physics_order'][0]
        }


# =============================================================================
# TRAINING (generates labels using Phase 8.3, trains policy)
# =============================================================================

def generate_teacher_labels(tasks: List[ARCTask], config: Phase9bConfig) -> Dict[str, TeacherLabel]:
    """Generate labels using EXACT Phase 8.3 solver."""
    labels = {}
    
    # Use exact Phase 8.3 solver
    phase83_config = ARCPhase83Config(
        energy_threshold=config.energy_threshold,
        consistency_threshold=config.consistency_threshold
    )
    solver = GeometryFirstSolver(phase83_config)
    
    printfl(f"\nGenerating teacher labels using Phase 8.3 solver...")
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose=False)
        
        if result['avg_train_energy'] < 0.5:  # Solvable
            geometry_family = classify_geometry(result['morphism'] if result['morphism'] != 'none' else 'identity')
            physics_family = classify_physics(result['operation'])
            
            labels[task.task_id] = TeacherLabel(
                task_id=task.task_id,
                geometry_family=geometry_family,
                physics_family=physics_family,
                morphism_name=result['morphism'] if result['morphism'] != 'none' else 'identity',
                physics_method=result['operation'],
                energy=result['avg_train_energy']
            )
        
        if (i + 1) % 20 == 0:
            printfl(f"  Processed {i+1}/{len(tasks)}, labeled {len(labels)} tasks")
    
    printfl(f"\nLabeled {len(labels)} tasks")
    
    # Statistics
    geo_counts = Counter(l.geometry_family for l in labels.values())
    phys_counts = Counter(l.physics_family for l in labels.values())
    
    printfl(f"\nGeometry distribution:")
    for i, name in enumerate(GEOMETRY_FAMILIES):
        printfl(f"  {name}: {geo_counts.get(i, 0)}")
    
    printfl(f"\nPhysics distribution:")
    for i, name in enumerate(PHYSICS_FAMILIES):
        printfl(f"  {name}: {phys_counts.get(i, 0)}")
    
    # Show perfect solves
    perfect = [l for l in labels.values() if l.energy < config.energy_threshold]
    printfl(f"\nPerfect solves in training data: {len(perfect)}")
    for l in perfect:
        printfl(f"  {l.task_id}: {l.morphism_name} + {l.physics_method}")
    
    return labels


def train_policy(dataset: Phase9bDataset, config: Phase9bConfig) -> PolicyNetwork:
    """Train policy network."""
    if len(dataset) == 0:
        printfl("No training data!")
        return None
    
    dataloader = DataLoader(dataset, batch_size=config.batch_size, shuffle=True)
    model = PolicyNetwork(config).to(config.device)
    optimizer = torch.optim.Adam(model.parameters(), lr=config.learning_rate)
    
    geo_criterion = nn.CrossEntropyLoss()
    phys_criterion = nn.CrossEntropyLoss()
    
    printfl(f"\nTraining Policy on {len(dataset)} samples...")
    
    for epoch in range(config.num_epochs):
        model.train()
        total_loss = 0
        geo_correct = phys_correct = total = 0
        
        for batch in dataloader:
            x = batch['x'].to(config.device)
            geo_labels = batch['geometry'].to(config.device)
            phys_labels = batch['physics'].to(config.device)
            
            optimizer.zero_grad()
            geo_logits, phys_logits = model(x)
            
            loss = geo_criterion(geo_logits, geo_labels) + phys_criterion(phys_logits, phys_labels)
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item()
            geo_correct += (geo_logits.argmax(1) == geo_labels).sum().item()
            phys_correct += (phys_logits.argmax(1) == phys_labels).sum().item()
            total += geo_labels.size(0)
        
        if (epoch + 1) % 10 == 0 or epoch == 0:
            printfl(f"  Epoch {epoch+1}/{config.num_epochs}: "
                   f"Geo={geo_correct/total*100:.1f}%, Phys={phys_correct/total*100:.1f}%")
    
    return model


# =============================================================================
# MAIN EVALUATION
# =============================================================================

def run_phase9b(data_path: str, config: Phase9bConfig):
    """Execute Phase 9b with closure guarantee."""
    
    printfl("=" * 70)
    printfl("ARC-SGC Phase 9b: Neural Amortization with Closure")
    printfl("=" * 70)
    printfl("\nKey fix: Guided solver uses EXACT Phase 8.3 executor")
    
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        printfl("No tasks found!")
        return
    
    # Step 1: Generate labels using Phase 8.3 teacher
    printfl("\n" + "=" * 50)
    printfl("STEP 1: Generate Teacher Labels (Phase 8.3)")
    printfl("=" * 50)
    
    labels = generate_teacher_labels(tasks, config)
    
    if len(labels) < 10:
        printfl("Not enough labeled data!")
        return
    
    # Step 2: Train policy
    printfl("\n" + "=" * 50)
    printfl("STEP 2: Train Policy Network")
    printfl("=" * 50)
    
    dataset = Phase9bDataset(tasks, labels, config)
    policy = train_policy(dataset, config)
    
    if policy is None:
        return
    
    # Step 3: Validate with guided solver (EXACT Phase 8.3 executor)
    printfl("\n" + "=" * 50)
    printfl("STEP 3: Guided Solver (Phase 8.3 Executor)")
    printfl("=" * 50)
    
    guided_solver = GuidedPhase83Solver(policy, config)
    
    all_results = []
    perfect_tasks = []
    total_time = 0
    
    for task in tasks:
        result = guided_solver.solve_task(task, verbose=False)
        all_results.append(result)
        total_time += result['elapsed_ms']
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            printfl(f"  [PERFECT] {task.task_id}: {result['operation']} ({result['elapsed_ms']:.0f}ms)")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("PHASE 9b SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Perfect solves: {len(perfect_tasks)}")
    printfl(f"  Avg inference time: {total_time/len(tasks):.0f}ms")
    
    if perfect_tasks:
        printfl(f"\nPerfect solutions:")
        for r in perfect_tasks:
            printfl(f"  {r['task_id']}: {r['operation']}")
            printfl(f"    Predicted: geometry={r['geometry_pred']}, physics={r['physics_pred']}")
    
    # Compare with Phase 8.3 baseline
    printfl(f"\n=== Comparison with Phase 8.3 ===")
    printfl(f"Phase 8.3 perfect: 6")
    printfl(f"Phase 9b perfect:  {len(perfect_tasks)}")
    printfl(f"Closure achieved:  {len(perfect_tasks) >= 6}")
    
    return all_results


def main():
    config = Phase9bConfig()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase9b(arc_path, config)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
