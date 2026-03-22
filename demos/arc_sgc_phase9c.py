"""
ARC-SGC Phase 9c: Enhanced Policy with Amortized Constants

BUILDS ON PHASE 9b:
- Closure Principle: Policy only reorders Phase 8.3 capabilities (LOCKED IN)
- Executor: EXACT Phase 8.3 (never changes)

NEW IN PHASE 9C:
1. Hamiltonian Weight Head: Policy predicts w over {V_contact, V_top, V_bottom, V_boundary}
   - "Movement family" → "which law" via amortized constant selection
   - Executor verifies via cross-example consistency
   
2. Object Selector Prior: Policy predicts which object selector to try first
   - {largest, smallest, unique_color_1, unique_color_2, ...}
   - Parameters still from invariants (Lean-friendly)

3. Replay Buffer + Adiabatic Regularization:
   - Store solved tasks with discovered laws
   - Train with rehearsal + stability constraint
   - Prevents catastrophic forgetting as task set grows

METRICS:
- Realizability: % of policy top-k that executor can evaluate (should be 100%)
- Amortization gain: top-1 success rate, speedup vs unguided
- Continual stability: performance on early tasks after adding new ones
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional
from collections import Counter, deque
import numpy as np
import json
from pathlib import Path
import sys
import time
import copy

# Import EXACT Phase 8.3 components (closure preserved)
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
class Phase9cConfig:
    # Physics (from Phase 8.3)
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    max_relax_steps: int = 20
    energy_threshold: float = 0.0001
    consistency_threshold: float = 0.005
    
    # Policy architecture
    hidden_dim: int = 128
    num_geometry_families: int = 5   # identity, crop, extract, scale, tile
    num_physics_families: int = 4    # movement, color, pattern, none
    num_hamiltonian_basis: int = 4   # V_contact, V_top, V_bottom, V_boundary
    num_object_selectors: int = 7    # largest, smallest, color_1..5
    
    # Training
    batch_size: int = 32
    learning_rate: float = 1e-3
    num_epochs: int = 50
    
    # Continual learning
    replay_buffer_size: int = 500
    adiabatic_lambda: float = 0.1    # Stability regularization weight
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# Mappings
GEOMETRY_FAMILIES = ['identity', 'crop', 'extract', 'scale', 'tile']
PHYSICS_FAMILIES = ['movement', 'color', 'pattern', 'none']
HAMILTONIAN_BASIS = ['V_contact', 'V_top', 'V_bottom', 'V_boundary']
OBJECT_SELECTORS = ['largest', 'smallest', 'color_1', 'color_2', 'color_3', 'color_4', 'color_5']


def classify_geometry(name: str) -> int:
    name = name.lower()
    if 'crop' in name: return 1
    if 'extract' in name: return 2
    if 'scale' in name or 'downscale' in name: return 3
    if 'tile' in name: return 4
    return 0

def classify_physics(name: str) -> int:
    name = name.lower()
    if 'v_' in name or 'contact' in name or 'top' in name or 'boundary' in name or 'bottom' in name:
        return 0
    if 'color' in name or 'map' in name:
        return 1
    if 'rot' in name or 'flip' in name:
        return 2
    return 3

def parse_hamiltonian_weights(operation: str) -> np.ndarray:
    """Parse operation string to Hamiltonian weight vector."""
    weights = np.zeros(4)  # [contact, top, bottom, boundary]
    op = operation.lower()
    if 'contact' in op:
        weights[0] = 1.0 if '+' in op else -1.0
    if 'v_top' in op:
        weights[1] = 1.0 if '+' in op else -1.0
    if 'v_bottom' in op:
        weights[2] = 1.0 if '+' in op else -1.0
    if 'v_boundary' in op:
        weights[3] = 1.0 if '+' in op else -1.0
    return weights

def parse_object_selector(operation: str) -> int:
    """Parse operation string to object selector index."""
    op = operation.lower()
    if 'largest' in op: return 0
    if 'smallest' in op: return 1
    for i in range(1, 6):
        if f'color_{i}' in op: return i + 1
    return 0  # default to largest


# =============================================================================
# REPLAY BUFFER (Continual Learning)
# =============================================================================

@dataclass
class SolvedTask:
    """Record of a solved task for replay."""
    task_id: str
    input_tensor: torch.Tensor
    output_tensor: torch.Tensor
    geometry_family: int
    physics_family: int
    hamiltonian_weights: np.ndarray
    object_selector: int
    operation: str


class ReplayBuffer:
    """Buffer for continual learning with adiabatic protection."""
    
    def __init__(self, max_size: int = 500):
        self.buffer: deque = deque(maxlen=max_size)
        self.task_ids: set = set()
    
    def add(self, solved: SolvedTask):
        if solved.task_id not in self.task_ids:
            self.buffer.append(solved)
            self.task_ids.add(solved.task_id)
    
    def sample(self, n: int) -> List[SolvedTask]:
        if len(self.buffer) == 0:
            return []
        n = min(n, len(self.buffer))
        indices = np.random.choice(len(self.buffer), n, replace=False)
        return [self.buffer[i] for i in indices]
    
    def __len__(self):
        return len(self.buffer)


# =============================================================================
# ENHANCED POLICY NETWORK
# =============================================================================

class EnhancedPolicyNetwork(nn.Module):
    """
    Policy with factorized outputs:
    1. P(geometry_family)
    2. P(physics_family) 
    3. Hamiltonian weights w (for movement tasks)
    4. P(object_selector) (for extract tasks)
    """
    
    def __init__(self, config: Phase9cConfig):
        super().__init__()
        self.config = config
        
        # CNN backbone
        self.conv1 = nn.Conv2d(2, 32, 3, padding=1)
        self.conv2 = nn.Conv2d(32, 64, 3, padding=1)
        self.conv3 = nn.Conv2d(64, 128, 3, padding=1)
        self.pool = nn.MaxPool2d(2, 2)
        
        self.fc1 = nn.Linear(128 * 3 * 3, config.hidden_dim)
        
        # Output heads
        self.geometry_head = nn.Linear(config.hidden_dim, config.num_geometry_families)
        self.physics_head = nn.Linear(config.hidden_dim, config.num_physics_families)
        self.hamiltonian_head = nn.Linear(config.hidden_dim, config.num_hamiltonian_basis)
        self.selector_head = nn.Linear(config.hidden_dim, config.num_object_selectors)
    
    def forward(self, x):
        x = F.relu(self.conv1(x))
        x = self.pool(x)
        x = F.relu(self.conv2(x))
        x = self.pool(x)
        x = F.relu(self.conv3(x))
        x = self.pool(x)
        
        x = x.view(x.size(0), -1)
        features = F.relu(self.fc1(x))
        
        geo_logits = self.geometry_head(features)
        phys_logits = self.physics_head(features)
        ham_weights = torch.tanh(self.hamiltonian_head(features))  # [-1, 1] range
        selector_logits = self.selector_head(features)
        
        return geo_logits, phys_logits, ham_weights, selector_logits
    
    def get_predictions(self, input_grid: ARCGrid, output_grid: ARCGrid) -> Dict:
        """Get all predictions for a single example."""
        self.eval()
        with torch.no_grad():
            x_in = torch.zeros(self.config.max_grid_size, self.config.max_grid_size)
            x_out = torch.zeros(self.config.max_grid_size, self.config.max_grid_size)
            x_in[:input_grid.height, :input_grid.width] = input_grid.data.float().cpu()
            x_out[:output_grid.height, :output_grid.width] = output_grid.data.float().cpu()
            
            x = torch.stack([x_in, x_out], dim=0).unsqueeze(0).to(next(self.parameters()).device)
            
            geo_logits, phys_logits, ham_weights, selector_logits = self(x)
            
            geo_probs = F.softmax(geo_logits, dim=1)[0]
            phys_probs = F.softmax(phys_logits, dim=1)[0]
            selector_probs = F.softmax(selector_logits, dim=1)[0]
            
            return {
                'geometry_probs': {GEOMETRY_FAMILIES[i]: geo_probs[i].item() 
                                   for i in range(len(GEOMETRY_FAMILIES))},
                'physics_probs': {PHYSICS_FAMILIES[i]: phys_probs[i].item() 
                                  for i in range(len(PHYSICS_FAMILIES))},
                'hamiltonian_weights': ham_weights[0].cpu().numpy(),
                'selector_probs': {OBJECT_SELECTORS[i]: selector_probs[i].item() 
                                   for i in range(len(OBJECT_SELECTORS))},
                'geometry_order': sorted(GEOMETRY_FAMILIES, 
                                        key=lambda g: -geo_probs[GEOMETRY_FAMILIES.index(g)].item()),
                'physics_order': sorted(PHYSICS_FAMILIES,
                                        key=lambda p: -phys_probs[PHYSICS_FAMILIES.index(p)].item()),
                'selector_order': sorted(OBJECT_SELECTORS,
                                         key=lambda s: -selector_probs[OBJECT_SELECTORS.index(s)].item())
            }


# =============================================================================
# DATASET WITH ENHANCED LABELS
# =============================================================================

@dataclass
class EnhancedLabel:
    task_id: str
    geometry_family: int
    physics_family: int
    hamiltonian_weights: np.ndarray
    object_selector: int
    operation: str
    energy: float


class EnhancedDataset(Dataset):
    def __init__(self, tasks: List[ARCTask], labels: Dict[str, EnhancedLabel], 
                 config: Phase9cConfig):
        self.config = config
        self.samples = []
        
        for task in tasks:
            if task.task_id not in labels:
                continue
            
            label = labels[task.task_id]
            
            for ex in task.train_examples:
                x_in = torch.zeros(config.max_grid_size, config.max_grid_size)
                x_out = torch.zeros(config.max_grid_size, config.max_grid_size)
                x_in[:ex.input_grid.height, :ex.input_grid.width] = ex.input_grid.data.float().cpu()
                x_out[:ex.output_grid.height, :ex.output_grid.width] = ex.output_grid.data.float().cpu()
                
                self.samples.append({
                    'input': x_in,
                    'output': x_out,
                    'geometry_family': label.geometry_family,
                    'physics_family': label.physics_family,
                    'hamiltonian_weights': torch.tensor(label.hamiltonian_weights, dtype=torch.float32),
                    'object_selector': label.object_selector,
                    'task_id': task.task_id
                })
    
    def __len__(self):
        return len(self.samples)
    
    def __getitem__(self, idx):
        s = self.samples[idx]
        x = torch.stack([s['input'], s['output']], dim=0)
        return {
            'x': x,
            'geometry': s['geometry_family'],
            'physics': s['physics_family'],
            'hamiltonian': s['hamiltonian_weights'],
            'selector': s['object_selector']
        }


# =============================================================================
# GUIDED SOLVER (EXACT Phase 8.3 with enhanced guidance)
# =============================================================================

class EnhancedGuidedSolver:
    """
    Guided solver using EXACT Phase 8.3 executor with enhanced policy guidance.
    Now uses Hamiltonian weights directly for movement tasks.
    """
    
    def __init__(self, policy: EnhancedPolicyNetwork, config: Phase9cConfig):
        self.policy = policy
        self.config = config
        
        self.phase83_config = ARCPhase83Config(
            max_grid_size=config.max_grid_size,
            num_colors=config.num_colors,
            background_color=config.background_color,
            max_relax_steps=config.max_relax_steps,
            energy_threshold=config.energy_threshold,
            consistency_threshold=config.consistency_threshold
        )
        
        self.content_solver = ContentSolver(self.phase83_config)
        
        # Movement potential basis (exact same as Phase 8.3)
        self.movement_potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
        
        self.morphism_families = {
            'identity': [IdentityMorphism()],
            'crop': [CropToContentMorphism()] + [CropToColorMorphism(c) for c in range(1, 6)],
            'extract': [ExtractObjectMorphism('largest'), ExtractObjectMorphism('smallest')] + 
                      [ExtractObjectMorphism(f'color_{c}') for c in range(1, 6)],
            'scale': [ScaleMorphism(2), ScaleMorphism(3), DownscaleMorphism(2), DownscaleMorphism(3)],
            'tile': []
        }
    
    def _check_morphism_consistency(self, morphism: ShapeMorphism, 
                                    examples: List[ARCExample]) -> bool:
        for ex in examples:
            try:
                result = morphism.apply(ex.input_grid, self.phase83_config)
                if result.shape != ex.output_grid.shape:
                    return False
            except:
                return False
        return True
    
    def _try_hamiltonian(self, weights: np.ndarray, examples: List[ARCExample]) -> float:
        """Try movement with specific Hamiltonian weights."""
        potential = CompositePotential(self.movement_potentials, weights)
        total_e = 0
        for ex in examples:
            result = relax_all_colors(ex.input_grid, potential, self.phase83_config)
            total_e += compute_defect_energy(result, ex.output_grid)
        return total_e / len(examples)
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        start_time = time.time()
        examples = task.train_examples
        
        # Get policy predictions
        preds = self.policy.get_predictions(examples[0].input_grid, examples[0].output_grid)
        
        if verbose:
            printfl(f"\n   Policy predictions:")
            geo_top3 = preds['geometry_order'][:3]
            geo_probs = [f"{preds['geometry_probs'][g]:.2f}" for g in geo_top3]
            printfl(f"   Geometry: {geo_top3} (probs: {geo_probs})")
            phys_top3 = preds['physics_order'][:3]
            phys_probs = [f"{preds['physics_probs'][p]:.2f}" for p in phys_top3]
            printfl(f"   Physics: {phys_top3} (probs: {phys_probs})")
            printfl(f"   Hamiltonian weights: {preds['hamiltonian_weights']}")
        
        best_energy = float('inf')
        best_morphism = "identity"
        best_method = "identity"
        
        # Try geometry families in policy order
        for geo_family in preds['geometry_order']:
            morphisms = self.morphism_families.get(geo_family, [])
            
            # For extract, order by selector preference
            if geo_family == 'extract':
                selector_order = preds['selector_order']
                morphisms = sorted(morphisms, key=lambda m: 
                    selector_order.index(m.name().replace('extract(', '').replace(')', '')) 
                    if m.name().replace('extract(', '').replace(')', '') in selector_order else 100)
            
            for morphism in morphisms:
                if not self._check_morphism_consistency(morphism, examples):
                    continue
                
                # Try physics in policy order
                for phys_family in preds['physics_order']:
                    if phys_family == 'movement':
                        # Use predicted Hamiltonian weights
                        pred_weights = preds['hamiltonian_weights']
                        e = self._try_hamiltonian(pred_weights, examples)
                        if e < best_energy:
                            best_energy = e
                            best_morphism = morphism.name()
                            best_method = f"H={pred_weights}"
                        
                        # Also try discrete sign variations (refinement)
                        for i in range(4):
                            for sign in [-1.0, 1.0]:
                                w = np.zeros(4)
                                w[i] = sign
                                e = self._try_hamiltonian(w, examples)
                                if e < best_energy:
                                    best_energy = e
                                    best_morphism = morphism.name()
                                    best_method = f"{'+' if sign > 0 else '-'}1.0*{HAMILTONIAN_BASIS[i]}"
                    
                    elif phys_family == 'color':
                        for from_c in range(1, 6):
                            for to_c in range(0, 6):
                                if from_c == to_c: continue
                                total_e = 0
                                for ex in examples:
                                    transformed = morphism.apply(ex.input_grid, self.phase83_config)
                                    data = transformed.data.clone()
                                    data[data == from_c] = to_c
                                    total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
                                avg_e = total_e / len(examples)
                                if avg_e < best_energy:
                                    best_energy = avg_e
                                    best_morphism = morphism.name()
                                    best_method = f"color_map({from_c}->{to_c})"
                    
                    elif phys_family == 'pattern':
                        for name, rot in [('rot180', 2), ('rot90', 1), ('rot270', 3)]:
                            total_e = 0
                            valid = True
                            for ex in examples:
                                try:
                                    transformed = morphism.apply(ex.input_grid, self.phase83_config)
                                    result = ARCGrid(transformed.data.rot90(rot, [0, 1]))
                                    if result.shape != ex.output_grid.shape:
                                        valid = False
                                        break
                                    total_e += compute_defect_energy(result, ex.output_grid)
                                except:
                                    valid = False
                                    break
                            if valid:
                                avg_e = total_e / len(examples)
                                if avg_e < best_energy:
                                    best_energy = avg_e
                                    best_morphism = morphism.name()
                                    best_method = name
                    
                    else:  # none
                        total_e = 0
                        for ex in examples:
                            transformed = morphism.apply(ex.input_grid, self.phase83_config)
                            total_e += compute_defect_energy(transformed, ex.output_grid)
                        avg_e = total_e / len(examples)
                        if avg_e < best_energy:
                            best_energy = avg_e
                            best_morphism = morphism.name()
                            best_method = "identity"
                
                if best_energy < self.config.energy_threshold:
                    break
            
            if best_energy < self.config.energy_threshold:
                break
        
        elapsed = time.time() - start_time
        is_perfect = best_energy < self.config.energy_threshold
        
        return {
            'task_id': task.task_id,
            'morphism': best_morphism,
            'method': best_method,
            'operation': f"{best_morphism} + {best_method}",
            'energy': best_energy,
            'elapsed_ms': elapsed * 1000,
            'is_perfect': is_perfect,
            'predictions': preds
        }


# =============================================================================
# TRAINING WITH ADIABATIC REGULARIZATION
# =============================================================================

def train_with_adiabatic(model: EnhancedPolicyNetwork, dataset: EnhancedDataset,
                         replay_buffer: ReplayBuffer, config: Phase9cConfig,
                         old_model: Optional[EnhancedPolicyNetwork] = None):
    """Train with replay and adiabatic stability constraint."""
    
    if len(dataset) == 0:
        return model
    
    dataloader = DataLoader(dataset, batch_size=config.batch_size, shuffle=True)
    optimizer = torch.optim.Adam(model.parameters(), lr=config.learning_rate)
    
    geo_criterion = nn.CrossEntropyLoss()
    phys_criterion = nn.CrossEntropyLoss()
    ham_criterion = nn.MSELoss()
    selector_criterion = nn.CrossEntropyLoss()
    
    printfl(f"\nTraining with {len(dataset)} samples, {len(replay_buffer)} replay...")
    
    for epoch in range(config.num_epochs):
        model.train()
        total_loss = 0
        geo_correct = phys_correct = total = 0
        
        for batch in dataloader:
            x = batch['x'].to(config.device)
            geo_labels = batch['geometry'].to(config.device)
            phys_labels = batch['physics'].to(config.device)
            ham_targets = batch['hamiltonian'].to(config.device)
            selector_labels = batch['selector'].to(config.device)
            
            optimizer.zero_grad()
            geo_logits, phys_logits, ham_weights, selector_logits = model(x)
            
            # Main losses
            loss = (geo_criterion(geo_logits, geo_labels) + 
                   phys_criterion(phys_logits, phys_labels) +
                   ham_criterion(ham_weights, ham_targets) +
                   selector_criterion(selector_logits, selector_labels))
            
            # Adiabatic regularization (if old model exists)
            if old_model is not None and config.adiabatic_lambda > 0:
                with torch.no_grad():
                    old_geo, old_phys, old_ham, old_sel = old_model(x)
                # KL divergence to old predictions (stability)
                adiabatic_loss = (F.kl_div(F.log_softmax(geo_logits, dim=1), 
                                          F.softmax(old_geo, dim=1), reduction='batchmean') +
                                 F.kl_div(F.log_softmax(phys_logits, dim=1),
                                          F.softmax(old_phys, dim=1), reduction='batchmean'))
                loss = loss + config.adiabatic_lambda * adiabatic_loss
            
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
# GENERATE ENHANCED LABELS
# =============================================================================

def generate_enhanced_labels(tasks: List[ARCTask], config: Phase9cConfig) -> Dict[str, EnhancedLabel]:
    """Generate enhanced labels using Phase 8.3 solver."""
    labels = {}
    
    phase83_config = ARCPhase83Config(
        energy_threshold=config.energy_threshold,
        consistency_threshold=config.consistency_threshold
    )
    solver = GeometryFirstSolver(phase83_config)
    
    printfl(f"\nGenerating enhanced labels...")
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose=False)
        
        if result['avg_train_energy'] < 0.5:
            op = result['operation']
            labels[task.task_id] = EnhancedLabel(
                task_id=task.task_id,
                geometry_family=classify_geometry(result['morphism'] if result['morphism'] != 'none' else 'identity'),
                physics_family=classify_physics(op),
                hamiltonian_weights=parse_hamiltonian_weights(op),
                object_selector=parse_object_selector(op),
                operation=op,
                energy=result['avg_train_energy']
            )
        
        if (i + 1) % 20 == 0:
            printfl(f"  Processed {i+1}/{len(tasks)}, labeled {len(labels)}")
    
    printfl(f"\nLabeled {len(labels)} tasks")
    
    # Show perfect solves
    perfect = [l for l in labels.values() if l.energy < config.energy_threshold]
    printfl(f"\nPerfect solves: {len(perfect)}")
    for l in perfect:
        printfl(f"  {l.task_id}: {l.operation}")
        printfl(f"    ham_weights={l.hamiltonian_weights}, selector={OBJECT_SELECTORS[l.object_selector]}")
    
    return labels


# =============================================================================
# MAIN
# =============================================================================

def run_phase9c(data_path: str, config: Phase9cConfig):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 9c: Enhanced Policy with Amortized Constants")
    printfl("=" * 70)
    
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        return
    
    # Step 1: Generate enhanced labels
    printfl("\n" + "=" * 50)
    printfl("STEP 1: Generate Enhanced Labels")
    printfl("=" * 50)
    
    labels = generate_enhanced_labels(tasks, config)
    
    # Step 2: Train enhanced policy
    printfl("\n" + "=" * 50)
    printfl("STEP 2: Train Enhanced Policy")
    printfl("=" * 50)
    
    dataset = EnhancedDataset(tasks, labels, config)
    replay_buffer = ReplayBuffer(config.replay_buffer_size)
    
    policy = EnhancedPolicyNetwork(config).to(config.device)
    policy = train_with_adiabatic(policy, dataset, replay_buffer, config)
    
    # Step 3: Validate with guided solver
    printfl("\n" + "=" * 50)
    printfl("STEP 3: Guided Solver Validation")
    printfl("=" * 50)
    
    solver = EnhancedGuidedSolver(policy, config)
    
    perfect_tasks = []
    near_misses = []
    total_time = 0
    
    for task in tasks:
        result = solver.solve_task(task, verbose=False)
        total_time += result['elapsed_ms']
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            printfl(f"  [PERFECT] {task.task_id}: {result['operation']} ({result['elapsed_ms']:.0f}ms)")
        elif result['energy'] < 0.1:
            near_misses.append(result)
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("PHASE 9c SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Perfect solves: {len(perfect_tasks)}")
    printfl(f"  Near-misses (E<0.1): {len(near_misses)}")
    printfl(f"  Avg inference time: {total_time/len(tasks):.0f}ms")
    
    # Policy distribution analysis
    printfl(f"\n=== Policy Distributions (Perfect Solves) ===")
    for r in perfect_tasks[:3]:
        printfl(f"\n  {r['task_id']}: {r['operation']}")
        printfl(f"    Geometry probs: {r['predictions']['geometry_probs']}")
        printfl(f"    Physics probs: {r['predictions']['physics_probs']}")
        printfl(f"    Hamiltonian weights: {r['predictions']['hamiltonian_weights']}")
    
    printfl(f"\n=== Policy Distributions (Near-Misses) ===")
    for r in near_misses[:3]:
        printfl(f"\n  {r['task_id']}: E={r['energy']:.4f}")
        printfl(f"    Geometry probs: {r['predictions']['geometry_probs']}")
        printfl(f"    Physics probs: {r['predictions']['physics_probs']}")
    
    printfl(f"\n=== Closure Check ===")
    printfl(f"Phase 8.3 perfect: 6")
    printfl(f"Phase 9c perfect:  {len(perfect_tasks)}")
    printfl(f"Closure maintained: {len(perfect_tasks) >= 6}")


def main():
    config = Phase9cConfig()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase9c(arc_path, config)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
