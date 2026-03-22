"""
ARC-SGC Phase 9: Neural Amortization (The Neural Physicist)

THEORETICAL FOUNDATION:
Phase 8.3 validated H_geometry ⊗ H_content as the correct factorization.
But exhaustive search is O(N_ops × N_shapes) - doesn't scale.

Phase 9 replaces SEARCH with INTUITION via Amortized Inference:
- SGC Theory: Brain minimizes free energy by training a generative model (Policy)
  to predict the posterior distribution of actions.
- Implementation: Train CNN to predict solution CATEGORY instantly.

NEURO-SYMBOLIC AGI:
1. Symbolic Solver (Phase 8.3) generates ground truth labels
2. Neural Network learns to predict hypothesis class
3. Neural Network guides Symbolic Solver's priority queue

ARCHITECTURE:
- Input: (Input Grid, Output Grid) stacked channels
- Output Head 1 (Geometry): Softmax over [Identity, Crop, Extract, Scale, Tile]
- Output Head 2 (Physics): Softmax over [Movement, Color, Pattern, None]
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

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class Phase9Config:
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    
    # Neural network
    hidden_dim: int = 128
    num_geometry_classes: int = 5  # identity, crop, extract, scale, tile
    num_physics_classes: int = 4   # movement, color, pattern, none
    
    # Training
    batch_size: int = 32
    learning_rate: float = 1e-3
    num_epochs: int = 50
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# Geometry and Physics class mappings
GEOMETRY_CLASSES = ['identity', 'crop', 'extract', 'scale', 'tile']
PHYSICS_CLASSES = ['movement', 'color', 'pattern', 'none']

def geometry_to_idx(name: str) -> int:
    name = name.lower()
    if 'crop' in name: return 1
    if 'extract' in name: return 2
    if 'scale' in name or 'downscale' in name: return 3
    if 'tile' in name: return 4
    return 0  # identity

def physics_to_idx(name: str) -> int:
    name = name.lower()
    if 'v_' in name or 'contact' in name or 'top' in name or 'boundary' in name or 'bottom' in name:
        return 0  # movement
    if 'color' in name or 'map' in name or 'swap' in name:
        return 1  # color
    if 'rot' in name or 'flip' in name or 'transpose' in name:
        return 2  # pattern
    return 3  # none (identity)


# =============================================================================
# DATA STRUCTURES (from Phase 8.3)
# =============================================================================

@dataclass
class ARCGrid:
    data: torch.Tensor
    
    @property
    def height(self) -> int: return self.data.shape[0]
    @property
    def width(self) -> int: return self.data.shape[1]
    @property
    def shape(self) -> Tuple[int, int]: return (self.height, self.width)
    
    def to_numpy(self) -> np.ndarray:
        """Convert grid data to numpy array."""
        return self.data.cpu().numpy()
    
    @classmethod
    def from_list(cls, lst: List[List[int]], device: str = 'cpu') -> 'ARCGrid':
        return cls(torch.tensor(lst, dtype=torch.long, device=device))
    
    def to_tensor(self, max_size: int = 30) -> torch.Tensor:
        """Convert to padded tensor suitable for neural network."""
        H, W = self.shape
        padded = torch.zeros(max_size, max_size, dtype=torch.float32)
        padded[:H, :W] = self.data.float()
        return padded


@dataclass
class ARCExample:
    input_grid: ARCGrid
    output_grid: ARCGrid


@dataclass
class ARCTask:
    task_id: str
    train_examples: List[ARCExample]
    test_examples: List[ARCExample]
    
    @classmethod
    def from_json(cls, task_id: str, data: dict, device: str = 'cpu') -> 'ARCTask':
        train = [ARCExample(
            ARCGrid.from_list(ex['input'], device),
            ARCGrid.from_list(ex.get('output', ex['input']), device)
        ) for ex in data['train']]
        test = [ARCExample(
            ARCGrid.from_list(ex['input'], device),
            ARCGrid.from_list(ex.get('output', ex['input']), device)
        ) for ex in data['test']]
        return cls(task_id, train, test)


def load_arc_tasks(path: str, device: str = 'cpu', limit: int = None) -> List[ARCTask]:
    tasks = []
    p = Path(path)
    if not p.exists(): return tasks
    files = sorted(p.glob("*.json"))
    if limit:
        files = files[:limit]
    for f in files:
        try:
            with open(f) as fp:
                tasks.append(ARCTask.from_json(f.stem, json.load(fp), device))
        except: pass
    return tasks


# =============================================================================
# DATASET FOR NEURAL NETWORK
# =============================================================================

@dataclass
class SolverResult:
    """Result from Phase 8.3 solver."""
    task_id: str
    geometry_label: int  # 0=identity, 1=crop, 2=extract, 3=scale, 4=tile
    physics_label: int   # 0=movement, 1=color, 2=pattern, 3=none
    energy: float
    operation: str


class ARCPolicyDataset(Dataset):
    """Dataset for training the policy network."""
    
    def __init__(self, tasks: List[ARCTask], labels: Dict[str, SolverResult], 
                 config: Phase9Config):
        self.config = config
        self.samples = []
        
        for task in tasks:
            if task.task_id not in labels:
                continue
            
            result = labels[task.task_id]
            
            # Create samples from each training example
            for ex in task.train_examples:
                self.samples.append({
                    'input': ex.input_grid.to_tensor(config.max_grid_size),
                    'output': ex.output_grid.to_tensor(config.max_grid_size),
                    'geometry_label': result.geometry_label,
                    'physics_label': result.physics_label,
                    'task_id': task.task_id
                })
    
    def __len__(self):
        return len(self.samples)
    
    def __getitem__(self, idx):
        sample = self.samples[idx]
        # Stack input and output as channels
        x = torch.stack([sample['input'], sample['output']], dim=0)
        return {
            'x': x,
            'geometry': sample['geometry_label'],
            'physics': sample['physics_label']
        }


# =============================================================================
# NEURAL POLICY NETWORK
# =============================================================================

class PolicyNetwork(nn.Module):
    """
    CNN that predicts solution category from (Input, Output) grid pair.
    
    Outputs:
    - P(Geometry): Which shape morphism? [identity, crop, extract, scale, tile]
    - P(Physics): Which content operation? [movement, color, pattern, none]
    """
    
    def __init__(self, config: Phase9Config):
        super().__init__()
        self.config = config
        
        # Convolutional backbone
        self.conv1 = nn.Conv2d(2, 32, 3, padding=1)
        self.conv2 = nn.Conv2d(32, 64, 3, padding=1)
        self.conv3 = nn.Conv2d(64, 128, 3, padding=1)
        self.pool = nn.MaxPool2d(2, 2)
        
        # After 3 pools: 30 -> 15 -> 7 -> 3
        self.fc1 = nn.Linear(128 * 3 * 3, config.hidden_dim)
        
        # Output heads
        self.geometry_head = nn.Linear(config.hidden_dim, config.num_geometry_classes)
        self.physics_head = nn.Linear(config.hidden_dim, config.num_physics_classes)
    
    def forward(self, x):
        # x: (batch, 2, 30, 30)
        x = F.relu(self.conv1(x))
        x = self.pool(x)  # 15x15
        x = F.relu(self.conv2(x))
        x = self.pool(x)  # 7x7
        x = F.relu(self.conv3(x))
        x = self.pool(x)  # 3x3
        
        x = x.view(x.size(0), -1)
        x = F.relu(self.fc1(x))
        
        geometry_logits = self.geometry_head(x)
        physics_logits = self.physics_head(x)
        
        return geometry_logits, physics_logits
    
    def predict(self, input_grid: ARCGrid, output_grid: ARCGrid) -> Dict:
        """Predict geometry and physics categories for a single example."""
        self.eval()
        with torch.no_grad():
            x_in = input_grid.to_tensor(self.config.max_grid_size)
            x_out = output_grid.to_tensor(self.config.max_grid_size)
            x = torch.stack([x_in, x_out], dim=0).unsqueeze(0)
            x = x.to(next(self.parameters()).device)
            
            geo_logits, phys_logits = self(x)
            
            geo_probs = F.softmax(geo_logits, dim=1)[0]
            phys_probs = F.softmax(phys_logits, dim=1)[0]
            
            return {
                'geometry_probs': {GEOMETRY_CLASSES[i]: geo_probs[i].item() 
                                   for i in range(len(GEOMETRY_CLASSES))},
                'physics_probs': {PHYSICS_CLASSES[i]: phys_probs[i].item() 
                                  for i in range(len(PHYSICS_CLASSES))},
                'geometry_pred': GEOMETRY_CLASSES[geo_probs.argmax().item()],
                'physics_pred': PHYSICS_CLASSES[phys_probs.argmax().item()]
            }


# =============================================================================
# TRAINING
# =============================================================================

def train_policy_network(dataset: ARCPolicyDataset, config: Phase9Config) -> PolicyNetwork:
    """Train the policy network on labeled data."""
    
    if len(dataset) == 0:
        printfl("No training data!")
        return None
    
    dataloader = DataLoader(dataset, batch_size=config.batch_size, shuffle=True)
    
    model = PolicyNetwork(config).to(config.device)
    optimizer = torch.optim.Adam(model.parameters(), lr=config.learning_rate)
    
    geo_criterion = nn.CrossEntropyLoss()
    phys_criterion = nn.CrossEntropyLoss()
    
    printfl(f"\nTraining Policy Network on {len(dataset)} samples...")
    printfl(f"Device: {config.device}")
    
    for epoch in range(config.num_epochs):
        model.train()
        total_loss = 0
        geo_correct = 0
        phys_correct = 0
        total = 0
        
        for batch in dataloader:
            x = batch['x'].to(config.device)
            geo_labels = batch['geometry'].to(config.device)
            phys_labels = batch['physics'].to(config.device)
            
            optimizer.zero_grad()
            geo_logits, phys_logits = model(x)
            
            geo_loss = geo_criterion(geo_logits, geo_labels)
            phys_loss = phys_criterion(phys_logits, phys_labels)
            loss = geo_loss + phys_loss
            
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item()
            geo_correct += (geo_logits.argmax(1) == geo_labels).sum().item()
            phys_correct += (phys_logits.argmax(1) == phys_labels).sum().item()
            total += geo_labels.size(0)
        
        if (epoch + 1) % 10 == 0 or epoch == 0:
            geo_acc = geo_correct / total * 100
            phys_acc = phys_correct / total * 100
            printfl(f"  Epoch {epoch+1}/{config.num_epochs}: Loss={total_loss/len(dataloader):.4f}, "
                   f"Geo={geo_acc:.1f}%, Phys={phys_acc:.1f}%")
    
    return model


# =============================================================================
# PHASE 8.3 SOLVER (Simplified for labeling)
# =============================================================================

def run_phase83_solver(task: ARCTask, config: Phase9Config) -> Optional[SolverResult]:
    """
    Run simplified Phase 8.3 solver and return the best solution label.
    This is used to generate training data for the policy network.
    """
    from collections import deque
    
    examples = task.train_examples
    
    # Check shape consistency
    input_shapes = [ex.input_grid.shape for ex in examples]
    output_shapes = [ex.output_grid.shape for ex in examples]
    same_shape = all(i == o for i, o in zip(input_shapes, output_shapes))
    
    best_energy = float('inf')
    best_geometry = 'identity'
    best_physics = 'identity'
    
    def compute_energy(pred, target):
        if pred.shape != target.shape:
            return 1000.0
        # Ensure both on same device (CPU)
        pred_data = pred.data.cpu() if pred.data.is_cuda else pred.data
        target_data = target.data.cpu() if target.data.is_cuda else target.data
        return (pred_data != target_data).float().mean().item()
    
    # Movement potential helper functions
    def detect_objects_local(grid_data):
        """Detect objects in grid (local version)."""
        data = grid_data.cpu().numpy() if grid_data.is_cuda else grid_data.numpy()
        H, W = data.shape
        visited = np.zeros((H, W), dtype=bool)
        objects = []
        
        for r in range(H):
            for c in range(W):
                if visited[r, c]: continue
                color = data[r, c]
                if color == config.background_color:
                    visited[r, c] = True
                    continue
                pixels = []
                queue = deque([(r, c)])
                visited[r, c] = True
                while queue:
                    cr, cc = queue.popleft()
                    pixels.append((cr, cc))
                    for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                        nr, nc = cr + dr, cc + dc
                        if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                            if data[nr, nc] == color:
                                visited[nr, nc] = True
                                queue.append((nr, nc))
                if pixels:
                    objects.append({'color': int(color), 'pixels': pixels, 'mass': len(pixels)})
        return objects
    
    def relax_with_potential(grid, potential_name, max_steps=20):
        """Apply movement potential to relax objects."""
        data = grid.data.clone().cpu()
        H, W = data.shape
        
        for step in range(max_steps):
            # Find objects
            objects = detect_objects_local(data)
            if not objects:
                break
            
            moved_any = False
            for obj in objects:
                # Compute gradient direction based on potential
                rows = [p[0] for p in obj['pixels']]
                cols = [p[1] for p in obj['pixels']]
                r1, c1 = min(rows), min(cols)
                r2, c2 = max(rows) + 1, max(cols) + 1
                cr, cc = (r1 + r2) / 2, (c1 + c2) / 2
                
                dr, dc = 0, 0
                if potential_name == 'V_top':
                    dr = -1 if r1 > 0 else 0
                elif potential_name == 'V_bottom':
                    dr = 1 if r2 < H else 0
                elif potential_name == 'V_contact':
                    # Move toward nearest other object
                    min_dist = float('inf')
                    best_dir = (0, 0)
                    for other in objects:
                        if other['color'] == obj['color'] and other['pixels'] == obj['pixels']:
                            continue
                        orows = [p[0] for p in other['pixels']]
                        ocols = [p[1] for p in other['pixels']]
                        ocr = (min(orows) + max(orows) + 1) / 2
                        occ = (min(ocols) + max(ocols) + 1) / 2
                        dist = ((cr - ocr)**2 + (cc - occ)**2) ** 0.5
                        if dist < min_dist and dist > 1:
                            min_dist = dist
                            # Move toward other object
                            if abs(cr - ocr) > abs(cc - occ):
                                best_dir = (1 if ocr > cr else -1, 0)
                            else:
                                best_dir = (0, 1 if occ > cc else -1)
                    dr, dc = best_dir
                
                if dr == 0 and dc == 0:
                    continue
                
                # Check if move is valid
                can_move = True
                new_pixels = [(r + dr, c + dc) for r, c in obj['pixels']]
                for nr, nc in new_pixels:
                    if not (0 <= nr < H and 0 <= nc < W):
                        can_move = False
                        break
                    if data[nr, nc] != 0 and (nr - dr, nc - dc) not in obj['pixels']:
                        can_move = False
                        break
                
                if can_move:
                    # Move object
                    color = obj['color']
                    for r, c in obj['pixels']:
                        data[r, c] = 0
                    for r, c in obj['pixels']:
                        data[r + dr, c + dc] = color
                    moved_any = True
            
            if not moved_any:
                break
        
        return ARCGrid(data)
    
    # Try identity geometry first
    if same_shape:
        # Test identity
        total_e = sum(compute_energy(ex.input_grid, ex.output_grid) for ex in examples)
        avg_e = total_e / len(examples)
        if avg_e < best_energy:
            best_energy = avg_e
            best_geometry = 'identity'
            best_physics = 'identity'
        
        # Test movement potentials
        for pot_name in ['V_top', 'V_bottom', 'V_contact']:
            total_e = 0
            for ex in examples:
                result = relax_with_potential(ex.input_grid, pot_name)
                total_e += compute_energy(result, ex.output_grid)
            avg_e = total_e / len(examples)
            if avg_e < best_energy:
                best_energy = avg_e
                best_geometry = 'identity'
                best_physics = pot_name
        
        # Test color maps
        for from_c in range(1, 6):
            for to_c in range(0, 6):
                if from_c == to_c: continue
                total_e = 0
                for ex in examples:
                    data = ex.input_grid.data.clone()
                    data[data == from_c] = to_c
                    total_e += compute_energy(ARCGrid(data), ex.output_grid)
                avg_e = total_e / len(examples)
                if avg_e < best_energy:
                    best_energy = avg_e
                    best_geometry = 'identity'
                    best_physics = f'color_map({from_c}->{to_c})'
        
        # Test pattern ops
        for name, rot in [('rot90', 1), ('rot180', 2), ('rot270', 3)]:
            total_e = 0
            valid = True
            for ex in examples:
                try:
                    result = ARCGrid(ex.input_grid.data.rot90(rot, [0, 1]))
                    if result.shape != ex.output_grid.shape:
                        valid = False
                        break
                    total_e += compute_energy(result, ex.output_grid)
                except:
                    valid = False
                    break
            if valid:
                avg_e = total_e / len(examples)
                if avg_e < best_energy:
                    best_energy = avg_e
                    best_geometry = 'identity'
                    best_physics = name
        
        for name, dim in [('flip_h', 1), ('flip_v', 0)]:
            total_e = 0
            for ex in examples:
                result = ARCGrid(ex.input_grid.data.flip(dim))
                total_e += compute_energy(result, ex.output_grid)
            avg_e = total_e / len(examples)
            if avg_e < best_energy:
                best_energy = avg_e
                best_geometry = 'identity'
                best_physics = name
    
    # Try crop/extract morphisms
    def get_content_bbox(grid):
        data = grid.to_numpy() if hasattr(grid, 'to_numpy') else grid.data.cpu().numpy()
        non_bg = np.argwhere(data != config.background_color)
        if len(non_bg) == 0: return None
        r1, c1 = non_bg.min(axis=0)
        r2, c2 = non_bg.max(axis=0)
        return (r1, c1, r2 + 1, c2 + 1)
    
    # Crop to content
    all_match = True
    total_e = 0
    for ex in examples:
        bbox = get_content_bbox(ex.input_grid)
        if bbox is None:
            all_match = False
            break
        r1, c1, r2, c2 = bbox
        cropped = ARCGrid(ex.input_grid.data[r1:r2, c1:c2].clone())
        if cropped.shape != ex.output_grid.shape:
            all_match = False
            break
        total_e += compute_energy(cropped, ex.output_grid)
    
    if all_match:
        avg_e = total_e / len(examples)
        if avg_e < best_energy:
            best_energy = avg_e
            best_geometry = 'crop_to_content'
            best_physics = 'identity'
    
    # Extract largest object
    def detect_objects(grid):
        data = grid.data.cpu().numpy()
        H, W = data.shape
        visited = np.zeros((H, W), dtype=bool)
        objects = []
        
        for r in range(H):
            for c in range(W):
                if visited[r, c]: continue
                color = data[r, c]
                if color == config.background_color:
                    visited[r, c] = True
                    continue
                pixels = []
                queue = deque([(r, c)])
                visited[r, c] = True
                while queue:
                    cr, cc = queue.popleft()
                    pixels.append((cr, cc))
                    for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                        nr, nc = cr + dr, cc + dc
                        if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                            if data[nr, nc] == color:
                                visited[nr, nc] = True
                                queue.append((nr, nc))
                if pixels:
                    objects.append({'color': color, 'pixels': pixels, 'mass': len(pixels)})
        return objects
    
    def extract_object(grid, selector):
        objects = detect_objects(grid)
        if not objects: return None
        if selector == 'largest':
            obj = max(objects, key=lambda o: o['mass'])
        elif selector == 'smallest':
            obj = min(objects, key=lambda o: o['mass'])
        else:
            return None
        
        rows = [p[0] for p in obj['pixels']]
        cols = [p[1] for p in obj['pixels']]
        r1, c1, r2, c2 = min(rows), min(cols), max(rows)+1, max(cols)+1
        H, W = r2 - r1, c2 - c1
        result = torch.zeros(H, W, dtype=torch.long, device='cpu')
        for r, c in obj['pixels']:
            result[r - r1, c - c1] = obj['color']
        return ARCGrid(result)
    
    for selector in ['largest', 'smallest']:
        all_match = True
        total_e = 0
        for ex in examples:
            extracted = extract_object(ex.input_grid, selector)
            if extracted is None or extracted.shape != ex.output_grid.shape:
                all_match = False
                break
            total_e += compute_energy(extracted, ex.output_grid)
        
        if all_match:
            avg_e = total_e / len(examples)
            if avg_e < best_energy:
                best_energy = avg_e
                best_geometry = f'extract({selector})'
                best_physics = 'identity'
    
    # Try scale morphisms
    for k in [2, 3]:
        # Upscale
        all_match = True
        total_e = 0
        for ex in examples:
            scaled = ex.input_grid.data.repeat_interleave(k, dim=0).repeat_interleave(k, dim=1)
            if scaled.shape != ex.output_grid.data.shape:
                all_match = False
                break
            total_e += compute_energy(ARCGrid(scaled), ex.output_grid)
        
        if all_match:
            avg_e = total_e / len(examples)
            if avg_e < best_energy:
                best_energy = avg_e
                best_geometry = f'scale({k}x)'
                best_physics = 'identity'
        
        # Downscale
        all_match = True
        total_e = 0
        for ex in examples:
            data = ex.input_grid.data.cpu().numpy()
            H, W = data.shape
            if H % k != 0 or W % k != 0:
                all_match = False
                break
            newH, newW = H // k, W // k
            result = np.zeros((newH, newW), dtype=data.dtype)
            for r in range(newH):
                for c in range(newW):
                    block = data[r*k:(r+1)*k, c*k:(c+1)*k]
                    values, counts = np.unique(block, return_counts=True)
                    result[r, c] = values[np.argmax(counts)]
            downscaled = ARCGrid(torch.tensor(result, dtype=torch.long))
            if downscaled.shape != ex.output_grid.shape:
                all_match = False
                break
            total_e += compute_energy(downscaled, ex.output_grid)
        
        if all_match:
            avg_e = total_e / len(examples)
            if avg_e < best_energy:
                best_energy = avg_e
                best_geometry = f'downscale({k}x)'
                best_physics = 'identity'
    
    # Determine labels
    geometry_label = geometry_to_idx(best_geometry)
    physics_label = physics_to_idx(best_physics)
    
    return SolverResult(
        task_id=task.task_id,
        geometry_label=geometry_label,
        physics_label=physics_label,
        energy=best_energy,
        operation=f"{best_geometry} + {best_physics}"
    )


# =============================================================================
# GUIDED SOLVER
# =============================================================================

class GuidedSolver:
    """
    Solver that uses Policy Network to prioritize search.
    Instead of trying all operations, uses P(category) to order the search.
    """
    
    def __init__(self, policy: PolicyNetwork, config: Phase9Config):
        self.policy = policy
        self.config = config
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve task using neural guidance."""
        start_time = time.time()
        
        # Get policy predictions from first training example
        ex = task.train_examples[0]
        predictions = self.policy.predict(ex.input_grid, ex.output_grid)
        
        if verbose:
            printfl(f"\n   Policy predictions:")
            printfl(f"   Geometry: {predictions['geometry_pred']} ({predictions['geometry_probs'][predictions['geometry_pred']]:.2f})")
            printfl(f"   Physics: {predictions['physics_pred']} ({predictions['physics_probs'][predictions['physics_pred']]:.2f})")
        
        # Order operations by policy probability
        geo_order = sorted(GEOMETRY_CLASSES, 
                          key=lambda g: -predictions['geometry_probs'].get(g, 0))
        phys_order = sorted(PHYSICS_CLASSES,
                           key=lambda p: -predictions['physics_probs'].get(p, 0))
        
        # Try operations in priority order
        best_energy = float('inf')
        best_op = "identity"
        
        def compute_energy(pred, target):
            if pred.shape != target.shape:
                return 1000.0
            return (pred.data != target.data).float().mean().item()
        
        def eval_on_examples(transform_fn):
            total = 0
            for ex in task.train_examples:
                try:
                    result = transform_fn(ex.input_grid)
                    total += compute_energy(result, ex.output_grid)
                except:
                    return float('inf')
            return total / len(task.train_examples)
        
        # Movement relaxation helper
        def relax_movement(grid, pot_name, max_steps=20):
            data = grid.data.clone().cpu()
            H, W = data.shape
            for step in range(max_steps):
                # Simple object detection
                visited = np.zeros((H, W), dtype=bool)
                objects = []
                for r in range(H):
                    for c in range(W):
                        if visited[r, c] or data[r, c] == 0: 
                            visited[r, c] = True
                            continue
                        color = data[r, c].item()
                        pixels = []
                        queue = [(r, c)]
                        visited[r, c] = True
                        while queue:
                            cr, cc = queue.pop(0)
                            pixels.append((cr, cc))
                            for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                                nr, nc = cr + dr, cc + dc
                                if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                                    if data[nr, nc] == color:
                                        visited[nr, nc] = True
                                        queue.append((nr, nc))
                        if pixels:
                            objects.append({'color': color, 'pixels': pixels})
                
                if not objects: break
                moved = False
                for obj in objects:
                    rows = [p[0] for p in obj['pixels']]
                    cols = [p[1] for p in obj['pixels']]
                    r1, r2 = min(rows), max(rows) + 1
                    c1, c2 = min(cols), max(cols) + 1
                    cr, cc = (r1 + r2) / 2, (c1 + c2) / 2
                    
                    dr, dc = 0, 0
                    if pot_name == 'V_top' and r1 > 0:
                        dr = -1
                    elif pot_name == 'V_contact':
                        min_dist = float('inf')
                        for other in objects:
                            if other['pixels'] == obj['pixels']: continue
                            orows = [p[0] for p in other['pixels']]
                            ocols = [p[1] for p in other['pixels']]
                            ocr = (min(orows) + max(orows) + 1) / 2
                            occ = (min(ocols) + max(ocols) + 1) / 2
                            dist = ((cr - ocr)**2 + (cc - occ)**2) ** 0.5
                            if dist < min_dist and dist > 1:
                                min_dist = dist
                                if abs(cr - ocr) > abs(cc - occ):
                                    dr, dc = (1 if ocr > cr else -1, 0)
                                else:
                                    dr, dc = (0, 1 if occ > cc else -1)
                    
                    if dr == 0 and dc == 0: continue
                    new_pixels = [(p[0]+dr, p[1]+dc) for p in obj['pixels']]
                    if all(0 <= nr < H and 0 <= nc < W and 
                           (data[nr, nc] == 0 or (nr-dr, nc-dc) in obj['pixels'])
                           for nr, nc in new_pixels):
                        for p in obj['pixels']: data[p[0], p[1]] = 0
                        for p in obj['pixels']: data[p[0]+dr, p[1]+dc] = obj['color']
                        moved = True
                if not moved: break
            return ARCGrid(data)
        
        # Try top geometry predictions first
        for geo in geo_order[:2]:  # Top 2 geometry
            if geo == 'identity':
                # Try physics on same shape
                for phys in phys_order[:2]:
                    if phys == 'movement':
                        # Try movement potentials
                        for pot_name in ['V_contact', 'V_top']:
                            def move_fn(g, pn=pot_name):
                                return relax_movement(g, pn)
                            e = eval_on_examples(move_fn)
                            if e < best_energy:
                                best_energy = e
                                best_op = pot_name
                    elif phys == 'color':
                        for from_c in range(1, 5):
                            for to_c in range(0, 5):
                                if from_c == to_c: continue
                                def color_map(g, fc=from_c, tc=to_c):
                                    d = g.data.clone()
                                    d[d == fc] = tc
                                    return ARCGrid(d)
                                e = eval_on_examples(color_map)
                                if e < best_energy:
                                    best_energy = e
                                    best_op = f"color_map({from_c}->{to_c})"
                    elif phys == 'pattern':
                        for name, rot in [('rot180', 2), ('rot90', 1)]:
                            def rotate(g, r=rot):
                                return ARCGrid(g.data.rot90(r, [0, 1]))
                            e = eval_on_examples(rotate)
                            if e < best_energy:
                                best_energy = e
                                best_op = name
            
            elif geo == 'crop':
                def crop_to_content(g):
                    data = g.data.cpu().numpy()
                    non_bg = np.argwhere(data != 0)
                    if len(non_bg) == 0: return g
                    r1, c1 = non_bg.min(axis=0)
                    r2, c2 = non_bg.max(axis=0)
                    return ARCGrid(g.data[r1:r2+1, c1:c2+1].clone())
                e = eval_on_examples(crop_to_content)
                if e < best_energy:
                    best_energy = e
                    best_op = "crop_to_content"
            
            elif geo == 'extract':
                for selector in ['largest', 'smallest']:
                    def extract(g, sel=selector):
                        # Simplified extraction
                        return crop_to_content(g)  # Fallback
                    e = eval_on_examples(extract)
                    if e < best_energy:
                        best_energy = e
                        best_op = f"extract({selector})"
            
            elif geo == 'scale':
                for k in [2, 3]:
                    def scale(g, factor=k):
                        return ARCGrid(g.data.repeat_interleave(factor, 0).repeat_interleave(factor, 1))
                    e = eval_on_examples(scale)
                    if e < best_energy:
                        best_energy = e
                        best_op = f"scale({k}x)"
        
        elapsed = time.time() - start_time
        
        return {
            'task_id': task.task_id,
            'operation': best_op,
            'energy': best_energy,
            'elapsed_ms': elapsed * 1000,
            'geometry_pred': predictions['geometry_pred'],
            'physics_pred': predictions['physics_pred'],
            'is_perfect': best_energy < 0.0001
        }


# =============================================================================
# MAIN EVALUATION
# =============================================================================

def generate_labels(tasks: List[ARCTask], config: Phase9Config) -> Dict[str, SolverResult]:
    """Generate ground truth labels by running Phase 8.3 solver on all tasks."""
    labels = {}
    
    printfl(f"\nGenerating labels for {len(tasks)} tasks...")
    
    for i, task in enumerate(tasks):
        result = run_phase83_solver(task, config)
        if result and result.energy < 0.5:  # Only keep "solvable" tasks
            labels[task.task_id] = result
        
        if (i + 1) % 20 == 0:
            printfl(f"  Processed {i+1}/{len(tasks)}, labeled {len(labels)} tasks")
    
    printfl(f"\nLabeled {len(labels)} tasks with energy < 0.5")
    
    # Statistics
    geo_counts = Counter(r.geometry_label for r in labels.values())
    phys_counts = Counter(r.physics_label for r in labels.values())
    
    printfl(f"\nGeometry distribution:")
    for i, name in enumerate(GEOMETRY_CLASSES):
        printfl(f"  {name}: {geo_counts.get(i, 0)}")
    
    printfl(f"\nPhysics distribution:")
    for i, name in enumerate(PHYSICS_CLASSES):
        printfl(f"  {name}: {phys_counts.get(i, 0)}")
    
    return labels


def run_phase9(data_path: str, config: Phase9Config):
    """Execute Phase 9: Neural Amortization."""
    
    printfl("=" * 70)
    printfl("ARC-SGC Phase 9: Neural Amortization (The Neural Physicist)")
    printfl("=" * 70)
    
    # Load tasks
    tasks = load_arc_tasks(data_path, config.device)
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        printfl("No tasks found!")
        return
    
    # Task 1: Generate labels
    printfl("\n" + "=" * 50)
    printfl("TASK 1: Dataset Generation")
    printfl("=" * 50)
    
    labels = generate_labels(tasks, config)
    
    if len(labels) < 10:
        printfl("Not enough labeled data for training!")
        return
    
    # Task 2: Train Policy Network
    printfl("\n" + "=" * 50)
    printfl("TASK 2: Train Policy Network")
    printfl("=" * 50)
    
    dataset = ARCPolicyDataset(tasks, labels, config)
    printfl(f"Dataset size: {len(dataset)} samples")
    
    policy = train_policy_network(dataset, config)
    
    if policy is None:
        printfl("Training failed!")
        return
    
    # Task 3: Validate with Guided Solver
    printfl("\n" + "=" * 50)
    printfl("TASK 3: Guided Solver Validation")
    printfl("=" * 50)
    
    guided_solver = GuidedSolver(policy, config)
    
    perfect_tasks = []
    total_time = 0
    
    for task in tasks[:50]:  # Test on first 50
        result = guided_solver.solve_task(task, verbose=False)
        total_time += result['elapsed_ms']
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            printfl(f"  [PERFECT] {task.task_id}: {result['operation']} ({result['elapsed_ms']:.1f}ms)")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("PHASE 9 SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Perfect solves: {len(perfect_tasks)}")
    printfl(f"  Avg inference time: {total_time/50:.1f}ms")
    
    if perfect_tasks:
        printfl(f"\nPerfect solutions:")
        for r in perfect_tasks:
            printfl(f"  {r['task_id']}: {r['operation']} (predicted: {r['geometry_pred']}/{r['physics_pred']})")


def main():
    config = Phase9Config()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase9(arc_path, config)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
