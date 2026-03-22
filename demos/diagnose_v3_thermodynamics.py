"""
Diagnostic: Why is v3 Temperature Stuck at 0.5?

This script runs targeted experiments to understand the thermodynamic failure mode.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
import numpy as np

# Import from v3
from adaptive_polarity_v3 import (
    AdaptivePolarityConfigV3, AdaptivePolarityAgentV3, 
    build_sudoku_graph
)
from baby_agi_sudoku import generate_puzzles_with_clues


def diagnose_temperature_dynamics():
    """Analyze what's keeping temperature at 0.5."""
    device = "cuda" if torch.cuda.is_available() else "cpu"
    config = AdaptivePolarityConfigV3()
    edges, edge_types = build_sudoku_graph()
    
    model = AdaptivePolarityAgentV3(config, edges, edge_types).to(device)
    
    # Generate data
    train_puzzles, train_solutions = generate_puzzles_with_clues(500, 35, seed=42)
    train_dataset = TensorDataset(
        torch.tensor(train_puzzles, dtype=torch.long),
        torch.tensor(train_solutions - 1, dtype=torch.long),
    )
    train_loader = DataLoader(train_dataset, batch_size=32, shuffle=True, drop_last=True)
    
    optimizer = torch.optim.AdamW(model.parameters(), lr=1e-3)
    
    print("=" * 80)
    print("DIAGNOSTIC: Temperature Dynamics Analysis")
    print("=" * 80)
    
    history = {
        'epoch': [], 'temp': [], 'arousal': [], 'pain_ema': [],
        'constraint_ema': [], 'train_acc': [], 'overlap_mean': [],
        'drift_norm': [], 'noise_norm': []
    }
    
    for epoch in range(50):
        model.train()
        epoch_pain = []
        epoch_overlap = []
        epoch_drift = []
        epoch_noise = []
        correct = 0
        total = 0
        
        for batch in train_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            optimizer.zero_grad()
            
            # Get intermediate values for diagnosis
            with torch.no_grad():
                clue_mask = (puzzles > 0)
                stalks = model.embed(puzzles)
                stalks = stalks + model.cell_mlp(stalks)
                
                prior_prec, effective_prec = model.controller.get_effective_precision()
                temperature = model.controller.get_temperature()
                
                # Track one diffusion step
                logits = model.output_head(stalks)
                probs = F.softmax(logits, dim=-1)
                
                # Compute overlap
                src_probs = probs[:, model.diffusion.src_idx, :]
                dst_probs = probs[:, model.diffusion.dst_idx, :]
                overlap = (src_probs * dst_probs).sum(dim=-1)
                epoch_overlap.append(overlap.mean().item())
                
                # Compute drift magnitude
                g = model.diffusion.get_mixture_weight()
                g_per_edge = g[model.diffusion.type_idx].view(1, -1, 1)
                prec_per_edge = effective_prec[model.diffusion.type_idx].view(1, -1, 1)
                
                dst_stalks = stalks[:, model.diffusion.dst_idx, :]
                restricted_src = model.diffusion.apply_restriction(stalks)
                
                attr_flow = restricted_src - dst_stalks
                repl_flow = -overlap.unsqueeze(-1) * (restricted_src - dst_stalks)
                flow = prec_per_edge * (g_per_edge * attr_flow + (1 - g_per_edge) * repl_flow)
                
                drift_norm = (config.diffusion_dt * flow).norm().item()
                epoch_drift.append(drift_norm)
                
                # Compute noise magnitude  
                noise_std = config.noise_scale * torch.sqrt(2 * temperature * config.diffusion_dt + 1e-8)
                noise_norm = (noise_std * stalks.shape[-1] ** 0.5).item()  # Expected norm
                epoch_noise.append(noise_norm)
            
            # Normal forward pass
            logits, energy, complexity, per_type_energy, arousal, g, temp = model(puzzles, solutions)
            
            loss_ce = F.cross_entropy(
                logits.view(-1, 9),
                solutions.view(-1),
                reduction='none'
            ).view(puzzles.shape[0], 81)
            
            unknown_mask = (puzzles == 0).float()
            loss_ce = (loss_ce * unknown_mask).sum() / unknown_mask.sum()
            epoch_pain.append(loss_ce.item())
            
            loss = loss_ce + 0.5 * energy + complexity
            loss.backward()
            optimizer.step()
            
            with torch.no_grad():
                preds = logits.argmax(dim=-1)
                unknown = (puzzles == 0)
                correct += ((preds == solutions) & unknown).sum().item()
                total += unknown.sum().item()
        
        # Record metrics
        train_acc = correct / max(total, 1)
        history['epoch'].append(epoch)
        history['temp'].append(model.controller.get_temperature().item())
        history['arousal'].append(model.controller.get_arousal().item())
        history['pain_ema'].append(model.controller.task_pain_ema.item())
        history['constraint_ema'].append(model.controller.constraint_ema.mean().item())
        history['train_acc'].append(train_acc)
        history['overlap_mean'].append(np.mean(epoch_overlap))
        history['drift_norm'].append(np.mean(epoch_drift))
        history['noise_norm'].append(np.mean(epoch_noise))
        
        if epoch % 5 == 0:
            print(f"Epoch {epoch:3d} | Acc={train_acc*100:5.1f}% | "
                  f"Temp={history['temp'][-1]:.3f} | Pain_EMA={history['pain_ema'][-1]:.3f} | "
                  f"Overlap={history['overlap_mean'][-1]:.4f} | "
                  f"Drift/Noise={history['drift_norm'][-1]/max(history['noise_norm'][-1],1e-6):.2f}")
    
    print("\n" + "=" * 80)
    print("DIAGNOSIS RESULTS")
    print("=" * 80)
    
    final_temp = history['temp'][-1]
    final_drift = history['drift_norm'][-1]
    final_noise = history['noise_norm'][-1]
    final_overlap = history['overlap_mean'][-1]
    
    print(f"\n1. TEMPERATURE: {final_temp:.3f}")
    if final_temp > 0.4:
        print("   -> Temperature stayed HIGH. Arousal never dropped.")
        print("   -> This means pain/loss never decreased enough to cool down.")
    
    print(f"\n2. DRIFT/NOISE RATIO: {final_drift/max(final_noise, 1e-6):.3f}")
    if final_drift < final_noise:
        print("   -> NOISE DOMINATES DRIFT!")
        print("   -> The thermal noise is washing out the deterministic signal.")
        print("   -> Solution: Reduce noise_scale or increase drift.")
    else:
        print("   -> Drift dominates noise (good for crystallization)")
    
    print(f"\n3. PROBABILITY OVERLAP: {final_overlap:.4f}")
    print("   -> This is the average <p_u, p_v> over all edges.")
    if final_overlap > 0.2:
        print("   -> HIGH OVERLAP: Cells are predicting similar digits!")
        print("   -> The repulsive dynamics should be pushing harder.")
    else:
        print("   -> Low overlap: Cells are differentiating (good)")
    
    print(f"\n4. POLARITY g = {model.diffusion.get_mixture_weight().detach().cpu().numpy()}")
    print("   -> g near 0 = repulsive (correct for Sudoku)")
    
    print("\n" + "=" * 80)
    print("HYPOTHESIS: The system is trapped because:")
    print("1. High temperature -> noise dominates drift -> no crystallization")
    print("2. No crystallization -> loss stays high -> temperature stays high")
    print("3. This is a POSITIVE FEEDBACK LOOP (vicious cycle)")
    print("")
    print("PROPOSED FIX: Use ANNEALING instead of homeostatic temperature")
    print("- Start hot (explore), schedule cool-down (crystallize)")
    print("- Don't let pain control temperature during learning phase")
    print("=" * 80)
    
    return history


if __name__ == "__main__":
    diagnose_temperature_dynamics()
