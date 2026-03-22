"""
Test Adaptive Polarity on Sudoku

This script tests whether the agent can AUTOMATICALLY discover that
Sudoku constraints are REPULSIVE (σ < 0) without hard-coding.

The key hypothesis:
- Start with neutral polarity (σ = 0)
- Train on Sudoku task loss
- Observe polarity evolving to negative values
- This proves the agent can "sense" the constraint type
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
from datetime import datetime
import os

from adaptive_polarity_sheaf import (
    AdaptivePolarityConfig,
    AdaptivePolaritySudokuAgent,
    build_sudoku_graph,
)
from baby_agi_sudoku import generate_puzzles_with_clues


def evaluate(model, loader, device):
    """Evaluate model accuracy."""
    model.eval()
    correct_cells = 0
    total_cells = 0
    correct_puzzles = 0
    total_puzzles = 0
    
    with torch.no_grad():
        for batch in loader:
            puzzles, solutions = [x.to(device) for x in batch]
            logits, *_ = model(puzzles)
            preds = logits.argmax(dim=-1)
            
            unknown_mask = (puzzles == 0)
            correct = (preds == solutions) & unknown_mask
            
            correct_cells += correct.sum().item()
            total_cells += unknown_mask.sum().item()
            
            puzzle_correct = ((preds == solutions) | ~unknown_mask).all(dim=1)
            correct_puzzles += puzzle_correct.sum().item()
            total_puzzles += puzzles.shape[0]
    
    cell_acc = correct_cells / max(total_cells, 1)
    puzzle_acc = correct_puzzles / max(total_puzzles, 1)
    return cell_acc, puzzle_acc


def run_adaptive_polarity_test():
    """Run the adaptive polarity test on Sudoku."""
    device = "cuda" if torch.cuda.is_available() else "cpu"
    
    # Config
    config = AdaptivePolarityConfig(
        epochs=200,
        batch_size=32,
        diffusion_steps=8,
        tau=0.5,
        polarity_init=0.0,  # Start NEUTRAL
        log_interval=10,
    )
    
    # Build graph
    edges, edge_types = build_sudoku_graph()
    
    # Create model
    model = AdaptivePolaritySudokuAgent(config, edges, edge_types).to(device)
    
    # Generate data (35 clues - medium difficulty)
    train_puzzles, train_solutions = generate_puzzles_with_clues(1000, 35, seed=42)
    test_puzzles, test_solutions = generate_puzzles_with_clues(200, 35, seed=1042)
    
    train_dataset = TensorDataset(
        torch.tensor(train_puzzles, dtype=torch.long),
        torch.tensor(train_solutions - 1, dtype=torch.long),
    )
    test_dataset = TensorDataset(
        torch.tensor(test_puzzles, dtype=torch.long),
        torch.tensor(test_solutions - 1, dtype=torch.long),
    )
    
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True, drop_last=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    # Optimizer with separate LR for polarity
    polarity_params = [model.diffusion.polarity_logit]
    other_params = [p for p in model.parameters() if p is not model.diffusion.polarity_logit]
    
    optimizer = torch.optim.AdamW([
        {'params': other_params, 'lr': config.lr},
        {'params': polarity_params, 'lr': config.polarity_lr}
    ], weight_decay=config.weight_decay)
    
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=config.epochs)
    
    # Logging
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = f"{config.log_dir}/run_{timestamp}"
    os.makedirs(log_path, exist_ok=True)
    writer = SummaryWriter(log_path)
    
    print("=" * 100)
    print("ADAPTIVE POLARITY TEST: Can the agent discover Sudoku needs REPULSION?")
    print("=" * 100)
    print(f"Device: {device}")
    print(f"Parameters: {sum(p.numel() for p in model.parameters()):,}")
    print(f"Initial Polarity: {model.diffusion.get_polarity().detach().cpu().numpy()}")
    print(f"TensorBoard: {log_path}")
    print("=" * 100)
    print()
    print("Key Question: Will polarity evolve from 0 (neutral) to NEGATIVE (repulsive)?")
    print()
    
    print("-" * 110)
    print(f" {'Epoch':>5} | {'Train':>6} | {'Test':>6} | {'Pain':>6} | "
          f"{'sig_row':>7} | {'sig_col':>7} | {'sig_box':>7} | {'Arousal':>7} | Status")
    print("-" * 110)
    
    best_acc = 0.0
    
    for epoch in range(config.epochs):
        model.train()
        epoch_loss = 0.0
        
        for batch in train_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            optimizer.zero_grad()
            
            logits, energy, complexity, per_type_energy, arousal, polarity = model(puzzles, solutions)
            
            # Task loss
            loss_ce = F.cross_entropy(
                logits.view(-1, 9),
                solutions.view(-1),
                reduction='none'
            ).view(puzzles.shape[0], 81)
            
            unknown_mask = (puzzles == 0).float()
            loss_ce = (loss_ce * unknown_mask).sum() / unknown_mask.sum()
            
            # Total loss (energy term will drive polarity learning)
            loss = loss_ce + 1.0 * energy + complexity
            
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            
            epoch_loss += loss.item()
        
        scheduler.step()
        
        # Evaluate
        if epoch % config.log_interval == 0:
            train_acc, _ = evaluate(model, train_loader, device)
            test_acc, _ = evaluate(model, test_loader, device)
            
            polarity = model.diffusion.get_polarity().detach().cpu()
            arousal = model.controller.get_arousal().mean().item()
            pain = model.controller.task_pain_ema.item()
            
            status = ""
            if test_acc > best_acc:
                best_acc = test_acc
                status = "NEW BEST"
            
            # Check if polarity is learning correctly
            if polarity.min() < -0.3:
                status += " REPULSION DETECTED!"
            
            print(f" {epoch:>5} | {train_acc*100:>5.1f}% | {test_acc*100:>5.1f}% | {pain:>6.2f} | "
                  f"{polarity[0]:>7.3f} | {polarity[1]:>7.3f} | {polarity[2]:>7.3f} | "
                  f"{arousal:>7.3f} | {status}")
            
            # Log to TensorBoard
            writer.add_scalar("train/acc", train_acc, epoch)
            writer.add_scalar("test/acc", test_acc, epoch)
            writer.add_scalar("controller/pain", pain, epoch)
            writer.add_scalar("controller/arousal", arousal, epoch)
            writer.add_scalar("polarity/row", polarity[0], epoch)
            writer.add_scalar("polarity/col", polarity[1], epoch)
            writer.add_scalar("polarity/box", polarity[2], epoch)
    
    # Final summary
    final_polarity = model.diffusion.get_polarity().detach().cpu()
    print("=" * 100)
    print("FINAL RESULTS")
    print("=" * 100)
    print(f"Best Test Accuracy: {best_acc*100:.1f}%")
    print(f"Final Polarity: [row={final_polarity[0]:.3f}, col={final_polarity[1]:.3f}, box={final_polarity[2]:.3f}]")
    print()
    
    if final_polarity.min() < -0.3:
        print("SUCCESS: Agent discovered REPULSIVE constraints for Sudoku!")
        print("This proves the agent can sense constraint type without hard-coding.")
    elif final_polarity.max() < 0.1:
        print("PARTIAL: Polarity moved towards neutral/negative.")
    else:
        print("FAILED: Agent did not discover repulsive nature of Sudoku constraints.")
    
    print("=" * 100)
    
    writer.close()
    return model


if __name__ == "__main__":
    model = run_adaptive_polarity_test()
