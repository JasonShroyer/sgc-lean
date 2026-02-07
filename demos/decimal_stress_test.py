"""
Decimal Stress Test: Zero-Shot Generalization
==============================================

Tests whether the trained Homeostatic Sheaf Network can generalize
to decimal inputs without retraining.

Hypothesis: The "melted" multiplication path (arousal=1.0, precision~0)
should handle noisy/decimal inputs better than a rigid baseline because
it's already operating in a probabilistic, neighborhood-based regime.

The Platonic Insight:
- Integers are "Thick" points (high precision neighborhoods)
- Decimals are wider neighborhoods (lower precision)
- A model trained with "melted" precision should generalize naturally

Date: 2026-02-07
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
import numpy as np
from dataclasses import dataclass
from typing import Tuple, Optional
import sys
import os

# Import the model architectures
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellular_sheaf_homeostatic import HomeostaticSheafNetwork, HomeostaticConfig
from cellular_sheaf_network import CellularSheafNetwork, CellularConfig


def create_noisy_test_data(p: int, noise_level: float, n_samples: int = 1000):
    """
    Create test data with analog noise.
    
    For each sample:
    - Pick random integers x, y, z in [0, p-1]
    - Add multiplicative noise: x' = x * (1 + epsilon)
    - Compute noisy target: ((x' + y') * z') mod p (rounded)
    
    Returns embeddings as continuous values, not discrete indices.
    """
    np.random.seed(42)
    
    # Random integer base values
    x_int = np.random.randint(0, p, n_samples)
    y_int = np.random.randint(0, p, n_samples)
    z_int = np.random.randint(0, p, n_samples)
    
    # Add multiplicative noise
    noise_x = 1 + np.random.randn(n_samples) * noise_level
    noise_y = 1 + np.random.randn(n_samples) * noise_level
    noise_z = 1 + np.random.randn(n_samples) * noise_level
    
    x_noisy = x_int * noise_x
    y_noisy = y_int * noise_y
    z_noisy = z_int * noise_z
    
    # Compute "true" target (using original integers)
    target_true = ((x_int + y_int) * z_int) % p
    
    # Compute "noisy" target (what the answer "should" be with noisy inputs)
    # This is for reference - we still evaluate against the integer target
    target_noisy = ((x_noisy + y_noisy) * z_noisy) % p
    
    return {
        'x_int': torch.tensor(x_int, dtype=torch.long),
        'y_int': torch.tensor(y_int, dtype=torch.long),
        'z_int': torch.tensor(z_int, dtype=torch.long),
        'x_noisy': torch.tensor(x_noisy, dtype=torch.float32),
        'y_noisy': torch.tensor(y_noisy, dtype=torch.float32),
        'z_noisy': torch.tensor(z_noisy, dtype=torch.float32),
        'target_true': torch.tensor(target_true, dtype=torch.long),
        'target_noisy': torch.tensor(target_noisy, dtype=torch.float32),
    }


def evaluate_with_noise(model, data: dict, device: str, noise_mode: str = 'embedding'):
    """
    Evaluate model on noisy data.
    
    noise_mode:
    - 'none': Use clean integer inputs
    - 'embedding': Add noise to embeddings after lookup
    - 'interpolate': Interpolate between integer embeddings based on decimal part
    """
    model.eval()
    
    x_int = data['x_int'].to(device)
    y_int = data['y_int'].to(device)
    z_int = data['z_int'].to(device)
    x_noisy = data['x_noisy'].to(device)
    y_noisy = data['y_noisy'].to(device)
    z_noisy = data['z_noisy'].to(device)
    target = data['target_true'].to(device)
    
    with torch.no_grad():
        if noise_mode == 'none':
            # Clean evaluation
            if hasattr(model, 'precision_controller'):
                logits, _, _, _, _ = model(x_int, y_int, z_int)
            else:
                logits, _ = model(x_int, y_int, z_int)
        
        elif noise_mode == 'embedding':
            # Get embeddings and add noise proportional to the decimal offset
            e_x = model.embed(x_int)
            e_y = model.embed(y_int)
            e_z = model.embed(z_int)
            
            # Compute noise magnitude from the decimal difference
            noise_scale_x = (x_noisy - x_int.float()).unsqueeze(-1)
            noise_scale_y = (y_noisy - y_int.float()).unsqueeze(-1)
            noise_scale_z = (z_noisy - z_int.float()).unsqueeze(-1)
            
            # Add scaled noise to embeddings
            e_x_noisy = e_x + noise_scale_x * torch.randn_like(e_x) * 0.1
            e_y_noisy = e_y + noise_scale_y * torch.randn_like(e_y) * 0.1
            e_z_noisy = e_z + noise_scale_z * torch.randn_like(e_z) * 0.1
            
            # Manual forward pass with noisy embeddings
            v_x = model.cell_x.set_from_input(e_x_noisy)
            v_y = model.cell_y.set_from_input(e_y_noisy)
            v_z = model.cell_z.set_from_input(e_z_noisy)
            
            batch_size = x_int.shape[0]
            config = model.config
            v_sum = torch.zeros(batch_size, config.stalk_dim, device=device)
            v_result = torch.zeros(batch_size, config.stalk_dim, device=device)
            
            # Use appropriate diffusion method based on model type
            if hasattr(model, 'perceptual_inference_step'):
                for _ in range(config.diffusion_steps):
                    v_sum, v_result = model.perceptual_inference_step(
                        v_x, v_y, v_z, v_sum, v_result,
                        dt=config.diffusion_dt
                    )
            else:
                # Baseline model uses diffusion_step
                for _ in range(config.diffusion_steps):
                    v_sum, v_result = model.diffusion_step(
                        v_x, v_y, v_z, v_sum, v_result,
                        dt=config.diffusion_dt
                    )
            
            logits = model.cell_result.get_output(v_result)
        
        elif noise_mode == 'interpolate':
            # Interpolate between floor and ceil embeddings
            x_floor = x_noisy.floor().long().clamp(0, model.config.p - 1)
            x_ceil = x_noisy.ceil().long().clamp(0, model.config.p - 1)
            x_frac = (x_noisy - x_noisy.floor()).unsqueeze(-1)
            
            y_floor = y_noisy.floor().long().clamp(0, model.config.p - 1)
            y_ceil = y_noisy.ceil().long().clamp(0, model.config.p - 1)
            y_frac = (y_noisy - y_noisy.floor()).unsqueeze(-1)
            
            z_floor = z_noisy.floor().long().clamp(0, model.config.p - 1)
            z_ceil = z_noisy.ceil().long().clamp(0, model.config.p - 1)
            z_frac = (z_noisy - z_noisy.floor()).unsqueeze(-1)
            
            e_x = model.embed(x_floor) * (1 - x_frac) + model.embed(x_ceil) * x_frac
            e_y = model.embed(y_floor) * (1 - y_frac) + model.embed(y_ceil) * y_frac
            e_z = model.embed(z_floor) * (1 - z_frac) + model.embed(z_ceil) * z_frac
            
            v_x = model.cell_x.set_from_input(e_x)
            v_y = model.cell_y.set_from_input(e_y)
            v_z = model.cell_z.set_from_input(e_z)
            
            batch_size = x_int.shape[0]
            config = model.config
            v_sum = torch.zeros(batch_size, config.stalk_dim, device=device)
            v_result = torch.zeros(batch_size, config.stalk_dim, device=device)
            
            if hasattr(model, 'perceptual_inference_step'):
                for _ in range(config.diffusion_steps):
                    v_sum, v_result = model.perceptual_inference_step(
                        v_x, v_y, v_z, v_sum, v_result,
                        dt=config.diffusion_dt
                    )
            else:
                for _ in range(config.diffusion_steps):
                    v_sum, v_result = model.diffusion_step(
                        v_x, v_y, v_z, v_sum, v_result,
                        dt=config.diffusion_dt
                    )
            
            logits = model.cell_result.get_output(v_result)
        
        pred = logits.argmax(dim=-1)
        accuracy = (pred == target).float().mean().item()
    
    return accuracy


def train_baseline_model(config, device, epochs=1000):
    """Train a baseline model for comparison."""
    from cellular_sheaf_network import create_composition_dataset, CellularSheafNetwork
    
    print("\nTraining Baseline Model...")
    model = CellularSheafNetwork(config).to(device)
    
    train_dataset, test_dataset = create_composition_dataset(config.p, train_frac=0.3)
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    optimizer = torch.optim.AdamW(model.parameters(), lr=config.lr, weight_decay=config.weight_decay)
    
    best_acc = 0
    for epoch in range(epochs):
        model.train()
        for batch in train_loader:
            x, y, z, target = [b.to(device) for b in batch]
            optimizer.zero_grad()
            logits, energy = model(x, y, z)
            loss = F.cross_entropy(logits, target) + 0.01 * energy
            loss.backward()
            optimizer.step()
        
        if epoch % 100 == 0:
            model.eval()
            correct = 0
            total = 0
            with torch.no_grad():
                for batch in test_loader:
                    x, y, z, target = [b.to(device) for b in batch]
                    logits, _ = model(x, y, z)
                    pred = logits.argmax(dim=-1)
                    correct += (pred == target).sum().item()
                    total += target.shape[0]
            acc = correct / total
            print(f"  Epoch {epoch}: Test Acc = {acc:.1%}")
            if acc > 0.99:
                print(f"  Baseline grokked at epoch {epoch}")
                break
            best_acc = max(best_acc, acc)
    
    return model


def train_homeostatic_model(config, device, epochs=1000):
    """Train a homeostatic model."""
    from cellular_sheaf_homeostatic import create_composition_dataset
    
    print("\nTraining Homeostatic Model...")
    model = HomeostaticSheafNetwork(config).to(device)
    
    train_dataset, test_dataset = create_composition_dataset(config.p, train_frac=0.3)
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    main_params = [p for n, p in model.named_parameters() if 'log_precision' not in n]
    precision_params = [model.precision_controller.log_precision_prior]
    
    optimizer = torch.optim.AdamW([
        {'params': main_params, 'lr': config.lr, 'weight_decay': config.weight_decay},
        {'params': precision_params, 'lr': config.precision_lr, 'weight_decay': 0.0},
    ])
    
    for epoch in range(epochs):
        model.train()
        for batch in train_loader:
            x, y, z, target, sum_labels = [b.to(device) for b in batch]
            optimizer.zero_grad()
            logits, free_energy, complexity, _, _ = model(x, y, z)
            loss = F.cross_entropy(logits, target) + 0.01 * free_energy + complexity
            loss.backward()
            optimizer.step()
        
        if epoch % 100 == 0:
            model.eval()
            correct = 0
            total = 0
            with torch.no_grad():
                for batch in test_loader:
                    x, y, z, target, _ = [b.to(device) for b in batch]
                    logits, _, _, _, _ = model(x, y, z)
                    pred = logits.argmax(dim=-1)
                    correct += (pred == target).sum().item()
                    total += target.shape[0]
            acc = correct / total
            arousal = model.precision_controller.energy_ema.cpu().numpy()
            print(f"  Epoch {epoch}: Test Acc = {acc:.1%}, Arousal = [{arousal[0]:.2f}, {arousal[1]:.2f}, {arousal[2]:.2f}, {arousal[3]:.2f}]")
            if acc > 0.99:
                print(f"  Homeostatic grokked at epoch {epoch}")
                break
    
    return model


def run_stress_test():
    """Run the decimal stress test comparing Baseline vs Homeostatic."""
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    p = 23
    
    print("=" * 80)
    print("DECIMAL STRESS TEST: Zero-Shot Generalization")
    print("=" * 80)
    print(f"Device: {device}")
    print(f"Modulus: p={p}")
    print("=" * 80)
    
    # Train both models
    baseline_config = CellularConfig(p=p, epochs=1200, seed=42)
    homeostatic_config = HomeostaticConfig(p=p, epochs=1200, tau=5.0, ema_alpha=0.95, seed=42)
    
    baseline_model = train_baseline_model(baseline_config, device, epochs=1200)
    homeostatic_model = train_homeostatic_model(homeostatic_config, device, epochs=1200)
    
    # Create test data with varying noise levels
    noise_levels = [0.0, 0.01, 0.05, 0.1, 0.2, 0.5]
    
    print("\n" + "=" * 80)
    print("STRESS TEST RESULTS")
    print("=" * 80)
    print("\nNoise Level | Baseline (clean) | Baseline (noisy) | Homeostatic (clean) | Homeostatic (noisy)")
    print("-" * 100)
    
    results = []
    
    for noise in noise_levels:
        data = create_noisy_test_data(p, noise_level=noise, n_samples=2000)
        
        # Evaluate baseline
        baseline_clean = evaluate_with_noise(baseline_model, data, device, noise_mode='none')
        baseline_noisy = evaluate_with_noise(baseline_model, data, device, noise_mode='embedding') if noise > 0 else baseline_clean
        
        # Evaluate homeostatic
        homeo_clean = evaluate_with_noise(homeostatic_model, data, device, noise_mode='none')
        homeo_noisy = evaluate_with_noise(homeostatic_model, data, device, noise_mode='embedding') if noise > 0 else homeo_clean
        
        print(f"  {noise:9.2f} | {baseline_clean:16.1%} | {baseline_noisy:16.1%} | {homeo_clean:19.1%} | {homeo_noisy:18.1%}")
        
        results.append({
            'noise': noise,
            'baseline_clean': baseline_clean,
            'baseline_noisy': baseline_noisy,
            'homeo_clean': homeo_clean,
            'homeo_noisy': homeo_noisy,
        })
    
    # Analysis
    print("\n" + "=" * 80)
    print("ANALYSIS")
    print("=" * 80)
    
    # Compute degradation
    baseline_degradation = results[-1]['baseline_noisy'] - results[0]['baseline_clean']
    homeo_degradation = results[-1]['homeo_noisy'] - results[0]['homeo_clean']
    
    print(f"\nDegradation at max noise (0.5):")
    print(f"  Baseline:    {baseline_degradation:+.1%}")
    print(f"  Homeostatic: {homeo_degradation:+.1%}")
    
    if homeo_degradation > baseline_degradation:
        print(f"\n>>> Homeostatic model is MORE ROBUST by {(homeo_degradation - baseline_degradation):.1%} <<<")
    else:
        print(f"\n>>> Baseline model is more robust by {(baseline_degradation - homeo_degradation):.1%} <<<")
    
    # Final precision state
    print("\nFinal Homeostatic State:")
    with torch.no_grad():
        prior = torch.exp(homeostatic_model.precision_controller.log_precision_prior).cpu().numpy()
        ema = homeostatic_model.precision_controller.energy_ema.cpu().numpy()
    print(f"  Prior Precision: [{prior[0]:.3f}, {prior[1]:.3f}, {prior[2]:.3f}, {prior[3]:.3f}]")
    print(f"  Energy EMA:      [{ema[0]:.3f}, {ema[1]:.3f}, {ema[2]:.3f}, {ema[3]:.3f}]")
    
    print("\n" + "=" * 80)
    
    return results


if __name__ == "__main__":
    results = run_stress_test()
