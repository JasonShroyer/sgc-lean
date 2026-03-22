#!/usr/bin/env python3
"""
Simple grokking benchmark to measure actual training speed.
"""
import time
import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np

class EmbeddingGrokMLP(nn.Module):
    def __init__(self, p=97, embed_dim=128, hidden_dim=128, n_layers=2, noise_std=0.1):
        super().__init__()
        self.p = p
        self.noise_std = noise_std
        self.embed_a = nn.Embedding(p, embed_dim)
        self.embed_b = nn.Embedding(p, embed_dim)
        
        layers = [nn.Linear(2 * embed_dim, hidden_dim), nn.ReLU()]
        for _ in range(n_layers - 1):
            layers.extend([nn.Linear(hidden_dim, hidden_dim), nn.ReLU()])
        self.hidden = nn.Sequential(*layers)
        self.output = nn.Linear(hidden_dim, p)
    
    def forward(self, a, b):
        e_a, e_b = self.embed_a(a), self.embed_b(b)
        if self.training and self.noise_std > 0:
            e_a = e_a + torch.randn_like(e_a) * self.noise_std
            e_b = e_b + torch.randn_like(e_b) * self.noise_std
        return self.output(self.hidden(torch.cat([e_a, e_b], dim=-1)))


def benchmark_grokking(noise_std=0.1, max_epochs=3000):
    p = 97
    all_pairs = [(a, b) for a in range(p) for b in range(p)]
    np.random.seed(42)
    np.random.shuffle(all_pairs)
    n_train = int(len(all_pairs) * 0.3)
    train_pairs, test_pairs = all_pairs[:n_train], all_pairs[n_train:]

    train_a = torch.tensor([x[0] for x in train_pairs])
    train_b = torch.tensor([x[1] for x in train_pairs])
    train_c = torch.tensor([(x[0]+x[1])%p for x in train_pairs])
    test_a = torch.tensor([x[0] for x in test_pairs])
    test_b = torch.tensor([x[1] for x in test_pairs])
    test_c = torch.tensor([(x[0]+x[1])%p for x in test_pairs])

    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    model = EmbeddingGrokMLP(noise_std=noise_std).to(device)
    optimizer = optim.AdamW(model.parameters(), lr=1e-3, weight_decay=1.0)
    criterion = nn.CrossEntropyLoss()

    train_a, train_b, train_c = train_a.to(device), train_b.to(device), train_c.to(device)
    test_a, test_b, test_c = test_a.to(device), test_b.to(device), test_c.to(device)

    print(f"GROKKING BENCHMARK (embed_noise={noise_std}, wd=1.0)")
    print("=" * 60)
    print(f"Device: {device}, Train: {len(train_pairs)}, Test: {len(test_pairs)}")
    print(f"{'Epoch':>6} | {'Train':>7} | {'Test':>7} | {'Time':>8}")
    print("-" * 40)

    start = time.time()
    grok_epoch = -1
    
    for epoch in range(1, max_epochs + 1):
        model.train()
        optimizer.zero_grad()
        out = model(train_a, train_b)
        loss = criterion(out, train_c)
        loss.backward()
        optimizer.step()
        
        if epoch % 100 == 0 or epoch == 1:
            model.eval()
            with torch.no_grad():
                train_acc = (model(train_a, train_b).argmax(1) == train_c).float().mean().item()
                test_acc = (model(test_a, test_b).argmax(1) == test_c).float().mean().item()
            elapsed = time.time() - start
            print(f"{epoch:6d} | {train_acc*100:6.1f}% | {test_acc*100:6.1f}% | {elapsed:7.1f}s")
            
            if test_acc > 0.95 and grok_epoch < 0:
                grok_epoch = epoch
                print(f"*** GROKKING at epoch {epoch} ({elapsed:.1f}s) ***")

    print("=" * 60)
    total_time = time.time() - start
    print(f"Grokking epoch: {grok_epoch}, Total time: {total_time:.1f}s")
    return grok_epoch, total_time


if __name__ == "__main__":
    benchmark_grokking(noise_std=0.1, max_epochs=3000)
