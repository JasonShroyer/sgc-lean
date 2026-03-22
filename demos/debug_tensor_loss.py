"""Debug: check tensor shapes in the loss computation."""
import torch
import numpy as np
from arc_tensor_logic import encode_pixel_features

g = np.array([[1,1,1,1,1],[1,0,0,0,1],[1,0,0,0,1],[1,0,0,0,1],[1,1,1,1,1]])
t = np.array([[1,1,1,1,1],[1,2,2,2,1],[1,2,2,2,1],[1,2,2,2,1],[1,1,1,1,1]])
p = g.copy()

H, W = 5, 5
C = 10
K = 3
n_ex = 1

feat = np.stack([encode_pixel_features(g)])
feat_t = torch.tensor(feat)
print("feat_t:", feat_t.shape)

inp_oh = np.zeros((1, H, W, C), dtype=np.float32)
tgt_oh = np.zeros((1, H, W, C), dtype=np.float32)
for c in range(C):
    inp_oh[0, :, :, c] = (g == c)
    tgt_oh[0, :, :, c] = (t == c)

res_np = np.stack([(p != t).astype(np.float32)])
res_t = torch.tensor(res_np)
inp_t = torch.tensor(inp_oh)
tgt_t = torch.tensor(tgt_oh)

nf = feat_t.shape[1]
Wt = (torch.randn(nf, K) * 0.1).detach().requires_grad_(True)
b = torch.zeros(K).detach().requires_grad_(True)
V_init = torch.zeros(K, C, C)
for k in range(K):
    V_init[k] = torch.eye(C) * 2.0
V = V_init.detach().requires_grad_(True)

logits = torch.einsum('efhw,fk->ehwk', feat_t, Wt) + b
print("logits:", logits.shape)
P = torch.sigmoid(logits)
print("P:", P.shape)

rules = torch.sigmoid(V)
print("rules:", rules.shape)

mapped = torch.einsum('ehwi,kio->ehwko', inp_t, rules)
print("mapped:", mapped.shape)

pred = torch.einsum('ehwk,ehwko->ehwo', P, mapped)
print("pred:", pred.shape)

pred = pred / (pred.sum(dim=-1, keepdim=True) + 1e-8)
print("pred normalized:", pred.shape)

# Loss components
rw = 1.0 + 4.0 * res_t
print("residual_weight:", rw.shape)
print("rw unsqueeze:", rw.unsqueeze(-1).shape)

inner = rw.unsqueeze(-1) * tgt_t * torch.log(pred + 1e-8)
print("inner:", inner.shape)

wxent = -torch.sum(inner) / (n_ex * H * W)
print("wxent:", wxent.shape, "ndim:", wxent.ndim, "value:", wxent.item())

rs = 0.005 * torch.sum(torch.abs(Wt))
print("rs:", rs.shape, "ndim:", rs.ndim)

P_flat = P.reshape(-1, K)
P_centered = P_flat - P_flat.mean(dim=0, keepdim=True)
P_norm = P_centered / (P_centered.norm(dim=0, keepdim=True) + 1e-8)
gram = torch.mm(P_norm.t(), P_norm) / P_flat.shape[0]
od = gram - torch.eye(K)
rd = 0.01 * torch.sum(od ** 2)
print("rd:", rd.shape, "ndim:", rd.ndim)

tl = wxent + rs + rd
print("total_loss:", tl.shape, "ndim:", tl.ndim)

tl.backward()
print("backward OK!")
print("W grad:", Wt.grad is not None, Wt.grad.shape if Wt.grad is not None else "None")
