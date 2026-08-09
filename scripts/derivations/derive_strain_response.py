"""Strain response: symmetric edge weights q (lineGen convention:
p(x) = q(x) forward across edge {x,x+1}, m(x) = q(x-1) backward across {x-1,x}).

1. Single-edge strain: q = 1 except q(0) = 1 + s. Gamma_2 at 0 on the step
   witness wit = (-1, 0, 1, 1, 1); exact polynomial in s, sign threshold.
2. Worst case: minimize Gamma_2 quadratic form at 0 over f for given s
   (min eigenvalue of the form restricted to difference space).
3. General variable q: exact identity in first-difference basis to expose
   the strain structure.
"""
import sympy as sp

f = {k: sp.Symbol(f'f{k}') for k in range(-2, 3)}
q = {k: sp.Symbol(f'q{k}') for k in range(-3, 3)}   # edge {k, k+1}

def L(g, x):
    return q[x]*(g[x+1]-g[x]) + q[x-1]*(g[x-1]-g[x])

def gamma_at(g, h, x):
    gh = {k: g[k]*h[k] for k in g}
    return sp.Rational(1,2)*(L(gh,x) - g[x]*L(h,x) - h[x]*L(g,x))

G  = {x: sp.expand(gamma_at(f, f, x)) for x in (-1,0,1)}
Lf = {x: sp.expand(L(f,x)) for x in (-1,0,1)}
gh = {x: f[x]*Lf[x] for x in (-1,0,1)}
Lgh  = q[0]*(gh[1]-gh[0]) + q[-1]*(gh[-1]-gh[0])
LLf0 = q[0]*(Lf[1]-Lf[0]) + q[-1]*(Lf[-1]-Lf[0])
GfLf = sp.Rational(1,2)*(Lgh - f[0]*LLf0 - Lf[0]*L(f,0))
LG0  = q[0]*(G[1]-G[0]) + q[-1]*(G[-1]-G[0])
Gamma2 = sp.expand(sp.Rational(1,2)*LG0 - GfLf)

print("=== rates entering Gamma_2 at 0 (symmetric weights) ===")
print(sorted({s.name for s in Gamma2.free_symbols if s.name.startswith('q')}))

s = sp.Symbol('s')
one = {q[k]: 1 for k in q}
heavy = dict(one); heavy[q[0]] = 1 + s

wit = {-2: -1, -1: 0, 0: 1, 1: 1, 2: 1}
G2_wit = sp.expand(Gamma2.subs(heavy).subs({f[k]: wit[k] for k in f}))
print("\n=== Gamma_2(wit)(0) with q(0) = 1+s ===")
print(sp.factor(G2_wit))
print("roots:", sp.solve(G2_wit, s))

# worst-case over f: min eigenvalue of the form (mod constants) vs s
vars5 = [f[k] for k in range(-2,3)]
G2s = sp.expand(Gamma2.subs(heavy))
Q = sp.Matrix(5,5, lambda i,j: sp.Rational(1,2)*sp.diff(G2s, vars5[i], vars5[j]))
print("\n=== min eigenvalue of heavy-edge form vs s ===")
for sv in [0, sp.Rational(1,2), 1, sp.Rational(3,2), 2, 3, 4]:
    Qn = Q.subs({s: sv})
    evn = [complex(sp.N(e)).real for e in Qn.eigenvals()]
    print(f"s = {sv}: min eig ~ {min(evn):+.6f}")

# threshold: find critical s where form loses PSD (det of difference-space form)
u = [f[k+1]-f[k] for k in (-2,-1,0,1)]
# build form in u-basis: substitute f-2 = 0 (gauge), f solved from u
subs_gauge = {f[-2]: 0, f[-1]: u[0]*0 + sp.Symbol('u1'),}
# simpler: parametrize f by partial sums of u
u1,u2,u3,u4 = sp.symbols('u1 u2 u3 u4')
fs = {-2: 0, -1: u1, 0: u1+u2, 1: u1+u2+u3, 2: u1+u2+u3+u4}
G2u = sp.expand(G2s.subs({f[k]: fs[k] for k in f}))
Qu = sp.Matrix(4,4, lambda i,j: sp.Rational(1,2)*sp.diff(G2u, [u1,u2,u3,u4][i], [u1,u2,u3,u4][j]))
dets = [sp.factor(Qu[:k,:k].det()) for k in range(1,5)]
print("\n=== leading principal minors of u-space form (PSD iff all >= 0) ===")
for k,dd in enumerate(dets,1):
    print(f"minor {k}: {dd}")
print("critical s (smallest positive root where PSD fails):")
for k,dd in enumerate(dets,1):
    rr = sp.solve(dd, s)
    print(f"  minor {k} roots: {rr}")

# general variable-q identity in u-basis (strain structure)
G2gen_u = sp.expand(Gamma2.subs({f[k]: fs[k] for k in f}))
Qgen = sp.Matrix(4,4, lambda i,j: sp.Rational(1,2)*sp.diff(G2gen_u, [u1,u2,u3,u4][i], [u1,u2,u3,u4][j]))
print("\n=== general symmetric-weight Gamma_2 in first-difference basis (u1..u4 = f-diffs from left) ===")
sp.pprint(sp.simplify(Qgen))
