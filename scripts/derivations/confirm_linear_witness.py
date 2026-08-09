"""Confirm the linear-witness discovery: for the single heavy edge q(T)=1+s,
ANY s > 0 already violates CD(0,inf), witnessed by the IDENTITY function
f(x) = x at site T-1  (Gamma_2(id)(T-1) = -s/4).

Also confirm the strain dipole values and sum rule.
"""
import sympy as sp

f = {k: sp.Symbol(f'f{k}') for k in range(-4, 5)}
s = sp.Symbol('s')
T = 0  # heavy edge {0, 1}

def q(k):  return 1 + s if k == T else 1

def L(g, x):
    return q(x)*(g[x+1]-g[x]) + q(x-1)*(g[x-1]-g[x])

def gamma2_at(x, fv):
    sites = (x-1, x, x+1)
    G  = {y: sp.Rational(1,2)*(L({k: fv[k]*fv[k] for k in fv}, y) - 2*fv[y]*L(fv, y)) for y in sites}
    Lf = {y: L(fv, y) for y in sites}
    gh = {y: fv[y]*Lf[y] for y in sites}
    Lgh  = q(x)*(gh[x+1]-gh[x]) + q(x-1)*(gh[x-1]-gh[x])
    LLfx = q(x)*(Lf[x+1]-Lf[x]) + q(x-1)*(Lf[x-1]-Lf[x])
    GfLf = sp.Rational(1,2)*(Lgh - fv[x]*LLfx - Lf[x]*L(fv, x))
    LG   = q(x)*(G[x+1]-G[x]) + q(x-1)*(G[x-1]-G[x])
    return sp.expand(sp.Rational(1,2)*LG - GfLf)

lin = {k: sp.Integer(k) for k in range(-4, 5)}
print("Gamma_2(id) at sites around heavy edge {0,1}:")
for x in (-2, -1, 0, 1, 2, 3):
    print(f"  x = {x:>2}: {sp.factor(gamma2_at(x, lin))}")
tot = sum(gamma2_at(x, lin) for x in (-1, 0, 1, 2))
print("sum over x in {-1,0,1,2} (x4 = total strain):", sp.factor(sp.expand(4*tot)))
