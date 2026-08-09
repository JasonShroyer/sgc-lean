"""Verify the exact discrete operator-strain decomposition and derive the
cold-water certificates.

Claimed identity (symmetric weights q, lineGen convention), at every x:

Gamma_2(f)(x) = q(x-1)q(x-2)/4 * D(x-1)^2
             + q(x-1)q(x)/2   * D(x)^2
             + q(x)q(x+1)/4   * D(x+1)^2
             + q(x-1)/4 * strainL(x) * (f(x)-f(x-1))^2
             + q(x)/4   * strainR(x) * (f(x+1)-f(x))^2

with D(y) = f(y-1) - 2f(y) + f(y+1) (second difference),
     strainL(x) = 4q(x-1) - 3q(x) - q(x-2)
     strainR(x) = 4q(x)   - 3q(x-1) - q(x+1).

Then: heavy edge q(0)=1+s, all else 1 -> check global CD(0,inf) at s=1/2 by
LDL/SOS of the Gamma_2 forms at x = -1, 0, 1, 2 (other x are flat-stencil).
"""
import sympy as sp

f = {k: sp.Symbol(f'f{k}') for k in range(-3, 4)}
q = {k: sp.Symbol(f'q{k}') for k in range(-4, 4)}

def L(g, x):
    return q[x]*(g[x+1]-g[x]) + q[x-1]*(g[x-1]-g[x])

def gamma2_at(x):
    sites = (x-1, x, x+1)
    G  = {y: sp.expand(sp.Rational(1,2)*(L({k: f[k]*f[k] for k in f}, y)
            - 2*f[y]*L(f, y))) for y in sites}
    Lf = {y: sp.expand(L(f, y)) for y in sites}
    gh = {y: f[y]*Lf[y] for y in sites}
    Lgh  = q[x]*(gh[x+1]-gh[x]) + q[x-1]*(gh[x-1]-gh[x])
    LLfx = q[x]*(Lf[x+1]-Lf[x]) + q[x-1]*(Lf[x-1]-Lf[x])
    GfLf = sp.Rational(1,2)*(Lgh - f[x]*LLfx - Lf[x]*L(f, x))
    LG   = q[x]*(G[x+1]-G[x]) + q[x-1]*(G[x-1]-G[x])
    return sp.expand(sp.Rational(1,2)*LG - GfLf)

def D(y):  return f[y-1] - 2*f[y] + f[y+1]
def sL(x): return 4*q[x-1] - 3*q[x] - q[x-2]
def sR(x): return 4*q[x] - 3*q[x-1] - q[x+1]

def claimed(x):
    return (q[x-1]*q[x-2]/4 * D(x-1)**2 + q[x-1]*q[x]/2 * D(x)**2
            + q[x]*q[x+1]/4 * D(x+1)**2
            + q[x-1]/4 * sL(x) * (f[x]-f[x-1])**2
            + q[x]/4  * sR(x) * (f[x+1]-f[x])**2)

print("=== identity check at x = 0 ===")
print("residual:", sp.simplify(gamma2_at(0) - claimed(0)))

# heavy edge: q0 = 1+s, else 1; global CD(0,inf) at s = 1/2?
s = sp.Symbol('s')
heavy = {q[k]: (1 + s if k == 0 else 1) for k in q}

u = sp.symbols('u1 u2 u3 u4')
for x in (-1, 0, 1, 2):
    G2 = sp.expand(gamma2_at(x).subs(heavy))
    fs = {x-2: 0}
    for i, k in enumerate(range(x-1, x+3)):
        fs[k] = fs[k-1] + u[i]
    G2u = sp.expand(G2.subs({f[k]: fs[k] for k in fs if k in f}))
    Q = sp.Matrix(4,4, lambda i,j: sp.Rational(1,2)*sp.diff(G2u, u[i], u[j]))
    Qh = Q.subs({s: sp.Rational(1,2)})
    # LDL via successive Schur complements (rational SOS certificate if PSD)
    M_ = sp.Matrix(Qh); n = 4; diag = []; ok = True
    Mk = sp.Matrix(M_)
    L_rows = []
    for k in range(n):
        d = sp.nsimplify(Mk[0,0])
        diag.append(d)
        if d == 0:
            if any(Mk[0,j] != 0 for j in range(1, Mk.shape[1])): ok = False; break
            Mk = Mk[1:,1:]; L_rows.append(None); continue
        if d < 0: ok = False; break
        row = Mk[0,:] / d
        L_rows.append(row)
        Mk = (Mk[1:,1:] - Mk[1:,0]*Mk[0,1:]/d).applyfunc(sp.nsimplify)
    print(f"\n=== x = {x}, s = 1/2: LDL diagonal = {diag}  PSD: {ok} ===")
