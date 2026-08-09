"""Derive the exact discrete Gamma_2 identity for the drifted line generator.

Generator: (L f)(x) = p(x)(f(x+1)-f(x)) + m(x)(f(x-1)-f(x))
  symmetric part nu(x) = (p+m)/2, drift b(x) = p(x)-m(x).

Gamma(f,g)  = 1/2 (L(fg) - f Lg - g Lf)
Gamma_2(f,f) = 1/2 (L Gamma(f,f) - 2 Gamma(f, Lf))

Gamma_2 at x=0 depends on f(-2..2) and rates at -1, 0, 1 (p_{-1},p_0,p_1,m_{-1},m_0,m_1).
Goal: canonical quadratic form; constant-rate SOS check; strain extraction.
"""
import sympy as sp

# function values f(-2), ..., f(2)
f = {k: sp.Symbol(f'f{k}') for k in range(-2, 3)}
# rates at sites -1, 0, 1 (only these can enter)
p = {k: sp.Symbol(f'p{k}') for k in range(-2, 3)}
m = {k: sp.Symbol(f'm{k}') for k in range(-2, 3)}

def L(g, x):        # g: dict site -> expr
    return p[x]*(g[x+1]-g[x]) + m[x]*(g[x-1]-g[x])

def gamma_at(g, h, x):
    gh = {k: g[k]*h[k] for k in g}
    return sp.Rational(1,2)*(L(gh,x) - g[x]*L(h,x) - h[x]*L(g,x))

# Gamma(f,f) as a site function on {-1,0,1}
G = {x: sp.expand(gamma_at(f, f, x)) for x in (-1,0,1)}
Lf = {x: sp.expand(L(f,x)) for x in (-1,0,1)}

# Gamma(f, Lf) at 0 needs (f*Lf) at -1,0,1 and Lf at -1,0,1 -> needs Lf at -1,0,1 only
def gamma_fLf_at0():
    gh = {x: f[x]*Lf[x] for x in (-1,0,1)}
    # L(gh, 0) uses gh at -1,0,1
    Lgh = p[0]*(gh[1]-gh[0]) + m[0]*(gh[-1]-gh[0])
    LLf0 = p[0]*(Lf[1]-Lf[0]) + m[0]*(Lf[-1]-Lf[0])
    return sp.Rational(1,2)*(Lgh - f[0]*LLf0 - Lf[0]*L(f,0))

LG0 = p[0]*(G[1]-G[0]) + m[0]*(G[-1]-G[0])
Gamma2 = sp.expand(sp.Rational(1,2)*LG0 - gamma_fLf_at0())
Gamma2 = sp.expand(Gamma2)

print("=== which rates appear ===")
print(sorted({s.name for s in Gamma2.free_symbols if s.name[0] in 'pm'}))

# ---- constant rates: p=P, m=M everywhere ----
P, M = sp.symbols('P M', positive=True)
G2c = Gamma2.subs({p[k]: P for k in p} | {m[k]: M for k in m})
G2c = sp.expand(G2c)

# express in second differences D_{-1}, D_0, D_1 and first differences
D = {k: f[k-1] - 2*f[k] + f[k+1] for k in (-1, 0, 1)}
u = {k: f[k+1] - f[k] for k in (-2, -1, 0, 1)}  # first differences

# try SOS ansatz: a*D(-1)^2 + b*D0^2 + c*D1^2 + cross terms in first diffs
print("\n=== constant-rate Gamma_2 (expanded) ===")
print(sp.simplify(G2c))

# canonical: as quadratic form in (f-2, f-1, f0, f1, f2); check PSD symbolically at samples
vars5 = [f[k] for k in range(-2,3)]
Qc = sp.Matrix(5,5, lambda i,j: sp.Rational(1,2)*sp.diff(G2c, vars5[i], vars5[j]))
print("\n=== constant-rate quadratic form eigen-test at P=2, M=1 and P=1, M=1 ===")
for (Pv,Mv) in [(2,1),(1,1),(5,1),(1,5),(3,2)]:
    Qn = Qc.subs({P:Pv, M:Mv})
    ev = [sp.nsimplify(e, rational=False) for e in Qn.eigenvals()]
    evn = [complex(sp.N(e)).real for e in Qn.eigenvals()]
    print(f"P={Pv}, M={Mv}: min eig ~ {min(evn):.6f}")

# try to write constant-rate G2 as combination of D squares and (D cross first-diff)
a,b,c,d,e,g_,h_ = sp.symbols('a b c d e g h')
ans = (a*D[-1]**2 + b*D[0]**2 + c*D[1]**2 + d*D[-1]*D[0] + e*D[0]*D[1] + g_*D[-1]*D[1])
sol = sp.solve(sp.Poly(sp.expand(G2c - ans), *vars5).coeffs(), [a,b,c,d,e,g_], dict=True)
print("\n=== constant-rate: representation in second differences only? ===")
print(sol if sol else "NO pure second-difference representation")
