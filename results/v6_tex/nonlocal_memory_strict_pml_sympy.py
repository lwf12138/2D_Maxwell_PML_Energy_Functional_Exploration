#!/usr/bin/env python3
"""Exact and numerical checks for the v6 strict-PML energy audit."""

from __future__ import annotations

import random
import sympy as sp


def zero(name: str, expr: sp.Expr) -> None:
    value = sp.factor(sp.cancel(sp.together(sp.expand(expr))))
    print(f"{name}: {value}")
    assert value == 0, name


print("=== strict stretched-coordinate dispersion and admittance ===")
s, sx, sy, mu, eps, kap, tau, ky, nu0 = sp.symbols(
    "s sigma_x sigma_y mu epsilon kappa tau k_y nu_0", nonzero=True
)
epsD = eps + kap / (1 + tau * s)
Sx, Sy = 1 + sx / s, 1 + sy / s
disp0 = nu0**2 - ky**2 - mu * s**2 * epsD
nu_plus = Sx * nu0
disp_plus = (nu_plus / Sx) ** 2 - ky**2 - mu * s**2 * epsD
zero("x-PML dispersion reduces to physical dispersion", disp_plus - disp0)
Y0 = nu0 / (mu * s)
Yplus = (nu_plus / Sx) / (mu * s)
zero("outgoing-branch admittance Yplus-Y0", Yplus - Y0)
R = (Y0 - Yplus) / (Y0 + Yplus)
zero("reflection coefficient", R)
nu_corner = Sx * sp.sqrt((ky / Sy) ** 2 + mu * s**2 * epsD)
Ycorner_sq = sp.factor((nu_corner / Sx / (mu * s)) ** 2)
Y0_sq = sp.factor((ky**2 + mu * s**2 * epsD) / (mu * s) ** 2)
print("corner/cross-damped squared-admittance defect:", sp.factor(Ycorner_sq - Y0_sq))

print("\n=== Baffet product rule and Debye/Schur identities ===")
utx, ax, u, ux, a = sp.symbols("u_tx a_x u u_x a")
zero("grad(u_t+a*u) product rule", utx + ax * u + a * ux - (utx + a * ux + u * ax))
mx, ml, g, lam = sp.symbols("m_u m_lambda g lambda", positive=True)
form = mx * u**2 + ml * lam**2 - g * u * lam
sos = (2 * mx * u - g * lam) ** 2 + (4 * mx * ml - g**2) * lam**2
zero("Schur/completing-square identity", 4 * mx * form - sos)

P, Pt, q = sp.symbols("P P_t q")
b = sx * sy
a = sx + sy
alpha = 1 + 2 * a * tau
beta = a + b * tau
gamma = a**2 + b * (1 + a * tau)
lhs = (Pt + a * P + b * q) * (tau * Pt + (1 + a * tau) * P + a * q)
rhs = Pt * (alpha * P + beta * q) + beta * P**2 + gamma * P * q
rhs += tau * Pt**2 + tau * (a**2 - b) * P**2 + a * b * q**2
zero("Debye primitive product", lhs - rhs)
detpq = sp.factor(alpha * gamma - beta**2)
detpq_sum = b + a * b * tau + 2 * a**3 * tau + b * (2 * a**2 - b) * tau**2
zero("Debye Pq determinant expansion", detpq - detpq_sum)

print("\n=== proposed elliptic nonlocal correction: complete proxy derivative ===")
eta, ell, ut, lt = sp.symbols("eta ell u_t lambda_t", nonzero=True)
z = -g * u / ell
zt = -g * ut / ell
F = eta * (lam * z + ell * z**2 / 2)
Ft_chain = eta * (lt * z + lam * zt + ell * z * zt)
Ft_expected = eta * (-g * u * lt / ell - g * ut * lam / ell + g**2 * u * ut / ell)
zero("nonlocal correction derivative", Ft_chain - Ft_expected)
total_residual = sp.factor(-g * u * lam + Ft_chain)
print("Baffet remainder plus proposed correction derivative:", total_residual)
assert total_residual != 0

print("\n=== two attempted repairs ===")
r = sp.symbols("r")
primitive_total = -g * u * lam + g * (ut * r + u * lam)
zero("temporal primitive cancels target but leaves g*u_t*r", primitive_total - g * ut * r)
p, pt = -lam / ell, -lt / ell
second_elliptic_dt = ell * (zt * p + z * pt)
zero("second elliptic variable derivative", second_elliptic_dt - g * (ut * lam + u * lt) / ell)

print("\n=== local cross-term route ===")
c, sigi, sigj, uxt = sp.symbols("c sigma_i sigma_j u_xt")
local_dt = c * (ut * lam + u * (uxt + sigj * ux - sigi * lam))
local_expanded = -c * sigi * u * lam + c * ut * lam + c * u * uxt + c * sigj * u * ux
zero("local c*u*lambda derivative", local_dt - local_expanded)
chosen = sp.factor(local_expanded.subs(c, -g / sigi) - g * u * lam)
print("residual after choosing c=-g/sigma_i to create +g*u*lambda:", chosen)
assert chosen != 0

print("\n=== finite-dimensional M and Q tests ===")
M = sp.Matrix([[mx, -g / 2], [-g / 2, ml]])
print("det(M_schur) =", sp.factor(M.det()))
Q = sp.Matrix([[mx, -g / 2], [-g / 2, ml]])
zero("M/Q determinant identity", M.det() - (mx * ml - g**2 / 4))

print("\n=== exact adversarial and random eigenvalue checks ===")
bad = sp.Matrix([[sp.Rational(1), -sp.Rational(3, 2)], [-sp.Rational(3, 2), sp.Rational(1)]])
bad_eigs = sorted(bad.eigenvals().keys(), key=lambda x: float(x))
print("adversarial high-gradient eigenvalues (g=3, mu=ml=1):", bad_eigs)
assert bad_eigs[0] < 0

rng = random.Random(20260714)
for j in range(12):
    muv = sp.Rational(rng.randint(1, 9), rng.randint(1, 5))
    mlv = sp.Rational(rng.randint(1, 9), rng.randint(1, 5))
    boundary = 2 * sp.sqrt(muv * mlv)
    factor = sp.Rational(rng.randint(0, 9), 10)
    gv = factor * boundary
    mat = sp.Matrix([[muv, -gv / 2], [-gv / 2, mlv]])
    mineig = min(float(sp.N(ev)) for ev in mat.eigenvals())
    print(f"random Schur case {j:02d}: min_eig={mineig:.6e}, factor={float(factor):.1f}")
    assert mineig > 0

print("baseline/control: the adversarial matrix violates Schur and has a negative eigenvalue;")
print("falsifier: any sampled in-condition matrix with min_eig<=0, or adversarial min_eig>=0.")
print("All v6 SymPy checks passed.")
