#!/usr/bin/env python3
"""Symbolic checks for the Baffet-Debye 2D Maxwell-PML energy.

The checks are intentionally algebraic.  Positivity is reduced to displayed
principal minors, Schur complements, and sums of nonnegative monomials under
the assumptions used in the TeX artifact:

    sigma_x >= 0, sigma_y >= 0, a = sigma_x + sigma_y > 0,
    b = sigma_x sigma_y, tau > 0, e > 0, mu > 0, chi > 0.
"""

from __future__ import annotations

import sympy as sp


def check_zero(name: str, expr: sp.Expr) -> None:
    reduced = sp.factor(sp.together(sp.expand(expr)))
    print(f"{name}: {reduced}")
    assert reduced == 0, name


def check_equal(name: str, lhs: sp.Expr, rhs: sp.Expr) -> None:
    check_zero(name, lhs - rhs)


sx, sy, tau, chi, mu, e, s, rho, ky = sp.symbols(
    "sigma_x sigma_y tau chi mu e s rho k_y", positive=True
)
Pt, P, q = sp.symbols("P_t P q")

a = sx + sy
b = sx * sy

alpha = 1 + 2 * a * tau
beta = a + b * tau
gamma = a**2 + b * (1 + a * tau)

print("=== Energy matrix M: Debye primitive P,q block ===")
M_pq = sp.Matrix([[alpha, beta], [beta, gamma]])
minor_1 = sp.factor(M_pq[:1, :1].det())
minor_2 = sp.factor(M_pq.det())
minor_2_sum = b + a * b * tau + 2 * a**3 * tau + b * (2 * a**2 - b) * tau**2
print(f"alpha = {minor_1}")
print(f"det(M_pq) = {minor_2}")
check_equal("det(M_pq) sum-of-positive-terms form", minor_2, minor_2_sum)
print(f"2*a^2-b = {sp.expand(2*a**2 - b)}")

print("\n=== Schur complement and completing the square ===")
schur = sp.factor(gamma - beta**2 / alpha)
print(f"Schur complement gamma - beta^2/alpha = {schur}")
completed_square = alpha * (P + beta / alpha * q) ** 2 + (
    gamma - beta**2 / alpha
) * q**2
quadratic = alpha * P**2 + 2 * beta * P * q + gamma * q**2
check_equal("P,q completed-square identity", completed_square, quadratic)

print("\n=== Debye primitive product identity ===")
lhs = (Pt + a * P + b * q) * (tau * Pt + (1 + a * tau) * P + a * q)
energy_derivative_part = (
    Pt * (alpha * P + beta * q) + beta * P**2 + gamma * P * q
)
rhs = (
    energy_derivative_part
    + tau * Pt**2
    + tau * (a**2 - b) * P**2
    + a * b * q**2
)
check_equal("Debye primitive multiplier expansion", lhs, rhs)
print(f"a^2-b = {sp.expand(a**2 - b)}")

print("\n=== Dissipation matrix Q nonnegative entries ===")
q_lambda_x = sp.factor(sx * (1 + sx / a))
q_lambda_y = sp.factor(sy * (1 + sy / a))
q_grad = sp.factor(b / a)
q_u = sp.factor(mu * e * a * b)
q_Pt = sp.factor(mu * tau / chi)
q_P = sp.factor(mu * tau * (a**2 - b) / chi)
q_q = sp.factor(mu * a * b / chi)
for name, value in [
    ("lambda_x", q_lambda_x),
    ("lambda_y", q_lambda_y),
    ("grad_u", q_grad),
    ("u", q_u),
    ("P_t", q_Pt),
    ("P", q_P),
    ("q", q_q),
]:
    print(f"Q[{name}] = {value}")

print("\n=== v2 admittance mismatch identity ===")
eps_D = sp.symbols("epsilon_D")
eps_D_expr = e + chi / (1 + tau * s)
eps_rho_expr = e + chi / (1 + tau * (s + rho))
Y0_sq = eps_D_expr / mu + ky**2 / (mu**2 * s**2)
Yrho_sq = eps_rho_expr / mu + ky**2 / (mu**2 * s * (s + rho))
mismatch = -rho * (
    chi * tau / (mu * (1 + tau * s) * (1 + tau * (s + rho)))
    + ky**2 / (mu**2 * s**2 * (s + rho))
)
check_equal("v2 squared-admittance mismatch", Yrho_sq - Y0_sq, mismatch)

print("\n=== standard stretched-coordinate matching identity ===")
Sx, nu0 = sp.symbols("S_x nu_0", nonzero=True)
nu_plus = Sx * nu0
Y_plus = (nu_plus / Sx) / (mu * s)
Y_0 = nu0 / (mu * s)
check_equal("stretched-coordinate admittance", Y_plus, Y_0)

print("\nAll SymPy algebra checks passed.")
