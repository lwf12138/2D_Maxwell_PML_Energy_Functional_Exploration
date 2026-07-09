#!/usr/bin/env python3
"""Symbolic checks for the variable-coefficient Baffet-Debye analysis.

The script verifies the algebra used in the v5 report:

* Debye primitive multiplier identity and P,q determinant.
* 2 a^2 - b expansion for a = sigma_x + sigma_y, b = sigma_x sigma_y.
* Variable-coefficient multiplier gradient term.
* Small-gradient absorption Schur complement.
* Port-model Maxwell cross-term cancellation.
* Port-model Laplace-Fourier admittance mismatch.
"""

from __future__ import annotations

import sympy as sp


def reduced(expr: sp.Expr) -> sp.Expr:
    return sp.factor(sp.cancel(sp.together(sp.expand(expr))))


def check_zero(name: str, expr: sp.Expr) -> None:
    value = reduced(expr)
    print(f"{name}: {value}")
    assert value == 0, name


def check_equal(name: str, lhs: sp.Expr, rhs: sp.Expr) -> None:
    check_zero(name, lhs - rhs)


sx, sy, tau = sp.symbols("sigma_x sigma_y tau", positive=True)
Pt, P, q = sp.symbols("P_t P q")

a = sx + sy
b = sx * sy
alpha = 1 + 2 * a * tau
beta = a + b * tau
gamma = a**2 + b * (1 + a * tau)

print("=== Debye primitive algebra ===")
lhs = (Pt + a * P + b * q) * (tau * Pt + (1 + a * tau) * P + a * q)
energy_derivative_part = Pt * (alpha * P + beta * q) + beta * P**2 + gamma * P * q
rhs = (
    energy_derivative_part
    + tau * Pt**2
    + tau * (a**2 - b) * P**2
    + a * b * q**2
)
check_equal("Debye primitive product identity", lhs, rhs)

det_pq = alpha * gamma - beta**2
det_sum = b + a * b * tau + 2 * a**3 * tau + b * (2 * a**2 - b) * tau**2
check_equal("P,q determinant identity", det_pq, det_sum)
check_equal(
    "2*a^2-b nonnegative expansion",
    2 * a**2 - b,
    2 * sx**2 + 3 * sx * sy + 2 * sy**2,
)
print(f"a^2-b = {sp.expand(a**2 - b)}")

print("\n=== Variable-coefficient multiplier term ===")
utx, u, ux, ax = sp.symbols("u_tx u u_x a_x")
check_equal(
    "component product-rule expansion for grad(u_t+a*u)",
    utx + ax * u + a * ux,
    utx + a * ux + u * ax,
)

print("\n=== Small-gradient absorption Schur complement ===")
m_u, m_lam, g, lam = sp.symbols("m_u m_lambda g lambda", positive=True)
positive_form = m_u * u**2 + m_lam * lam**2 - g * u * lam
sos_rhs = (2 * m_u * u - g * lam) ** 2 + (4 * m_u * m_lam - g**2) * lam**2
check_equal(
    "absorption sum-of-squares identity",
    4 * m_u * positive_form,
    sos_rhs,
)
schur_condition = sp.factor(m_u * m_lam - (g / 2) ** 2)
print(f"Schur complement m_u*m_lambda-(g/2)^2 = {schur_condition}")
print("Thus g^2 <= 4*m_u*m_lambda is exactly the 2x2 absorption condition.")

print("\n=== Port-model energy cross-term cancellation ===")
E, Wx, Wy = sp.symbols("E W_x W_y")
Ex, Ey, Wxy, Wyx = sp.symbols("E_x E_y W_x_y W_y_x")
maxwell_cross = E * (Wyx - Wxy) - Wx * Ey + Wy * Ex
boundary_divergence = Ex * Wy + E * Wyx - Ey * Wx - E * Wxy
check_equal(
    "port Maxwell cross terms equal div(E*W_y, -E*W_x)",
    maxwell_cross,
    boundary_divergence,
)

kappa = sp.symbols("kappa", positive=True)
check_equal(
    "Debye port product identity",
    ((P + tau * Pt) / kappa) * Pt,
    (sp.Rational(1, 2) / kappa) * (2 * P * Pt) + tau * Pt**2 / kappa,
)

print("\n=== Strict stretched-coordinate admittance ===")
mu, eps, s, sig, ky, nu0 = sp.symbols(
    "mu epsilon s sigma k_y nu_0", positive=True
)
eps_D = eps + kappa / (1 + tau * s)
Sx = 1 + sig / s
nu_plus = Sx * nu0
Y_sc = (nu_plus / Sx) / (mu * s)
Y0 = nu0 / (mu * s)
check_equal("strict stretched-coordinate admittance", Y_sc, Y0)

print("\n=== Port-model Laplace-Fourier mismatch ===")
sigma_E = sp.symbols("sigma_E")
Y0_sq = eps_D / mu + ky**2 / (mu**2 * s**2)
Yport_sq = (s * eps_D + eps * sigma_E) / (mu * (s + sig)) + ky**2 / (
    mu**2 * s * (s + sig)
)
port_mismatch = (eps * sigma_E - sig * eps_D) / (mu * (s + sig)) - sig * ky**2 / (
    mu**2 * s**2 * (s + sig)
)
check_equal("port squared-admittance mismatch", Yport_sq - Y0_sq, port_mismatch)

sigma_E_normal = sig * eps_D / eps
check_equal(
    "port normal-incidence matching with dispersive sigma_E",
    port_mismatch.subs({sigma_E: sigma_E_normal, ky: 0}),
    0,
)
oblique_residual = reduced(port_mismatch.subs({sigma_E: sigma_E_normal}))
print(f"oblique residual after normal-incidence sigma_E choice = {oblique_residual}")
assert oblique_residual == reduced(-sig * ky**2 / (mu**2 * s**2 * (s + sig)))

print("\nAll variable-coefficient Baffet SymPy checks passed.")
