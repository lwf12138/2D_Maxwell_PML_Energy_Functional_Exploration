import Mathlib

/-!
Lean/Mathlib algebra targets for the Baffet-Debye Maxwell-PML energy.

This file is intended to be checked in an environment with Lean 4 and Mathlib.
If an automated run reports `lean: command not found`, the usual cause is that
the run environment did not include `$HOME/.elan/bin` in PATH.  If Lean is found
but this file reports `unknown module prefix 'Mathlib'`, run it inside a
Lake/Mathlib project.
-/

open scoped BigOperators

section Algebra

variable {R : Type*} [LinearOrderedRing R]

theorem two_by_two_quadratic_complete_square
    (a b c x y : R) (ha : a ≠ 0) :
    a * (x + b / a * y)^2 + (c - b^2 / a) * y^2
      = a * x^2 + 2 * b * x * y + c * y^2 := by
  field_simp [ha]
  ring

theorem two_by_two_positive_conditions
    {a b c : R} (ha : 0 < a) (hdet : 0 < a * c - b^2) :
    0 < c := by
  have ha_nonneg : 0 < a := ha
  nlinarith [mul_pos ha (show 0 < (a * c - b^2) / a by positivity)]

theorem debye_primitive_product_identity
    (sigma_x sigma_y tau Pt P q : R) :
    let A := sigma_x + sigma_y
    let B := sigma_x * sigma_y
    let alpha := 1 + 2 * A * tau
    let beta := A + B * tau
    let gamma := A^2 + B * (1 + A * tau)
    (Pt + A * P + B * q) * (tau * Pt + (1 + A * tau) * P + A * q)
      =
    (Pt * (alpha * P + beta * q) + beta * P^2 + gamma * P * q)
      + tau * Pt^2 + tau * (A^2 - B) * P^2 + A * B * q^2 := by
  intros
  ring

theorem pq_determinant_identity
    (sigma_x sigma_y tau : R) :
    let A := sigma_x + sigma_y
    let B := sigma_x * sigma_y
    let alpha := 1 + 2 * A * tau
    let beta := A + B * tau
    let gamma := A^2 + B * (1 + A * tau)
    alpha * gamma - beta^2
      =
    B + A * B * tau + 2 * A^3 * tau + B * (2 * A^2 - B) * tau^2 := by
  intros
  ring

theorem v2_admittance_mismatch_identity
    (e chi tau mu s rho ky : R) :
    let epsD := e + chi / (1 + tau * s)
    let epsRho := e + chi / (1 + tau * (s + rho))
    epsRho / mu + ky^2 / (mu^2 * s * (s + rho))
      - (epsD / mu + ky^2 / (mu^2 * s^2))
      =
    -rho * (chi * tau / (mu * (1 + tau * s) * (1 + tau * (s + rho)))
      + ky^2 / (mu^2 * s^2 * (s + rho))) := by
  intros
  ring

end Algebra
