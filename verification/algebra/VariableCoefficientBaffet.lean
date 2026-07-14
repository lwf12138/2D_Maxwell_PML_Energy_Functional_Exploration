import Mathlib

/-!
Lean/Mathlib algebra targets for the v5 variable-coefficient Baffet-Debye
analysis.

This file should be checked with Lean 4 and Mathlib.  If an automated Iteris
run reports `lean: command not found`, the usual cause is that the run
environment did not include `$HOME/.elan/bin` in PATH.
-/

section RationalIdentities

theorem debye_primitive_product_identity
    (sigma_x sigma_y tau Pt P q : ℚ) :
    let a := sigma_x + sigma_y
    let b := sigma_x * sigma_y
    let alpha := 1 + 2 * a * tau
    let beta := a + b * tau
    let gamma := a^2 + b * (1 + a * tau)
    (Pt + a * P + b * q) * (tau * Pt + (1 + a * tau) * P + a * q)
      =
    (Pt * (alpha * P + beta * q) + beta * P^2 + gamma * P * q)
      + tau * Pt^2 + tau * (a^2 - b) * P^2 + a * b * q^2 := by
  ring_nf

theorem pq_determinant_identity
    (sigma_x sigma_y tau : ℚ) :
    let a := sigma_x + sigma_y
    let b := sigma_x * sigma_y
    let alpha := 1 + 2 * a * tau
    let beta := a + b * tau
    let gamma := a^2 + b * (1 + a * tau)
    alpha * gamma - beta^2
      =
    b + a * b * tau + 2 * a^3 * tau + b * (2 * a^2 - b) * tau^2 := by
  ring_nf

theorem two_a_sq_sub_b_expansion
    (sigma_x sigma_y : ℚ) :
    let a := sigma_x + sigma_y
    let b := sigma_x * sigma_y
    2 * a^2 - b = 2 * sigma_x^2 + 3 * sigma_x * sigma_y + 2 * sigma_y^2 := by
  ring_nf

theorem grad_multiplier_component_identity
    (u_tx a a_x u u_x : ℚ) :
    u_tx + (a_x * u + a * u_x) = u_tx + a * u_x + u * a_x := by
  ring

end RationalIdentities

section RealAbsorption

theorem absorption_sum_of_squares_identity
    (m_u m_lambda g u lambda : ℝ) :
    4 * m_u * (m_u * u^2 + m_lambda * lambda^2 - g * u * lambda)
      =
    (2 * m_u * u - g * lambda)^2
      + (4 * m_u * m_lambda - g^2) * lambda^2 := by
  ring

theorem absorption_quadratic_nonpos
    {m_u m_lambda g u lambda : ℝ}
    (hm_u : 0 < m_u)
    (_hm_lambda : 0 ≤ m_lambda)
    (hg : g^2 ≤ 4 * m_u * m_lambda) :
    -m_u * u^2 - m_lambda * lambda^2 + g * u * lambda ≤ 0 := by
  have hcoef : 0 ≤ 4 * m_u * m_lambda - g^2 := by
    nlinarith
  have hsos : 0 ≤
      (2 * m_u * u - g * lambda)^2
        + (4 * m_u * m_lambda - g^2) * lambda^2 := by
    have h1 : 0 ≤ (2 * m_u * u - g * lambda)^2 := sq_nonneg _
    have h2 : 0 ≤ (4 * m_u * m_lambda - g^2) * lambda^2 :=
      mul_nonneg hcoef (sq_nonneg lambda)
    nlinarith
  have hid :
      4 * m_u * (m_u * u^2 + m_lambda * lambda^2 - g * u * lambda)
        =
      (2 * m_u * u - g * lambda)^2
        + (4 * m_u * m_lambda - g^2) * lambda^2 := by
    ring
  have hmul : 0 ≤
      4 * m_u * (m_u * u^2 + m_lambda * lambda^2 - g * u * lambda) := by
    rw [hid]
    exact hsos
  have hpos : 0 < 4 * m_u := by
    nlinarith
  have hmul_comm :
      0 ≤ (m_u * u^2 + m_lambda * lambda^2 - g * u * lambda) * (4 * m_u) := by
    nlinarith [hmul]
  have hnonneg :
      0 ≤ m_u * u^2 + m_lambda * lambda^2 - g * u * lambda :=
    nonneg_of_mul_nonneg_left hmul_comm hpos
  nlinarith

end RealAbsorption
