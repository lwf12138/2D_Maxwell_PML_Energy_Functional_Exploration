import Mathlib

/-!
Algebra certificates for the v6 strict Maxwell--Debye PML audit.
No PDE theorem is claimed here: the scalar variables encode the indicated
finite-dimensional proxy blocks of the report.
-/

section SchurAbsorption

theorem schur_square_identity
    (mu ml g u l : ℝ) :
    4 * mu * (mu * u^2 + ml * l^2 - g * u * l) =
      (2 * mu * u - g * l)^2 + (4 * mu * ml - g^2) * l^2 := by
  ring

theorem schur_absorption
    {mu ml g u l : ℝ} (hmu : 0 < mu) (hml : 0 ≤ ml)
    (hg : g^2 ≤ 4 * mu * ml) :
    -mu * u^2 - ml * l^2 + g * u * l ≤ 0 := by
  have hc : 0 ≤ 4 * mu * ml - g^2 := by nlinarith
  have hs : 0 ≤ (2 * mu * u - g * l)^2 +
      (4 * mu * ml - g^2) * l^2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hc (sq_nonneg _))
  nlinarith [schur_square_identity mu ml g u l]

end SchurAbsorption

section NonlocalProxy

/- In the scalar elliptic proxy, ell*z = -g*u and ell*zt = -g*ut.
   F = eta*(l*z + ell*z^2/2) is the PDF's proposed correction. -/
theorem nonlocal_energy_expansion
    (eta ell g u l : ℝ) (hell : ell ≠ 0) :
    let z := -(g * u) / ell
    eta * (l * z + ell * z^2 / 2) =
      eta * (-(g * u * l) / ell + g^2 * u^2 / (2 * ell)) := by
  dsimp
  field_simp
  ring

theorem nonlocal_derivative_residual
    (eta ell g u ut l lt : ℝ) (hell : ell ≠ 0) :
    let z := -(g * u) / ell
    let zt := -(g * ut) / ell
    eta * (lt * z + l * zt + ell * z * zt) =
      eta * (-(g * u * lt) / ell - (g * ut * l) / ell
        + (g^2 * u * ut) / ell) := by
  dsimp
  field_simp
  ring

theorem nonlocal_does_not_cancel_remainder_identity
    (eta ell g u ut l lt : ℝ) (hell : ell ≠ 0) :
    let z := -(g * u) / ell
    let zt := -(g * ut) / ell
    (-g * u * l) + eta * (lt * z + l * zt + ell * z * zt) =
      -g * u * l + eta * (-(g * u * lt) / ell
        - (g * ut * l) / ell + (g^2 * u * ut) / ell) := by
  dsimp
  field_simp
  ring

/- A temporal primitive r_t=l cancels -g*u*l through d(g*u*r)/dt,
   but leaves the displayed new term g*ut*r. -/
theorem temporal_primitive_cancellation
    (g u ut l r : ℝ) :
    -g * u * l + g * (ut * r + u * l) = g * ut * r := by
  ring

/- Adding a second static elliptic proxy p=-l/ell only differentiates the
   product u*l and therefore creates ut*l+u*lt, not u*l. -/
theorem second_elliptic_proxy_derivative
    (ell g u ut l lt : ℝ) (hell : ell ≠ 0) :
    let z := -(g * u) / ell
    let p := -l / ell
    let zt := -(g * ut) / ell
    let pt := -lt / ell
    ell * (zt * p + z * pt) = g * (ut * l + u * lt) / ell := by
  dsimp
  field_simp
  ring

end NonlocalProxy

section PositivityAndMatching

theorem two_by_two_positive_sufficient
    {a b c x y : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hdet : b^2 < a * c) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < a * x^2 + 2 * b * x * y + c * y^2 := by
  have hs : 0 < a * c - b^2 := by nlinarith
  have hid :
      a * (a * x^2 + 2 * b * x * y + c * y^2) =
        (a * x + b * y)^2 + (a * c - b^2) * y^2 := by ring
  by_cases hy : y = 0
  · subst y
    simp only [ne_eq, or_false] at hxy
    nlinarith [sq_pos_of_ne_zero hxy]
  · have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
    have hr : 0 < (a * x + b * y)^2 + (a * c - b^2) * y^2 := by
      nlinarith [sq_nonneg (a * x + b * y)]
    nlinarith [hid]

theorem admittance_equality_implies_zero_reflection
    {Yp Y0 : ℂ} (hY : Yp = Y0) (hden : Y0 + Yp ≠ 0) :
    (Y0 - Yp) / (Y0 + Yp) = 0 := by
  rw [hY]
  simp

theorem local_cross_term_residual
    (c sigi sigj u ut ux uxt l : ℝ) :
    c * (ut * l + u * (uxt + sigj * ux - sigi * l)) =
      -c * sigi * u * l + c * ut * l + c * u * uxt
        + c * sigj * u * ux := by
  ring

end PositivityAndMatching
