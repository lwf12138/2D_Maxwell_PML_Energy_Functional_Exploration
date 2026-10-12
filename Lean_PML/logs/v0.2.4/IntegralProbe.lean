import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory

namespace IntegralProbe

theorem integrable_density {X : Type*} [MeasurableSpace X]
    (m : Measure X) (f p r : X → ℝ)
    (d : ℝ → ℝ → ℝ → ℝ) (C : ℝ)
    (hd : ∀ p r ξ, (ξ ≠ 0 → p = 0 ∧ r = 0) → d p r ξ = C * ξ ^ 2)
    (h_support : ∀ᵐ x ∂m, f x ≠ 0 → p x = 0 ∧ r x = 0)
    (h_sq : Integrable (fun x => (f x) ^ 2) m) :
    Integrable (fun x => d (p x) (r x) (f x)) m := by
  have h_density_ae :
      (fun x => C * (f x) ^ 2) =ᵐ[m] (fun x => d (p x) (r x) (f x)) := by
    filter_upwards [h_support] with x hx_support
    exact (hd (p x) (r x) (f x) hx_support).symm
  exact (h_sq.const_mul C).congr h_density_ae

theorem integral_density {X : Type*} [MeasurableSpace X]
    (m : Measure X) (f p r : X → ℝ)
    (d : ℝ → ℝ → ℝ → ℝ) (C : ℝ)
    (hd : ∀ p r ξ, (ξ ≠ 0 → p = 0 ∧ r = 0) → d p r ξ = C * ξ ^ 2)
    (h_support : ∀ᵐ x ∂m, f x ≠ 0 → p x = 0 ∧ r x = 0) :
    (∫ x, d (p x) (r x) (f x) ∂m) = C * ∫ x, (f x) ^ 2 ∂m := by
  have h_density_ae :
      (fun x => d (p x) (r x) (f x)) =ᵐ[m] (fun x => C * (f x) ^ 2) := by
    filter_upwards [h_support] with x hx_support
    exact hd (p x) (r x) (f x) hx_support
  calc
    (∫ x, d (p x) (r x) (f x) ∂m)
        = ∫ x, C * (f x) ^ 2 ∂m := integral_congr_ae h_density_ae
    _ = C * ∫ x, (f x) ^ 2 ∂m := integral_const_mul C _

theorem integral_negative {X : Type*} [MeasurableSpace X]
    (m : Measure X) (f p r : X → ℝ)
    (d : ℝ → ℝ → ℝ → ℝ) (ε κ μ c : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hμ : 0 < μ) (hc : 0 < c)
    (hd : ∀ p r ξ, (ξ ≠ 0 → p = 0 ∧ r = 0) →
      d p r ξ = -μ * c * (ε + κ) * ξ ^ 2)
    (h_support : ∀ᵐ x ∂m, f x ≠ 0 → p x = 0 ∧ r x = 0)
    (h_sq_pos : 0 < ∫ x, (f x) ^ 2 ∂m) :
    (∫ x, d (p x) (r x) (f x) ∂m) < 0 := by
  rw [integral_density m f p r d (-μ * c * (ε + κ)) hd h_support]
  have h_material_pos : 0 < μ * c * (ε + κ) :=
    mul_pos (mul_pos hμ hc) (add_pos hε hκ)
  have h_total_pos : 0 < μ * c * (ε + κ) * (∫ x, (f x) ^ 2 ∂m) :=
    mul_pos h_material_pos h_sq_pos
  nlinarith [h_total_pos]

theorem rectangle_integral
    (x₀ y₀ x₁ y₁ : ℝ) (f p r : ℝ × ℝ → ℝ)
    (d : ℝ → ℝ → ℝ → ℝ) (C : ℝ)
    (hd : ∀ p r ξ, (ξ ≠ 0 → p = 0 ∧ r = 0) → d p r ξ = C * ξ ^ 2)
    (h_support : ∀ᵐ x ∂(volume.restrict (Set.Icc (x₀, y₀) (x₁, y₁))),
      f x ≠ 0 → p x = 0 ∧ r x = 0)
    (h_sq : Integrable (fun x => (f x) ^ 2)
      (volume.restrict (Set.Icc (x₀, y₀) (x₁, y₁)))) :
    Integrable (fun x => d (p x) (r x) (f x))
      (volume.restrict (Set.Icc (x₀, y₀) (x₁, y₁))) ∧
    (∫ x in Set.Icc (x₀, y₀) (x₁, y₁), d (p x) (r x) (f x)) =
      C * ∫ x in Set.Icc (x₀, y₀) (x₁, y₁), (f x) ^ 2 := by
  constructor
  · exact integrable_density _ f p r d C hd h_support h_sq
  · exact integral_density _ f p r d C hd h_support

theorem secondLayer_integral {X : Type*} [MeasurableSpace X]
    (m : Measure X) (c : ℝ) (gx gy : X → ℝ)
    (hx_sq : Integrable (fun x => (gx x) ^ 2) m)
    (hy_sq : Integrable (fun x => (gy x) ^ 2) m) :
    Integrable (fun x => c * ((gx x) ^ 2 + (gy x) ^ 2)) m ∧
    (∫ x, c * ((gx x) ^ 2 + (gy x) ^ 2) ∂m) =
      c * ((∫ x, (gx x) ^ 2 ∂m) + (∫ x, (gy x) ^ 2 ∂m)) := by
  constructor
  · exact (hx_sq.add hy_sq).const_mul c
  · calc
      (∫ x, c * ((gx x) ^ 2 + (gy x) ^ 2) ∂m)
          = c * ∫ x, (gx x) ^ 2 + (gy x) ^ 2 ∂m := integral_const_mul c _
      _ = c * ((∫ x, (gx x) ^ 2 ∂m) + (∫ x, (gy x) ^ 2 ∂m)) := by
        rw [integral_add hx_sq hy_sq]

#print axioms integrable_density
#print axioms integral_density
#print axioms integral_negative
#print axioms rectangle_integral
#print axioms secondLayer_integral

end IntegralProbe
