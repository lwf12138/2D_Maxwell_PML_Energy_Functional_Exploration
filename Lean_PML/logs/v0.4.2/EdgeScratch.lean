import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Ring
open MeasureTheory Set
noncomputable section

def edgePair (a b : ℝ) (hab : a ≤ b) :
    C(Icc a b,ℝ) →ₗ[ℝ] C(Icc a b,ℝ) →ₗ[ℝ] ℝ where
  toFun u := {
    toFun := fun v => ∫ s in a..b, (u.IccExtend hab s) * (v.IccExtend hab s)
    map_add' := by
      intro v w
      change (∫ s in a..b, (u.IccExtend hab s) * ((v+w).IccExtend hab s)) = _
      have hexpand : ∀ s, u.IccExtend hab s * (v+w).IccExtend hab s =
          u.IccExtend hab s * v.IccExtend hab s + u.IccExtend hab s * w.IccExtend hab s := by
        intro s
        change u _ * (v _ + w _) = _
        exact mul_add _ _ _
      simp_rw [hexpand]
      exact intervalIntegral.integral_add
        (((u.IccExtend hab).continuous.mul (v.IccExtend hab).continuous).intervalIntegrable a b)
        (((u.IccExtend hab).continuous.mul (w.IccExtend hab).continuous).intervalIntegrable a b)
    map_smul' := by
      intro r v
      change (∫ s in a..b, (u.IccExtend hab s) * ((r • v).IccExtend hab s)) = _
      have hexpand : ∀ s, u.IccExtend hab s * (r • v).IccExtend hab s =
          r * (u.IccExtend hab s * v.IccExtend hab s) := by
        intro s
        change u _ * (r * v _) = _
        dsimp [ContinuousMap.IccExtend, Set.IccExtend]
        ring
      simp_rw [hexpand]
      exact intervalIntegral.integral_const_mul _ _ }
  map_add' := by
    intro u v
    ext w
    change (∫ s in a..b, ((u+v).IccExtend hab s) * (w.IccExtend hab s)) = _
    have hexpand : ∀ s, (u+v).IccExtend hab s * w.IccExtend hab s =
        u.IccExtend hab s * w.IccExtend hab s + v.IccExtend hab s * w.IccExtend hab s := by
      intro s
      change (u _ + v _) * w _ = _
      exact add_mul _ _ _
    simp_rw [hexpand]
    exact intervalIntegral.integral_add
      (((u.IccExtend hab).continuous.mul (w.IccExtend hab).continuous).intervalIntegrable a b)
      (((v.IccExtend hab).continuous.mul (w.IccExtend hab).continuous).intervalIntegrable a b)
  map_smul' := by
    intro r u
    ext w
    change (∫ s in a..b, ((r • u).IccExtend hab s) * (w.IccExtend hab s)) = _
    have hexpand : ∀ s, (r • u).IccExtend hab s * w.IccExtend hab s =
        r * (u.IccExtend hab s * w.IccExtend hab s) := by
      intro s
      change (r * u _) * w _ = _
      dsimp [ContinuousMap.IccExtend, Set.IccExtend]
      ring
    simp_rw [hexpand]
    exact intervalIntegral.integral_const_mul _ _
