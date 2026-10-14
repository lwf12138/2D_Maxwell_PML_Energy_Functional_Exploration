import LeanPML.Time.Constancy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# v1.0.2：(5.7) 的真实时间积分步骤

先固定空间点，σ、ρ 是该点两个时间不变的吸收值，g 是实际梯度分量的时间输入。
从 φ 的真实 HasDerivAt 演化推出变常数公式；不是把公式本身作为解的条件。
本文件不声称 g 已是弱空间梯度，也不声称 (5.8) 的加权可积性传播已经完成。
-/
noncomputable section
open MeasureTheory Set
namespace LeanPML.PML

/-- V7 (5.7) 的固定空间点版本。连续性仅在 [0,T]，ODE 仅在 (0,T)。
不需吸收正性；σ≥0 是后续估计指数核所需条件，不是此恒等式的条件。
使用积分因子真实求导和闭区间 FTC，故允许 t=0、t=T 和 T=0。 -/
theorem auxiliary_memory_formula (σ ρ T : ℝ) (φ g : ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hODE : ∀ s ∈ Ioo 0 T, HasDerivAt φ (-σ * φ s + (ρ - σ) * g s) s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    φ t = Real.exp (-σ * t) * φ 0 +
      (ρ - σ) * ∫ s in 0..t, Real.exp (-σ * (t - s)) * g s := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hexp : Continuous (fun s : ℝ => Real.exp (σ * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hintegrand : ContinuousOn (fun s => Real.exp (σ * s) * ((ρ - σ) * g s)) (Icc 0 t) :=
    hexp.continuousOn.mul (continuousOn_const.mul (hg.mono hsub))
  have hprod : ∀ s ∈ Ioo 0 t,
      HasDerivAt (fun s => Real.exp (σ * s) * φ s)
        (Real.exp (σ * s) * ((ρ - σ) * g s)) s := by
    intro s hs
    have hφs := hODE s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
    have hexps : HasDerivAt (fun s : ℝ => Real.exp (σ * s))
        (Real.exp (σ * s) * σ) s := by
      simpa using ((hasDerivAt_id s).const_mul σ).exp
    -- 乘积法则中的 σ exp(σs)φ 与 ODE 中的 −σφ 项抵消。
    exact (hexps.mul hφs).congr_deriv (by ring)
  have hFTC : (∫ s in 0..t, Real.exp (σ * s) * ((ρ - σ) * g s)) =
      Real.exp (σ * t) * φ t - φ 0 := by
    simpa only [Pi.mul_apply, mul_zero, Real.exp_zero, one_mul] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
        (hexp.continuousOn.mul (hφ.mono hsub)) hprod
        (hintegrand.intervalIntegrable_of_Icc ht.1)
  have hkernel : (∫ s in 0..t, Real.exp (-σ * (t - s)) * g s) =
      Real.exp (-σ * t) * ∫ s in 0..t, Real.exp (σ * s) * g s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [show -σ * (t - s) = -σ * t + σ * s by ring, Real.exp_add]
    ring
  have hfactor : (∫ s in 0..t, Real.exp (σ * s) * ((ρ - σ) * g s)) =
      (ρ - σ) * ∫ s in 0..t, Real.exp (σ * s) * g s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  rw [hfactor] at hFTC
  have hexpcancel : Real.exp (-σ * t) * Real.exp (σ * t) = 1 := by
    rw [← Real.exp_add, show -σ * t + σ * t = 0 by ring, Real.exp_zero]
  rw [hkernel]
  calc
    φ t = Real.exp (-σ * t) * (Real.exp (σ * t) * φ t) := by
      rw [← mul_assoc, hexpcancel, one_mul]
    _ = Real.exp (-σ * t) * φ 0 + Real.exp (-σ * t) *
        ((ρ - σ) * ∫ s in 0..t, Real.exp (σ * s) * g s) := by rw [hFTC]; ring
    _ = _ := by ring

/-- 零吸收点 σ=ρ=0 的保持。需要实际演化及初值；零吸收本身不使 φ 为零。
这是 (5.7) 的调用，不假设全时段零值，也不需要除以吸收系数。 -/
theorem auxiliary_zero_absorption_preserved (T : ℝ) (φ g : ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hODE : ∀ s ∈ Ioo 0 T, HasDerivAt φ 0 s)
    (hinitial : φ 0 = 0) {t : ℝ} (ht : t ∈ Icc 0 T) : φ t = 0 := by
  have hformula := auxiliary_memory_formula 0 0 T φ g hφ hg
    (by simpa using hODE) ht
  simpa [hinitial] using hformula

end LeanPML.PML
