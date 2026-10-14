import LeanPML.PML.AuxiliaryScalarMemory
import LeanPML.Examples.WeakCloseout
import LeanPML.Examples.FullDomainProfile

/-! V7 (5.7) 新标量核的实际调用：非零弱静态解，以及有物理区的非恒定吸收剖面。
后者只检查核算子，不声称另造一条非零 PDE 解。 -/
noncomputable section
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
open LeanPML.PML LeanPML.PML.Weak
namespace LeanPML.Examples.WeakStaticMode
/-- 已证非零原解调用两个方向的标量核记忆公式；y 辅助场非零，r=0。 -/
theorem scalar_kernel_static_call (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (solution T hT).weightedX 0 t = coefficients.scalarMemory unitSquare.measure 0
      (fun s => ((solution T hT).u s).val.val 1) t ∧
    (solution T hT).weightedY initialY t = weightedCongr unitSquare.measure coefficients.swap_wx_eq_wy
      (coefficients.swap.scalarMemory unitSquare.measure initialY
        (fun s => ((solution T hT).u s).val.val 2) t) := by
  apply (solution T hT).scalar_memory_both 0 initialY
  · simp only [map_zero, auxiliary_x]
  · rw [physical_initialY, auxiliary_y]
  · exact ht
end LeanPML.Examples.WeakStaticMode

namespace LeanPML.Examples.FullDomain
/-- 真正非恒定的分离剖面调用一般指数乘子定理。
零吸收平台和外层正值仍由旧 profile 证书保证；不要求权重上界。 -/
theorem nonconstant_profile_scalar_kernel (w : ℝ × ℝ → ℝ) (hw : Measurable w) (t : ℝ) :
    dampingKernel (weightedMul unitSquare.measure w (fun z => profile z.1)
      (profile_contDiff.continuous.measurable.comp measurable_fst) amplitudeS
      (fun z => by rw [abs_of_nonneg (profile_bounds z.1).1]; exact (profile_bounds z.1).2)) t =
    scalarExpMultiplier unitSquare.measure w (fun z => profile z.1)
      (profile_contDiff.continuous.measurable.comp measurable_fst) amplitudeS
      (fun z => by rw [abs_of_nonneg (profile_bounds z.1).1]; exact (profile_bounds z.1).2) t :=
  dampingKernel_eq_scalarExpMultiplier _ _ _ hw _ _ _ t
end LeanPML.Examples.FullDomain
