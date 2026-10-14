import LeanPML.Rectangle.SharpPoincare
import LeanPML.Rectangle.ParameterCertificate
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# V7 §10 的原参数与精确矩形常数

复用真实 (-1,1)²；用 π>3 严格证明 c=1/128、S=1/512 的阈值。
这里核验 (10.1) 的数值，不把 (10.2) 的 W¹,∞ 代表连接假装已经完成。
-/
noncomputable section
open LeanPML.PML
namespace LeanPML.Rectangle.ParameterCertificate

/-- (5.1)、§10：真实单位方形的 CP²=2/π²。 -/
theorem sharp_CP_sq_unitSquare : sharpPoincareConstant unitSquare^2 = 2/Real.pi^2 := by
  rw [sharpPoincareConstant_sq, unitSquare_sideLengths.1, unitSquare_sideLengths.2]
  field_simp
  <;> ring

/-- (5.2)、§10：A=3，K=48/π²。 -/
theorem sharp_K_unitSquare : scaleK 1 1 1 (sharpPoincareConstant unitSquare) = 48/Real.pi^2 := by
  unfold scaleK
  rw [sharp_CP_sq_unitSquare]
  norm_num [materialA]
  ring

/-- (10.1) 后的三条原小量不等式；π>3 提供严格界，没有浮点近似。 -/
theorem original_parameters_explicit :
    oldC^2 * scaleK 1 1 1 (sharpPoincareConstant unitSquare) < 1 ∧
    8*oldC*materialA 1 1*scaleK 1 1 1 (sharpPoincareConstant unitSquare) < 1 ∧
    8*oldC*materialA 1 1*(1:ℝ) < 1 := by
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  rw [sharp_K_unitSquare]
  norm_num [oldC, materialA]
  constructor
  · rw [← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith

/-- 把原参数的显式计算接回 (5.2) min 阈值；仍需使用真实吸收剖面证据。 -/
theorem original_parameters_threshold : oldC ≤ threshold 1 1 1 1 (sharpPoincareConstant unitSquare) := by
  apply (le_threshold_iff_explicit 1 1 1 1 (sharpPoincareConstant unitSquare) oldC
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (sharpPoincareConstant_pos unitSquare) (by norm_num [oldC])).mpr
  exact ⟨original_parameters_explicit.1.le, by simpa using original_parameters_explicit.2.1.le,
    original_parameters_explicit.2.2.le⟩

/-- 原 S=1/512 满足幅度限制，并核验 KS²<1；不构造解。 -/
theorem original_amplitude_certificate :
    (0:ℝ) ≤ 1/512 ∧ (1:ℝ)/512 = oldC/4 ∧
    scaleK 1 1 1 (sharpPoincareConstant unitSquare)*((1:ℝ)/512)^2 < 1 := by
  refine ⟨by norm_num, by norm_num [oldC], ?_⟩
  rw [sharp_K_unitSquare]
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have heq : (48/Real.pi^2)*((1:ℝ)/512)^2 = (3/16384)/Real.pi^2 := by ring
  rw [heq]
  apply (div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  nlinarith
end LeanPML.Rectangle.ParameterCertificate
