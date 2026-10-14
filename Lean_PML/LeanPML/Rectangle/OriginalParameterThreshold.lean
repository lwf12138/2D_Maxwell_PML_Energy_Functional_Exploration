import LeanPML.Rectangle.SharpParameterCertificate

/-!
# V7 §10 显示的 min 分支等式

已有证书说明 c=1/128 合法；本文件另证论文显示的阈值本身
c_* = min{π/√48, π²/1152, 1/24} = π²/1152。
只使用严格 π 界和平方根性质，不用小数近似。
-/
noncomputable section
open LeanPML.PML
namespace LeanPML.Rectangle.ParameterCertificate

/-- V7 §10 未编号阈值公式：第二项确实是三项的最小值。 -/
theorem original_threshold_min :
    min (Real.pi / Real.sqrt 48) (min (Real.pi^2 / 1152) ((1:ℝ)/24)) =
      Real.pi^2 / 1152 := by
  have hpi_pos := Real.pi_pos
  have hpi_sq : Real.pi^2 < 16 := by nlinarith [Real.pi_lt_four]
  have hroot_pos : 0 < Real.sqrt 48 := Real.sqrt_pos.mpr (by norm_num)
  have hroot_le : Real.sqrt 48 ≤ 8 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 48), Real.sqrt_nonneg (48:ℝ)]
  have hsecond_third : Real.pi^2/1152 ≤ (1:ℝ)/24 := by nlinarith
  have hsecond_first : Real.pi^2/1152 ≤ Real.pi/Real.sqrt 48 := by
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<1152) hroot_pos).mpr
    have hproduct : Real.pi^2 * Real.sqrt 48 ≤ 16*8 :=
      mul_le_mul hpi_sq.le hroot_le (Real.sqrt_nonneg _) (by norm_num)
    nlinarith [Real.pi_gt_three]
  rw [min_eq_left hsecond_third, min_eq_right hsecond_first]

/-- 把上条纸面 min 等式接回真实矩形、materialA、scaleK 与 threshold 定义。 -/
theorem original_threshold_exact :
    threshold 1 1 1 1 (sharpPoincareConstant unitSquare) = Real.pi^2/1152 := by
  have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hroot_ne : Real.sqrt (48:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hfirst : 1 / Real.sqrt (48 / Real.pi^2) = Real.pi / Real.sqrt 48 := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_sq Real.pi_pos.le]
    field_simp
  have hsecond : 1 / (8*3*(48 / Real.pi^2)) = Real.pi^2 / 1152 := by
    field_simp
    <;> ring
  unfold threshold
  rw [sharp_K_unitSquare]
  norm_num only [materialA]
  rw [hfirst]
  convert original_threshold_min using 1 <;> norm_num [hsecond]
  congr 1
  congr 1
  ring

/-- 原 c=1/128 严格小于真实 min 阈值；这是精确分支等式的实际调用。 -/
theorem original_c_lt_exact_threshold :
    oldC < threshold 1 1 1 1 (sharpPoincareConstant unitSquare) := by
  rw [original_threshold_exact]
  have hpi_sq : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  norm_num only [oldC]
  linarith

end LeanPML.Rectangle.ParameterCertificate
