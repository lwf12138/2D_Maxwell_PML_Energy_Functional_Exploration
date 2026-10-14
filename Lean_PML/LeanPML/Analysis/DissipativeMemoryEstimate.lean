import LeanPML.Analysis.EnergyCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# M2：真实 Hilbert 空间耗散 ODE 的有限时间记忆估计

由 V7 (5.7)–(5.8) 的证明需要引出，原文未单列此通用时间引理。
对实际空间值路径 W'=−BW+F，B 为固定连续线性算子且 ⟪X,BX⟫≥0，
通过 sqrt(‖W‖²+δ) 的真实求导得到不损失常数的范数积分估计。
不要求端点 PDE 或端点导数；闭区间连续和内部 HasDerivAt 分开输入。
本文件不预设加权成员传播，具体 WeightedL2 构造应在调用前完成。
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace Topology
namespace LeanPML.Analysis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- 正则化范数的导数不超过外力范数。
δ>0 保证平方根分母非零；耗散项非负仅用于丢弃 −⟪W,BW⟫。 -/
theorem regularized_memory_rate_le (B : H →L[ℝ] H)
    (hB : ∀ X : H, 0 ≤ ⟪X,B X⟫_ℝ) (X F : H) {δ : ℝ} (hδ : 0 < δ) :
    (2*⟪X,-B X+F⟫_ℝ)/(2*Real.sqrt (‖X‖^2+δ)) ≤ ‖F‖ := by
  have hradicand : 0 < ‖X‖^2+δ := by positivity
  have hsqrt : 0 < Real.sqrt (‖X‖^2+δ) := Real.sqrt_pos.mpr hradicand
  have hnorm : ‖X‖ ≤ Real.sqrt (‖X‖^2+δ) := by
    calc
      ‖X‖ = Real.sqrt (‖X‖^2) := (Real.sqrt_sq (norm_nonneg X)).symm
      _ ≤ Real.sqrt (‖X‖^2+δ) := Real.sqrt_le_sqrt (by linarith)
  have hinner : ⟪X,-B X+F⟫_ℝ ≤ ‖X‖*‖F‖ := by
    rw [inner_add_right, inner_neg_right]
    linarith [hB X, real_inner_le_norm X F]
  apply (div_le_iff₀ (mul_pos (by norm_num) hsqrt)).mpr
  have hproduct := mul_le_mul_of_nonneg_right hnorm (norm_nonneg F)
  nlinarith

/-- 真实耗散 ODE 给出正则化范数的端点积分上界。
能量求导由 HasDerivAt.norm_sq 与 sqrt 规则得到，再使用闭区间 FTC 和积分序关系。
此处 t=0 也合法，不需以空内部方程推出任何端点导数。 -/
theorem regularized_memory_bound (B : H →L[ℝ] H)
    (hB : ∀ X : H, 0 ≤ ⟪X,B X⟫_ℝ) (W F : ℝ → H) {T t δ : ℝ}
    (hW : ContinuousOn W (Icc 0 T)) (hF : ContinuousOn F (Icc 0 T))
    (hODE : ∀ s ∈ Ioo 0 T, HasDerivAt W (-B (W s)+F s) s)
    (ht : t ∈ Icc 0 T) (hδ : 0 < δ) :
    Real.sqrt (‖W t‖^2+δ) ≤ Real.sqrt (‖W 0‖^2+δ) + ∫ s in 0..t, ‖F s‖ := by
  let rate : ℝ → ℝ := fun s =>
    (2*⟪W s,-B (W s)+F s⟫_ℝ)/(2*Real.sqrt (‖W s‖^2+δ))
  have hsubset : Icc (0:ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hWsmall : ContinuousOn W (Icc 0 t) := hW.mono hsubset
  have hFsmall : ContinuousOn F (Icc 0 t) := hF.mono hsubset
  have hreg : ContinuousOn (fun s => Real.sqrt (‖W s‖^2+δ)) (Icc 0 t) :=
    Real.continuous_sqrt.comp_continuousOn ((hWsmall.norm.pow 2).add continuousOn_const)
  have hrate : ContinuousOn rate (Icc 0 t) := by
    apply ContinuousOn.div
    · exact continuousOn_const.mul
        (hWsmall.inner (((B.continuous.comp_continuousOn hWsmall).neg).add hFsmall))
    · exact continuousOn_const.mul hreg
    · intro s hs
      exact (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity))).ne'
  have hderiv : ∀ s ∈ Ioo 0 t,
      HasDerivAt (fun s => Real.sqrt (‖W s‖^2+δ)) (rate s) s := by
    intro s hs
    have hsT : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans_le ht.2⟩
    exact (((hODE s hsT).norm_sq).add_const δ).sqrt (by positivity)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hreg hderiv
    (hrate.intervalIntegrable_of_Icc ht.1)
  have hintegral : (∫ s in 0..t, rate s) ≤ ∫ s in 0..t, ‖F s‖ := by
    apply intervalIntegral.integral_mono_on ht.1
      (hrate.intervalIntegrable_of_Icc ht.1) (hFsmall.norm.intervalIntegrable_of_Icc ht.1)
    intro s hs
    exact regularized_memory_rate_le B hB (W s) (F s) hδ
  linarith

/-- 去掉正则化参数后得到精确范数估计。
取 δ=ε²，用 sqrt(a²+ε²)≤a+ε，再令任意 ε>0 消失；不除以 ‖W‖。 -/
theorem norm_le_initial_add_integral_forcing (B : H →L[ℝ] H)
    (hB : ∀ X : H, 0 ≤ ⟪X,B X⟫_ℝ) (W F : ℝ → H) {T t : ℝ}
    (hW : ContinuousOn W (Icc 0 T)) (hF : ContinuousOn F (Icc 0 T))
    (hODE : ∀ s ∈ Ioo 0 T, HasDerivAt W (-B (W s)+F s) s)
    (ht : t ∈ Icc 0 T) :
    ‖W t‖ ≤ ‖W 0‖ + ∫ s in 0..t, ‖F s‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hregular := regularized_memory_bound B hB W F hW hF hODE ht
    (δ := ε^2) (sq_pos_of_pos hε)
  have hleft : ‖W t‖ ≤ Real.sqrt (‖W t‖^2+ε^2) := by
    calc
      ‖W t‖ = Real.sqrt (‖W t‖^2) := (Real.sqrt_sq (norm_nonneg (W t))).symm
      _ ≤ Real.sqrt (‖W t‖^2+ε^2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  have hright : Real.sqrt (‖W 0‖^2+ε^2) ≤ ‖W 0‖+ε := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [norm_nonneg (W 0)]
  linarith

/-- 有限区间 Cauchy–Schwarz 的平方形式： (∫g)²≤t∫g²。
为保持精确常数，直接积分非负平方 (t g−∫g)²；t=0 单独化简。 -/
theorem square_intervalIntegral_le_mul_integral_square (g : ℝ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hg : ContinuousOn g (Icc 0 t)) :
    (∫ s in 0..t, g s)^2 ≤ t * ∫ s in 0..t, (g s)^2 := by
  rcases ht.eq_or_lt with hzero | hpos
  · subst t
    simp
  let I : ℝ := ∫ s in 0..t, g s
  have hgInt : IntervalIntegrable g volume 0 t := hg.intervalIntegrable_of_Icc ht
  have hgSqInt : IntervalIntegrable (fun s => (g s)^2) volume 0 t :=
    (hg.pow 2).intervalIntegrable_of_Icc ht
  have hnonneg : 0 ≤ ∫ s in 0..t, (t*g s-I)^2 :=
    intervalIntegral.integral_nonneg ht (fun s _ => sq_nonneg _)
  have hexpand : (∫ s in 0..t, (t*g s-I)^2) =
      t^2 * (∫ s in 0..t, (g s)^2) - t*I^2 := by
    calc
      _ = ∫ s in 0..t, t^2*(g s)^2-(2*t*I)*g s+I^2 := by
        apply intervalIntegral.integral_congr
        intro s hs
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((hgSqInt.const_mul (t^2)).sub (hgInt.const_mul (2*t*I)))
          (intervalIntegrable_const),
          intervalIntegral.integral_sub (hgSqInt.const_mul (t^2)) (hgInt.const_mul (2*t*I)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        dsimp [I]
        ring
  rw [hexpand] at hnonneg
  have hfactor : 0 ≤ t * (t*(∫ s in 0..t, (g s)^2)-I^2) := by
    nlinarith
  have hdiff := nonneg_of_mul_nonneg_right hfactor hpos
  dsimp [I] at hdiff
  linarith

/-- M2 所需精确 Hilbert 时间估计：
‖W(t)‖²≤2‖W(0)‖²+2t∫‖F(s)‖²。
这是实际连续路径和内部耗散 ODE 的结论，没有把目标范数估计放入输入。
加权 forcing 平方界 2cS‖h‖² 可由调用者的已证乘子定理代入，得到 V7 的 4cSt。 -/
theorem dissipative_memory_square_bound (B : H →L[ℝ] H)
    (hB : ∀ X : H, 0 ≤ ⟪X,B X⟫_ℝ) (W F : ℝ → H) {T t : ℝ}
    (hW : ContinuousOn W (Icc 0 T)) (hF : ContinuousOn F (Icc 0 T))
    (hODE : ∀ s ∈ Ioo 0 T, HasDerivAt W (-B (W s)+F s) s)
    (ht : t ∈ Icc 0 T) :
    ‖W t‖^2 ≤ 2*‖W 0‖^2 + 2*t*(∫ s in 0..t, ‖F s‖^2) := by
  have hnorm := norm_le_initial_add_integral_forcing B hB W F hW hF hODE ht
  have hforcing_nonneg : 0 ≤ ∫ s in 0..t, ‖F s‖ :=
    intervalIntegral.integral_nonneg ht.1 (fun s _ => norm_nonneg _)
  have hnorm_square : ‖W t‖^2 ≤ (‖W 0‖+(∫ s in 0..t, ‖F s‖))^2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) hnorm
  have hCauchy := square_intervalIntegral_le_mul_integral_square (fun s => ‖F s‖) ht.1
    (hF.norm.mono (Icc_subset_Icc le_rfl ht.2))
  nlinarith [sq_nonneg (‖W 0‖-(∫ s in 0..t, ‖F s‖))]

end LeanPML.Analysis
