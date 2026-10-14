import LeanPML.PML.WeakAbsorptionRepresentative
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# 分离 Lipschitz 剖面到区域弱系数

用于 V7 (10.2) 的有限阶分段幂次剖面。先由绝对连续积分分部证明真实弱导数，
再用 Fubini 接到现有二维测试定义；不把普通 deriv 的总定义当成弱导数证据。
全轴 Lipschitz 仅为本构造的技术延拓，物理幅度仍只约束矩形。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

/-- Lipschitz 函数与端点为零的 C¹ 测试函数满足一维弱配对。
使用绝对连续积分分部，允许 f 在分段接点不可普通微分。 -/
theorem lipschitz_weak_pairing {a b : ℝ} (hab : a ≤ b)
    (f g : ℝ → ℝ) {K : NNReal} (hf : LipschitzWith K f) (hg : ContDiff ℝ 1 g)
    (hga : g a = 0) (hgb : g b = 0) :
    (∫ x in Ioo a b, deriv f x*g x) = -(∫ x in Ioo a b, f x*deriv g x) := by
  have hfac : AbsolutelyContinuousOnInterval f a b := hf.lipschitzOnWith.absolutelyContinuousOnInterval
  have hgac : AbsolutelyContinuousOnInterval g a b := hg.contDiffOn.absolutelyContinuousOnInterval
  have hparts := hfac.integral_mul_deriv_eq_deriv_mul hgac
  rw [hga,hgb,mul_zero,mul_zero,sub_self,zero_sub] at hparts
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hab]
  linarith

/-- x 剖面的实际区域函数；bound 只在 x 的计算区间使用。 -/
def lipschitzValueX (D : Rect) (f : ℝ → ℝ) {K : NNReal} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x ∈ Ioo D.xlo D.xhi, |f x| ≤ B) : RegionalBounded D where
  value z := f z.1
  measurable := hf.continuous.measurable.comp measurable_fst
  bound := B
  bound_nonneg := hB
  bound_on z hz := hb z.1 hz.1

/-- 导数代表有界来自 Lipschitz 常数；可测性由 mathlib 的 measurable_deriv。 -/
def lipschitzDerivativeX (D : Rect) (f : ℝ → ℝ) {K : NNReal} (hf : LipschitzWith K f) :
    RegionalBounded D where
  value z := deriv f z.1
  measurable := (measurable_deriv f).comp measurable_fst
  bound := K
  bound_nonneg := K.coe_nonneg
  bound_on z _ := by simpa only [Real.norm_eq_abs] using (norm_deriv_le_of_lipschitz hf (x₀ := z.1))

/-- 纵向零偏导的零函数代表。 -/
def regionalZero (D : Rect) : RegionalBounded D where
  value _ := 0
  measurable := measurable_const
  bound := 0
  bound_nonneg := le_rfl
  bound_on _ _ := by simp

/-- 真实弱偏导的 x 方向配对；先验证 L² 乘积可积，再使用反向 Fubini。
横截线端点零值来自二维测试支撑，不额外限制系数在矩形边界的取值。 -/
theorem lipschitzValueX_weak_x (D : Rect) (f : ℝ → ℝ) {K : NNReal} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x ∈ Ioo D.xlo D.xhi, |f x| ≤ B) :
    HasWeakPartial D 0 (lipschitzValueX D f hf B hB hb).toL2 (lipschitzDerivativeX D f hf).toL2 := by
  intro φ
  rw [inner_eq_integral,inner_eq_integral]
  have hleft : (∫ z, (lipschitzDerivativeX D f hf).toL2 z * SmoothField.toL2 D φ.field z ∂D.measure) =
      ∫ z, deriv f z.1*φ.field z ∂D.measure := by
    apply integral_congr_ae
    filter_upwards [(lipschitzDerivativeX D f hf).coe_toL2,SmoothField.coe_toL2 D φ.field] with z hd hg
    rw [hd,hg];rfl
  have hright : (∫ z, (lipschitzValueX D f hf B hB hb).toL2 z *
      SmoothField.toL2 D (smoothPartial 0 φ.field) z ∂D.measure) =
      ∫ z, f z.1*dx φ.field z ∂D.measure := by
    apply integral_congr_ae
    filter_upwards [(lipschitzValueX D f hf B hB hb).coe_toL2,
      SmoothField.coe_toL2 D (smoothPartial 0 φ.field)] with z hd hg
    rw [hd,hg];rfl
  rw [hleft,hright]
  have hli := integrable_regional_smooth D (lipschitzDerivativeX D f hf) φ.field
  have hri := integrable_regional_smooth D (lipschitzValueX D f hf B hB hb) (smoothPartial 0 φ.field)
  change Integrable (fun z => deriv f z.1*φ.field z) D.measure at hli
  change Integrable (fun z => f z.1*dx φ.field z) D.measure at hri
  rw [D.measure_eq_prod] at hli hri ⊢
  rw [integral_prod_symm _ hli,integral_prod_symm _ hri,← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  let g : ℝ → ℝ := fun x => φ.field (x,y)
  have hg : ContDiff ℝ 1 g := (φ.field.contDiff.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hga : g D.xlo = 0 := φ.zeroBoundary.2.1 y ⟨hy.1.le,hy.2.le⟩
  have hgb : g D.xhi = 0 := φ.zeroBoundary.1 y ⟨hy.1.le,hy.2.le⟩
  have hderiv (x : ℝ) : deriv g x = dx φ.field (x,y) := (φ.field.hasDerivAt_sliceX (x,y)).deriv
  simpa only [hderiv] using lipschitz_weak_pairing D.x_lt.le f g hf hg hga hgb

/-- 全部二维弱导数由真实配对建立，供原文幂次剖面调用。 -/
def weakCoefficientOfLipschitzX (D : Rect) (f : ℝ → ℝ) {K : NNReal} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x ∈ Ioo D.xlo D.xhi, |f x| ≤ B) : RegionalWeakCoefficient D where
  value := lipschitzValueX D f hf B hB hb
  derivative i := if i = 0 then lipschitzDerivativeX D f hf else regionalZero D
  weak_partial i := by
    fin_cases i
    · exact lipschitzValueX_weak_x D f hf B hB hb
    · have hz : (regionalZero D).toL2 = 0 := by
        apply Lp.eq_zero_iff_ae_eq_zero.mpr
        exact (regionalZero D).coe_toL2
      change HasWeakPartial D 1 (lipschitzValueX D f hf B hB hb).toL2 (regionalZero D).toL2
      rw [hz]
      exact hasWeakPartial_y_of_separated_x D (lipschitzValueX D f hf B hB hb) f (fun _ _ => rfl)
/-- x 剖面的实际区域函数；bound 只在 x 的计算区间使用。 -/
def lipschitzValueY (D : Rect) (f : ℝ → ℝ) {K : NNReal} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x ∈ Ioo D.ylo D.yhi, |f x| ≤ B) : RegionalBounded D where
  value z := f z.2
  measurable := hf.continuous.measurable.comp measurable_snd
  bound := B
  bound_nonneg := hB
  bound_on z hz := hb z.2 hz.2

/-- 导数代表有界来自 Lipschitz 常数；可测性由 mathlib 的 measurable_deriv。 -/
def lipschitzDerivativeY (D : Rect) (f : ℝ → ℝ) {K : NNReal} (hf : LipschitzWith K f) :
    RegionalBounded D where
  value z := deriv f z.2
  measurable := (measurable_deriv f).comp measurable_snd
  bound := K
  bound_nonneg := K.coe_nonneg
  bound_on z _ := by simpa only [Real.norm_eq_abs] using (norm_deriv_le_of_lipschitz hf (x₀ := z.2))

/-- 真实弱偏导的 x 方向配对；先验证 L² 乘积可积，再使用反向 Fubini。
横截线端点零值来自二维测试支撑，不额外限制系数在矩形边界的取值。 -/
theorem lipschitzValueY_weak_y (D : Rect) (f : ℝ → ℝ) {K : NNReal} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x ∈ Ioo D.ylo D.yhi, |f x| ≤ B) :
    HasWeakPartial D 1 (lipschitzValueY D f hf B hB hb).toL2 (lipschitzDerivativeY D f hf).toL2 := by
  intro φ
  rw [inner_eq_integral,inner_eq_integral]
  have hleft : (∫ z, (lipschitzDerivativeY D f hf).toL2 z * SmoothField.toL2 D φ.field z ∂D.measure) =
      ∫ z, deriv f z.2*φ.field z ∂D.measure := by
    apply integral_congr_ae
    filter_upwards [(lipschitzDerivativeY D f hf).coe_toL2,SmoothField.coe_toL2 D φ.field] with z hd hg
    rw [hd,hg];rfl
  have hright : (∫ z, (lipschitzValueY D f hf B hB hb).toL2 z *
      SmoothField.toL2 D (smoothPartial 1 φ.field) z ∂D.measure) =
      ∫ z, f z.2*dy φ.field z ∂D.measure := by
    apply integral_congr_ae
    filter_upwards [(lipschitzValueY D f hf B hB hb).coe_toL2,
      SmoothField.coe_toL2 D (smoothPartial 1 φ.field)] with z hd hg
    rw [hd,hg];rfl
  rw [hleft,hright]
  have hli := integrable_regional_smooth D (lipschitzDerivativeY D f hf) φ.field
  have hri := integrable_regional_smooth D (lipschitzValueY D f hf B hB hb) (smoothPartial 1 φ.field)
  change Integrable (fun z => deriv f z.2*φ.field z) D.measure at hli
  change Integrable (fun z => f z.2*dy φ.field z) D.measure at hri
  rw [D.measure_eq_prod] at hli hri ⊢
  rw [integral_prod _ hli,integral_prod _ hri,← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  let g : ℝ → ℝ := fun x => φ.field (y,x)
  have hg : ContDiff ℝ 1 g := (φ.field.contDiff.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hga : g D.ylo = 0 := φ.zeroBoundary.2.2.2 y ⟨hy.1.le,hy.2.le⟩
  have hgb : g D.yhi = 0 := φ.zeroBoundary.2.2.1 y ⟨hy.1.le,hy.2.le⟩
  have hderiv (x : ℝ) : deriv g x = dy φ.field (y,x) := (φ.field.hasDerivAt_sliceY (y,x)).deriv
  simpa only [hderiv] using lipschitz_weak_pairing D.y_lt.le f g hf hg hga hgb

/-- 全部二维弱导数由真实配对建立，供原文幂次剖面调用。 -/
def weakCoefficientOfLipschitzY (D : Rect) (f : ℝ → ℝ) {K : NNReal} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x ∈ Ioo D.ylo D.yhi, |f x| ≤ B) : RegionalWeakCoefficient D where
  value := lipschitzValueY D f hf B hB hb
  derivative i := if i = 1 then lipschitzDerivativeY D f hf else regionalZero D
  weak_partial i := by
    fin_cases i
    · have hz : (regionalZero D).toL2 = 0 := by
        apply Lp.eq_zero_iff_ae_eq_zero.mpr
        exact (regionalZero D).coe_toL2
      change HasWeakPartial D 0 (lipschitzValueY D f hf B hB hb).toL2 (regionalZero D).toL2
      rw [hz]
      exact hasWeakPartial_x_of_separated_y D (lipschitzValueY D f hf B hB hb) f (fun _ _ => rfl)
    · exact lipschitzValueY_weak_y D f hf B hB hb

end LeanPML.PML
