import LeanPML.PML.WeakCoefficients
import LeanPML.Rectangle.WeakLocality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# 分离区域弱系数的横向导数

服务于 V7 §1 的 p(x)、r(y) 及 §5.3 的规范约束。本文件在真实区域
W¹,∞ 表示中加入“函数仅依赖一坐标”，由 Fubini 和紧支测试函数的
一维微积分基本定理证明横向弱导数为零。没有全轴 C∞ 系数要求。
这里的系数弱导数仍以区域分布定义输入，不假设任意 H¹ 乘积法则。
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ContDiff Topology
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

/-- 内部紧支测试函数的 y 偏导沿完整纵截线积分为零。
端点零值由测试支撑推出，偏导由真实切片 HasDerivAt 绑定。 -/
theorem integral_test_dy_zero (D : Rect) (φ : TestFunction D)
    (x : ℝ) (hx : x ∈ Ioo D.xlo D.xhi) :
    (∫ y in Ioo D.ylo D.yhi, dy φ.field (x,y)) = 0 := by
  have hcontinuous : Continuous (fun y : ℝ => φ.field (x,y)) :=
    φ.field.continuous.comp (continuous_const.prodMk continuous_id)
  have hdyContinuous : Continuous (fun y : ℝ => dy φ.field (x,y)) :=
    φ.field.derivativeY.continuous.comp (continuous_const.prodMk continuous_id)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le D.y_lt.le
    hcontinuous.continuousOn
    (fun y _ => φ.field.hasDerivAt_sliceY (x,y))
    (hdyContinuous.intervalIntegrable D.ylo D.yhi)
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le D.y_lt.le, hFTC]
  rw [φ.zeroBoundary.2.2.1 x ⟨hx.1.le,hx.2.le⟩,
    φ.zeroBoundary.2.2.2 x ⟨hx.1.le,hx.2.le⟩, sub_self]

/-- x 截线版本；方向与上一条互换。 -/
theorem integral_test_dx_zero (D : Rect) (φ : TestFunction D)
    (y : ℝ) (hy : y ∈ Ioo D.ylo D.yhi) :
    (∫ x in Ioo D.xlo D.xhi, dx φ.field (x,y)) = 0 := by
  have hcontinuous : Continuous (fun x : ℝ => φ.field (x,y)) :=
    φ.field.continuous.comp (continuous_id.prodMk continuous_const)
  have hdxContinuous : Continuous (fun x : ℝ => dx φ.field (x,y)) :=
    φ.field.derivativeX.continuous.comp (continuous_id.prodMk continuous_const)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le D.x_lt.le
    hcontinuous.continuousOn
    (fun x _ => φ.field.hasDerivAt_sliceX (x,y))
    (hdxContinuous.intervalIntegrable D.xlo D.xhi)
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le D.x_lt.le, hFTC]
  rw [φ.zeroBoundary.1 y ⟨hy.1.le,hy.2.le⟩,
    φ.zeroBoundary.2.1 y ⟨hy.1.le,hy.2.le⟩, sub_self]

/-- 区域有界系数乘光滑测试偏导确实可积；不是利用积分总定义。
a.e. 代表一致性把实际函数密度接回两个 L² 的可积乘积。 -/
theorem integrable_regional_smooth (D : Rect) (m : RegionalBounded D)
    (φ : SmoothField) : Integrable (fun z => m.value z * φ z) D.measure := by
  apply (integrable_product D.measure m.toL2 (SmoothField.toL2 D φ)).congr
  filter_upwards [m.coe_toL2, SmoothField.coe_toL2 D φ] with z hm hφ
  rw [hm,hφ]

/-- 仅依赖 x 的实际区域有界系数，其 y 弱偏导为零。
输入只识别系数值；结论是对所有内部测试函数成立的弱导数关系。 -/
theorem hasWeakPartial_y_of_separated_x (D : Rect) (m : RegionalBounded D)
    (p : ℝ → ℝ) (hseparated : ∀ z ∈ D.openSet, m.value z = p z.1) :
    HasWeakPartial D 1 m.toL2 0 := by
  intro φ
  rw [inner_zero_left]
  apply Eq.symm
  rw [neg_eq_zero, inner_eq_integral]
  have hrewrite :
      (fun z => m.toL2 z * (SmoothField.toL2 D (smoothPartial 1 φ.field)) z)
        =ᵐ[D.measure] (fun z => m.value z * dy φ.field z) := by
    filter_upwards [m.coe_toL2,
      SmoothField.coe_toL2 D (smoothPartial 1 φ.field)] with z hm hφ
    rw [hm,hφ]
    simp [smoothPartial, SmoothField.derivativeY_apply]
  rw [integral_congr_ae hrewrite]
  have hintegrable : Integrable (fun z => m.value z * dy φ.field z) D.measure := by
    simpa only [SmoothField.derivativeY_apply] using
      integrable_regional_smooth D m φ.field.derivativeY
  rw [D.integral_fubini _ hintegrable]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change (∫ y in Ioo D.ylo D.yhi, _) = 0
  have hslice : (fun y => m.value (x,y) * dy φ.field (x,y))
      =ᵐ[volume.restrict (Ioo D.ylo D.yhi)]
        (fun y => p x * dy φ.field (x,y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [hseparated (x,y) ⟨hx,hy⟩]
  rw [integral_congr_ae hslice, integral_const_mul, integral_test_dy_zero D φ x hx,
    mul_zero]

/-- 仅依赖 y 的系数，其 x 弱偏导为零；Fubini 采用反向积分次序。 -/
theorem hasWeakPartial_x_of_separated_y (D : Rect) (m : RegionalBounded D)
    (r : ℝ → ℝ) (hseparated : ∀ z ∈ D.openSet, m.value z = r z.2) :
    HasWeakPartial D 0 m.toL2 0 := by
  intro φ
  rw [inner_zero_left]
  apply Eq.symm
  rw [neg_eq_zero, inner_eq_integral]
  have hrewrite :
      (fun z => m.toL2 z * (SmoothField.toL2 D (smoothPartial 0 φ.field)) z)
        =ᵐ[D.measure] (fun z => m.value z * dx φ.field z) := by
    filter_upwards [m.coe_toL2,
      SmoothField.coe_toL2 D (smoothPartial 0 φ.field)] with z hm hφ
    rw [hm,hφ]
    simp [smoothPartial, SmoothField.derivativeX_apply]
  rw [integral_congr_ae hrewrite]
  have hintegrable : Integrable (fun z => m.value z * dx φ.field z) D.measure := by
    simpa only [SmoothField.derivativeX_apply] using
      integrable_regional_smooth D m φ.field.derivativeX
  rw [D.measure_eq_prod] at hintegrable ⊢
  rw [integral_prod_symm _ hintegrable]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  change (∫ x in Ioo D.xlo D.xhi, _) = 0
  have hslice : (fun x => m.value (x,y) * dx φ.field (x,y))
      =ᵐ[volume.restrict (Ioo D.xlo D.xhi)]
        (fun x => r y * dx φ.field (x,y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hseparated (x,y) ⟨hx,hy⟩]
  rw [integral_congr_ae hslice, integral_const_mul, integral_test_dx_zero D φ y hy,
    mul_zero]

/-- 分离区域 W¹,∞ 系数的模型入口：弱导数由 RegionalWeakCoefficient 的
分布关系定义；分离条件只在 Ω 上要求。非负与幅度可另加，不影响本导数性质。 -/
structure SeparatedRegionalWeakCoefficients (D : Rect) where
  p : RegionalWeakCoefficient D
  r : RegionalWeakCoefficient D
  profileX : ℝ → ℝ
  profileY : ℝ → ℝ
  p_separated : ∀ z ∈ D.openSet, p.value.value z = profileX z.1
  r_separated : ∀ z ∈ D.openSet, r.value.value z = profileY z.2

/-- 原文分离形式实际推出 ∂y p=0、∂x r=0。
调用上述 Fubini 证明及真实弱导数唯一性，未将横向零导数放入结构字段。 -/
theorem SeparatedRegionalWeakCoefficients.transverse_zero {D : Rect}
    (m : SeparatedRegionalWeakCoefficients D) :
    (m.p.derivative 1).toL2 = 0 ∧ (m.r.derivative 0).toL2 = 0 := by
  exact ⟨(m.p.weak_partial 1).unique
    (hasWeakPartial_y_of_separated_x D m.p.value m.profileX m.p_separated),
    (m.r.weak_partial 0).unique
    (hasWeakPartial_x_of_separated_y D m.r.value m.profileY m.r_separated)⟩

/-- 非对称分离入口调用：p=1、r=0，仍由一般分离弱导数定理核验。
仅测试系数空间接口，不是主定理的正幅度参数或 PDE 解实例。 -/
def separatedWeakOneZero (D : Rect) : SeparatedRegionalWeakCoefficients D where
  p := weakCoefficientOfSmooth D weakCoefficientOne
  r := weakCoefficientOfSmooth D 0
  profileX := fun _ => 1
  profileY := fun _ => 0
  p_separated := by intro z hz; rfl
  r_separated := by intro z hz; rfl

/-- 非零且不对称系数的真实调用；横向弱导数由 Fubini 推出。 -/
theorem separatedWeakOneZero_transverse (D : Rect) :
    ((separatedWeakOneZero D).p.derivative 1).toL2 = 0 ∧
    ((separatedWeakOneZero D).r.derivative 0).toL2 = 0 :=
  (separatedWeakOneZero D).transverse_zero

/-- 规范差值的最后步骤：已知 pg=rg=0，且零吸收区梯度为零，则 g=0。
连续性只要求实际区域代表，用于 Ω₊ 开集；这里明确保留 pg=rg=0 作为
上游方向 Poincaré 所需产物，尚不冒称从全部提升约束已完成唯一性。 -/
theorem weak_zero_of_coefficient_products (D : Rect)
    (p r : RegionalBounded D) (g : zeroBoundaryGraph D)
    (hp_continuous : ContinuousOn p.value D.openSet)
    (hr_continuous : ContinuousOn r.value D.openSet)
    (hp_nonneg : ∀ x ∈ D.openSet, 0 ≤ p.value x)
    (hr_nonneg : ∀ x ∈ D.openSet, 0 ≤ r.value x)
    (hpg : p.operator (g.val.val 0) = 0)
    (hrg : r.operator (g.val.val 0) = 0)
    (hzero_zone : ∀ᵐ x ∂D.measure,
      p.value x + r.value x = 0 → g.val.val 1 x = 0 ∧ g.val.val 2 x = 0) :
    g = 0 := by
  let positiveSet : Set (ℝ × ℝ) :=
    D.openSet ∩ (fun x => p.value x + r.value x) ⁻¹' Ioi 0
  have hpositive_open : IsOpen positiveSet :=
    (hp_continuous.add hr_continuous).isOpen_inter_preimage D.openSet_open isOpen_Ioi
  have hpositive_inside : positiveSet ⊆ D.openSet := inter_subset_left
  have hpg_ae : ∀ᵐ x ∂D.measure, p.value x * g.val.val 0 x = 0 := by
    filter_upwards [p.operator_ae (g.val.val 0), Lp.eq_zero_iff_ae_eq_zero.mp hpg]
      with x hrepr hzero
    exact hrepr.symm.trans hzero
  have hrg_ae : ∀ᵐ x ∂D.measure, r.value x * g.val.val 0 x = 0 := by
    filter_upwards [r.operator_ae (g.val.val 0), Lp.eq_zero_iff_ae_eq_zero.mp hrg]
      with x hrepr hzero
    exact hrepr.symm.trans hzero
  have hvalue_zero : ∀ᵐ x ∂D.measure, x ∈ positiveSet → g.val.val 0 x = 0 := by
    filter_upwards [hpg_ae,hrg_ae] with x hpx hrx hx
    have hsum_positive : 0 < p.value x + r.value x := hx.2
    have hsum_product : (p.value x + r.value x) * g.val.val 0 x = 0 := by
      rw [add_mul,hpx,hrx,add_zero]
    exact (mul_eq_zero.mp hsum_product).resolve_left (ne_of_gt hsum_positive)
  have hcomplement : ∀ᵐ x ∂D.measure, x ∉ positiveSet →
      g.val.val 1 x = 0 ∧ g.val.val 2 x = 0 := by
    filter_upwards [ae_restrict_mem D.openSet_open.measurableSet,hzero_zone]
      with x hx hzero hnot
    have hsum_nonpos : p.value x + r.value x ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      exact hnot ⟨hx,hpos⟩
    have hsum_zero : p.value x + r.value x = 0 :=
      le_antisymm hsum_nonpos (add_nonneg (hp_nonneg x hx) (hr_nonneg x hx))
    exact hzero hsum_zero
  exact weak_zero_of_open_value_and_complement_gradient D g
    hpositive_open hpositive_inside hvalue_zero hcomplement

end LeanPML.PML
