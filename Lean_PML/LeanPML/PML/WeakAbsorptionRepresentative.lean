import LeanPML.PML.SeparatedRepresentative
import LeanPML.PML.WeakRegionalAbsorption

/-!
# 一般区域分离弱吸收的连续代表构造

对应 V7 §1 的分离 W¹,∞、(5.3) 的幅度和 (5.5) 的权重。
原始输入仅含真实区域弱导数、分离性和区域幅度；不输入连续代表存在。
从二维测试/Fubini、一维分布原函数构造 Lipschitz 代表，再填入既有入口。
代表在矩形内 a.e. 相等，因此原乘子、能量密度及权重不改变。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

/-- 原始分离区域 W¹,∞ 吸收数据；与旧入口相比，删除两个连续性字段。
弱导数由实际测试积分定义，幅度只约束计算域坐标闭区间。
本结构没有能量、Green 或兼容保持结论。 -/
structure RawWeakRegionalAbsorption (D : Rect) where
  coefficients : SeparatedRegionalWeakCoefficients D
  c : ℝ
  S : ℝ
  c_pos : 0 < c
  S_nonneg : 0 ≤ S
  S_le_quarter : S ≤ c/4
  profileX_bounds : ∀ x ∈ Icc D.xlo D.xhi,
    0 ≤ coefficients.profileX x ∧ coefficients.profileX x ≤ S
  profileY_bounds : ∀ y ∈ Icc D.ylo D.yhi,
    0 ≤ coefficients.profileY y ∧ coefficients.profileY y ≤ S

namespace RawWeakRegionalAbsorption
variable {D : Rect}

/-- 将坐标区间的原始幅度转成 Ω 内真实代表的幅度。
这里实际调用分离等式，不要求原 profile 在区间外也满足界。 -/
theorem regional_bounds (A : RawWeakRegionalAbsorption D) (x : ℝ × ℝ) (hx : x ∈ D.openSet) :
    (0 ≤ A.coefficients.p.value.value x ∧ A.coefficients.p.value.value x ≤ A.S) ∧
    (0 ≤ A.coefficients.r.value.value x ∧ A.coefficients.r.value.value x ≤ A.S) := by
  rw [A.coefficients.p_separated x hx, A.coefficients.r_separated x hx]
  exact ⟨A.profileX_bounds x.1 ⟨hx.1.1.le,hx.1.2.le⟩,
    A.profileY_bounds x.2 ⟨hx.2.1.le,hx.2.2.le⟩⟩

/-- 内部有界可测代表：Ω 外置零，Ω 内保留原区域弱系数。
零延拓只供 L² 乘法和权重积分；不声称延拓在全空间仍是 W¹,∞。 -/
def rawSpatial (A : RawWeakRegionalAbsorption D) : SpatialAbsorption (ℝ × ℝ) where
  c := A.c
  S := A.S
  c_pos := A.c_pos
  p := A.coefficients.p.value.extended
  r := A.coefficients.r.value.extended
  p_measurable := A.coefficients.p.value.extended_measurable
  r_measurable := A.coefficients.r.value.extended_measurable
  p_nonneg x := by
    by_cases hx : x ∈ D.openSet
    · simpa [RegionalBounded.extended,hx] using (A.regional_bounds x hx).1.1
    · simp [RegionalBounded.extended,hx]
  r_nonneg x := by
    by_cases hx : x ∈ D.openSet
    · simpa [RegionalBounded.extended,hx] using (A.regional_bounds x hx).2.1
    · simp [RegionalBounded.extended,hx]
  p_le_S x := by
    by_cases hx : x ∈ D.openSet
    · simpa [RegionalBounded.extended,hx] using (A.regional_bounds x hx).1.2
    · simpa [RegionalBounded.extended,hx] using A.S_nonneg
  r_le_S x := by
    by_cases hx : x ∈ D.openSet
    · simpa [RegionalBounded.extended,hx] using (A.regional_bounds x hx).2.2
    · simpa [RegionalBounded.extended,hx] using A.S_nonneg
  S_le_quarter := A.S_le_quarter


/-- 两个 Lipschitz 代表及其闭区间幅度由弱导数推出。
原文未单列此辅助结论；它消除旧入口中独立的连续性假设。 -/
theorem representatives (A : RawWeakRegionalAbsorption D) :
    ∃ p r : ℝ → ℝ, Continuous p ∧ Continuous r ∧
      (A.coefficients.profileX =ᵐ[volume.restrict (Ioo D.xlo D.xhi)] p) ∧
      (A.coefficients.profileY =ᵐ[volume.restrict (Ioo D.ylo D.yhi)] r) ∧
      (∀ x ∈ Icc D.xlo D.xhi, 0 ≤ p x ∧ p x ≤ A.S) ∧
      (∀ y ∈ Icc D.ylo D.yhi, 0 ≤ r y ∧ r y ≤ A.S) := by
  obtain ⟨p,hp,hpae⟩ := separated_lipschitz_representative_x D A.coefficients.p
    A.coefficients.profileX A.coefficients.p_separated
  obtain ⟨r,hr,hrae⟩ := separated_lipschitz_representative_y D A.coefficients.r
    A.coefficients.profileY A.coefficients.r_separated
  have hpbound : ∀ x ∈ Icc D.xlo D.xhi, 0 ≤ p x ∧ p x ≤ A.S := by
    apply continuous_representative_bounds D.x_lt A.S_nonneg _ _ hp.continuous hpae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact A.profileX_bounds x ⟨hx.1.le,hx.2.le⟩
  have hrbound : ∀ y ∈ Icc D.ylo D.yhi, 0 ≤ r y ∧ r y ≤ A.S := by
    apply continuous_representative_bounds D.y_lt A.S_nonneg _ _ hr.continuous hrae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact A.profileY_bounds y ⟨hy.1.le,hy.2.le⟩
  exact ⟨p,r,hp.continuous,hr.continuous,hpae,hrae,hpbound,hrbound⟩

/-- 选择已经证明存在的代表，不以选择公理代替存在证明。 -/
def profileX (A : RawWeakRegionalAbsorption D) : ℝ → ℝ := A.representatives.choose

def profileY (A : RawWeakRegionalAbsorption D) : ℝ → ℝ := A.representatives.choose_spec.choose

theorem representative_spec (A : RawWeakRegionalAbsorption D) :
    Continuous A.profileX ∧ Continuous A.profileY ∧
      (A.coefficients.profileX =ᵐ[volume.restrict (Ioo D.xlo D.xhi)] A.profileX) ∧
      (A.coefficients.profileY =ᵐ[volume.restrict (Ioo D.ylo D.yhi)] A.profileY) ∧
      (∀ x ∈ Icc D.xlo D.xhi, 0 ≤ A.profileX x ∧ A.profileX x ≤ A.S) ∧
      (∀ y ∈ Icc D.ylo D.yhi, 0 ≤ A.profileY y ∧ A.profileY y ≤ A.S) :=
  A.representatives.choose_spec.choose_spec

/-- p 的连续有界区域代表；域外不施加物理上界。 -/
def pValue (A : RawWeakRegionalAbsorption D) : RegionalBounded D where
  value z := A.profileX z.1
  measurable := A.representative_spec.1.measurable.comp measurable_fst
  bound := A.S
  bound_nonneg := A.S_nonneg
  bound_on z hz := by
    have hb := A.representative_spec.2.2.2.2.1 z.1 ⟨hz.1.1.le,hz.1.2.le⟩
    simpa only [abs_of_nonneg hb.1] using hb.2

/-- r 的对应区域代表。 -/
def rValue (A : RawWeakRegionalAbsorption D) : RegionalBounded D where
  value z := A.profileY z.2
  measurable := A.representative_spec.2.1.measurable.comp measurable_snd
  bound := A.S
  bound_nonneg := A.S_nonneg
  bound_on z hz := by
    have hb := A.representative_spec.2.2.2.2.2 z.2 ⟨hz.2.1.le,hz.2.2.le⟩
    simpa only [abs_of_nonneg hb.1] using hb.2

/-- 两个二维代表与输入原系数 a.e. 相同；零集可以变化于零测集，商类不变。 -/
theorem values_ae (A : RawWeakRegionalAbsorption D) :
    A.coefficients.p.value.value =ᵐ[D.measure] A.pValue.value ∧
    A.coefficients.r.value.value =ᵐ[D.measure] A.rValue.value :=
  ⟨representative_ae_rectangle_x D A.coefficients.p _ _ A.coefficients.p_separated
      A.representative_spec.2.2.1,
    representative_ae_rectangle_y D A.coefficients.r _ _ A.coefficients.r_separated
      A.representative_spec.2.2.2.1⟩

/-- 实际填入既有能量入口。连续性、弱导数和幅度均来自以上证明。
调用者不再提供 p_continuous、r_continuous。 -/
def represented (A : RawWeakRegionalAbsorption D) : WeakRegionalAbsorption D where
  coefficients :=
    { p := A.coefficients.p.replaceValue A.pValue A.values_ae.1
      r := A.coefficients.r.replaceValue A.rValue A.values_ae.2
      profileX := A.profileX
      profileY := A.profileY
      p_separated := fun _ _ => rfl
      r_separated := fun _ _ => rfl }
  c := A.c
  S := A.S
  c_pos := A.c_pos
  S_nonneg := A.S_nonneg
  S_le_quarter := A.S_le_quarter
  profileX_bounds := A.representative_spec.2.2.2.2.1
  profileY_bounds := A.representative_spec.2.2.2.2.2
  p_continuous := (A.representative_spec.1.comp continuous_fst).continuousOn
  r_continuous := (A.representative_spec.2.1.comp continuous_snd).continuousOn

/-- 原弱系数乘子就是主定理内部的能量乘子。
因此用新代表表达的八式没有改变实际 L² 方程。 -/
theorem operators_eq (A : RawWeakRegionalAbsorption D) :
    A.coefficients.p.value.operator = A.represented.spatial.pCoeff.operator D.measure ∧
    A.coefficients.r.value.operator = A.represented.spatial.rCoeff.operator D.measure := by
  have hrep := A.represented.operators_eq
  exact ⟨(RegionalBounded.operator_eq_of_ae _ _ A.values_ae.1).trans hrep.1,
    (RegionalBounded.operator_eq_of_ae _ _ A.values_ae.2).trans hrep.2⟩

/-- 最终空间系数仍与原始弱系数相同 a.e.；这是权重与积分换代表的依据。 -/
theorem spatial_ae (A : RawWeakRegionalAbsorption D) :
    A.represented.spatial.p =ᵐ[D.measure] A.coefficients.p.value.value ∧
    A.represented.spatial.r =ᵐ[D.measure] A.coefficients.r.value.value := by
  constructor
  · filter_upwards [A.values_ae.1,ae_restrict_mem D.openSet_open.measurableSet] with z hz hin
    exact (A.represented.p_match z hin).symm.trans hz.symm
  · filter_upwards [A.values_ae.2,ae_restrict_mem D.openSet_open.measurableSet] with z hz hin
    exact (A.represented.r_match z hin).symm.trans hz.symm

/-- 原系数的内部有界延拓与所构造代表 a.e. 相同，供原八式搬运。 -/
theorem rawSpatial_ae (A : RawWeakRegionalAbsorption D) :
    A.rawSpatial.p =ᵐ[D.measure] A.represented.spatial.p ∧
    A.rawSpatial.r =ᵐ[D.measure] A.represented.spatial.r := by
  exact ⟨A.coefficients.p.value.extended_ae.trans A.spatial_ae.1.symm,
    A.coefficients.r.value.extended_ae.trans A.spatial_ae.2.symm⟩

/-- 任意实际密度的积分及可积性保持，包括能量、耗散和可能无界权重。
这里只用 a.e. 一致；绝不将 w 当作普通 L² 上的有界乘子。 -/
theorem integral_and_integrable (A : RawWeakRegionalAbsorption D)
    (F : (ℝ × ℝ) → ℝ → ℝ → ℝ) :
    (∫ z, F z (A.represented.spatial.p z) (A.represented.spatial.r z) ∂D.measure) =
      (∫ z, F z (A.coefficients.p.value.value z) (A.coefficients.r.value.value z) ∂D.measure) ∧
    (Integrable (fun z => F z (A.represented.spatial.p z) (A.represented.spatial.r z)) D.measure ↔
      Integrable (fun z => F z (A.coefficients.p.value.value z) (A.coefficients.r.value.value z)) D.measure) := by
  have heq : (fun z => F z (A.represented.spatial.p z) (A.represented.spatial.r z)) =ᵐ[D.measure]
      (fun z => F z (A.coefficients.p.value.value z) (A.coefficients.r.value.value z)) := by
    filter_upwards [A.spatial_ae.1,A.spatial_ae.2] with z hp hr
    rw [hp,hr]
  exact ⟨integral_congr_ae heq,integrable_congr heq⟩

end RawWeakRegionalAbsorption
end LeanPML.PML
