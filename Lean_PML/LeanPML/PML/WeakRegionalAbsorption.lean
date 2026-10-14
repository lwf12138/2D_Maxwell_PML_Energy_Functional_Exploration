import LeanPML.PML.SeparatedWeakCoefficients
import LeanPML.PML.SpatialCoefficients
import LeanPML.Rectangle.ParameterCertificate

/-!
# 区域分离 W¹,∞ 吸收到实际能量系数的推荐桥接

V7 §1、(5.3)、(5.5)：原 p(x)、r(y) 的物理幅度只约束矩形对应闭区间。
系数弱导数采用已有 RegionalWeakCoefficient；没有全轴 C∞ 或幅度条件。
内部 SpatialAbsorption 使用区域代表的零延拓；下面证明域内、a.e.、
L² 乘子以及权重积分的一致性。延拓的域外跳跃不用于弱求导。
区域连续代表单列为提升唯一性当前证明所用的技术输入，不冒称已由类型自动选择。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

/-- 推荐弱系数入口。分离 W¹,∞ 本身来自测试函数定义；
非负及幅度只输入 profile 的闭坐标区间，内部非负界随后推出。
连续代表用于已有规范唯一性，不是全轴光滑延拓要求。 -/
structure WeakRegionalAbsorption (D : Rect) where
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
  p_continuous : ContinuousOn coefficients.p.value.value D.openSet
  r_continuous : ContinuousOn coefficients.r.value.value D.openSet

namespace WeakRegionalAbsorption
variable {D : Rect}

/-- 将坐标区间的原始幅度转成 Ω 内真实代表的幅度。
这里实际调用分离等式，不要求原 profile 在区间外也满足界。 -/
theorem regional_bounds (A : WeakRegionalAbsorption D) (x : ℝ × ℝ) (hx : x ∈ D.openSet) :
    (0 ≤ A.coefficients.p.value.value x ∧ A.coefficients.p.value.value x ≤ A.S) ∧
    (0 ≤ A.coefficients.r.value.value x ∧ A.coefficients.r.value.value x ≤ A.S) := by
  rw [A.coefficients.p_separated x hx, A.coefficients.r_separated x hx]
  exact ⟨A.profileX_bounds x.1 ⟨hx.1.1.le,hx.1.2.le⟩,
    A.profileY_bounds x.2 ⟨hx.2.1.le,hx.2.2.le⟩⟩

/-- 内部有界可测代表：Ω 外置零，Ω 内保留原区域弱系数。
零延拓只供 L² 乘法和权重积分；不声称延拓在全空间仍是 W¹,∞。 -/
def spatial (A : WeakRegionalAbsorption D) : SpatialAbsorption (ℝ × ℝ) where
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

/-- 原区域 p 与内部代表在实际开矩形逐点相同。
方向恰好适合 CompatibleLift.u_unique 的 hp_match 参数。 -/
theorem p_match (A : WeakRegionalAbsorption D) (x : ℝ × ℝ) (hx : x ∈ D.openSet) :
    A.coefficients.p.value.value x = A.spatial.p x := by
  simp [spatial,RegionalBounded.extended,hx]

/-- r 的对应域内相等；不要求整个实轴相等。 -/
theorem r_match (A : WeakRegionalAbsorption D) (x : ℝ × ℝ) (hx : x ∈ D.openSet) :
    A.coefficients.r.value.value x = A.spatial.r x := by
  simp [spatial,RegionalBounded.extended,hx]

/-- 内部能量系数与原分离 profile 在 Ω 上一致，零区及两个方向均保留。 -/
theorem profile_match (A : WeakRegionalAbsorption D) (x : ℝ × ℝ) (hx : x ∈ D.openSet) :
    A.spatial.p x = A.coefficients.profileX x.1 ∧
    A.spatial.r x = A.coefficients.profileY x.2 := by
  exact ⟨(A.p_match x hx).symm.trans (A.coefficients.p_separated x hx),
    (A.r_match x hx).symm.trans (A.coefficients.r_separated x hx)⟩

/-- 全矩形实际测度下的原系数 a.e. 一致；不缩小成物理区。 -/
theorem profiles_ae (A : WeakRegionalAbsorption D) :
    A.spatial.p =ᵐ[D.measure] (fun x => A.coefficients.profileX x.1) ∧
    A.spatial.r =ᵐ[D.measure] (fun x => A.coefficients.profileY x.2) := by
  constructor
  · filter_upwards [ae_restrict_mem D.openSet_open.measurableSet] with x hx
    exact (A.profile_match x hx).1
  · filter_upwards [ae_restrict_mem D.openSet_open.measurableSet] with x hx
    exact (A.profile_match x hx).2

/-- 区域弱系数乘子和能量模块乘子是同一个实际 L² 算子。
两套幅度证据可能不同，但输出 a.e. 相同，因此商类及连续线性映射相等。 -/
theorem operators_eq (A : WeakRegionalAbsorption D) :
    A.coefficients.p.value.operator = A.spatial.pCoeff.operator D.measure ∧
    A.coefficients.r.value.operator = A.spatial.rCoeff.operator D.measure := by
  constructor
  · ext f
    filter_upwards [A.coefficients.p.value.operator_ae f,
      coeFn_boundedMul D.measure A.spatial.pCoeff.value A.spatial.pCoeff.measurable
        A.spatial.pCoeff.bound A.spatial.pCoeff.abs_le f, ae_restrict_mem D.openSet_open.measurableSet]
      with x hm hk hx
    rw [hm,BoundedCoefficient.operator,hk]
    exact congrArg (fun z => z*f x) (A.p_match x hx)
  · ext f
    filter_upwards [A.coefficients.r.value.operator_ae f,
      coeFn_boundedMul D.measure A.spatial.rCoeff.value A.spatial.rCoeff.measurable
        A.spatial.rCoeff.bound A.spatial.rCoeff.abs_le f, ae_restrict_mem D.openSet_open.measurableSet]
      with x hm hk hx
    rw [hm,BoundedCoefficient.operator,hk]
    exact congrArg (fun z => z*f x) (A.r_match x hx)

/-- 权重同样由原 profile 恢复；不对无界 w 作空间求导或有界乘法。
这给后续实际加权成员/能量积分换代表提供 a.e. 证据。 -/
theorem weights_ae (A : WeakRegionalAbsorption D) :
    A.spatial.wx =ᵐ[D.measure] (fun x => energyWeightX A.c
      (A.coefficients.profileX x.1) (A.coefficients.profileY x.2)) ∧
    A.spatial.wy =ᵐ[D.measure] (fun x => energyWeightY A.c
      (A.coefficients.profileX x.1) (A.coefficients.profileY x.2)) := by
  have hcoeff := A.profiles_ae
  constructor
  · filter_upwards [hcoeff.1,hcoeff.2] with x hp hr
    simp only [SpatialAbsorption.wx,hp,hr]
    rfl
  · filter_upwards [hcoeff.1,hcoeff.2] with x hp hr
    simp only [SpatialAbsorption.wy,hp,hr]
    rfl

/-- 对任意实际空间密度，内部代表换回原 p(x)、r(y) 不改变积分。
此处只证明换代表；可积性须由使用它的能量/耗散定理另行兑现。 -/
theorem integral_profiles (A : WeakRegionalAbsorption D)
    (F : (ℝ × ℝ) → ℝ → ℝ → ℝ) :
    (∫ x, F x (A.spatial.p x) (A.spatial.r x) ∂D.measure) =
      ∫ x, F x (A.coefficients.profileX x.1) (A.coefficients.profileY x.2) ∂D.measure := by
  apply integral_congr_ae
  filter_upwards [A.profiles_ae.1,A.profiles_ae.2] with x hp hr
  rw [hp,hr]

/-- 换代表同时保持密度可积性，避免把积分相等误当作已证可积。 -/
theorem integrable_profiles_iff (A : WeakRegionalAbsorption D)
    (F : (ℝ × ℝ) → ℝ → ℝ → ℝ) :
    Integrable (fun x => F x (A.spatial.p x) (A.spatial.r x)) D.measure ↔
      Integrable (fun x => F x (A.coefficients.profileX x.1)
        (A.coefficients.profileY x.2)) D.measure := by
  apply integrable_congr
  filter_upwards [A.profiles_ae.1,A.profiles_ae.2] with x hp hr
  rw [hp,hr]

/-- 常数分离系数的区域调用构造，供四个退化分支回归。
这里只用光滑常数生成合法弱导数证据；不缩小一般结构的 W¹,∞ 范围。 -/
def constant (D : Rect) (c S p r : ℝ) (hc : 0 < c) (hS : 0 ≤ S)
    (hsmall : S ≤ c/4) (hp : 0 ≤ p ∧ p ≤ S) (hr : 0 ≤ r ∧ r ≤ S) :
    WeakRegionalAbsorption D where
  coefficients :=
    { p := weakCoefficientOfSmooth D ⟨fun _ => p, by change ContDiff ℝ ∞ (fun _ : ℝ × ℝ => p); exact contDiff_const⟩
      r := weakCoefficientOfSmooth D ⟨fun _ => r, by change ContDiff ℝ ∞ (fun _ : ℝ × ℝ => r); exact contDiff_const⟩
      profileX := fun _ => p
      profileY := fun _ => r
      p_separated := by intro x hx; rfl
      r_separated := by intro x hx; rfl }
  c := c
  S := S
  c_pos := hc
  S_nonneg := hS
  S_le_quarter := hsmall
  profileX_bounds := fun _ _ => hp
  profileY_bounds := fun _ _ => hr
  p_continuous := continuousOn_const
  r_continuous := continuousOn_const

open LeanPML.Rectangle.ParameterCertificate

/-- 使用项目真实 C_P=4、K=384 的参数证书，构造零/x边层/y边层/角层。
布尔位只控制是否取幅度 S；不把吸收正下界加入一般模型。 -/
def certificateConfiguration (xActive yActive : Bool) : WeakRegionalAbsorption unitSquare :=
  constant unitSquare smallC amplitudeS (if xActive then amplitudeS else 0)
    (if yActive then amplitudeS else 0) smallC_pos amplitudeS_pos.le amplitudeS_eq_quarter.le
    (by cases xActive <;> simp [amplitudeS_pos.le])
    (by cases yActive <;> simp [amplitudeS_pos.le])

/-- 四配置均通过真实区域入口，并复用同一小量阈值证书。 -/
theorem certificate_threshold (xActive yActive : Bool) :
    (certificateConfiguration xActive yActive).spatial.c ≤
      threshold 1 1 1 1 (poincareConstant unitSquare) :=
  unitSquare_le_threshold

/-- 两方向的实际域内取值，显式验证方向交换。 -/
theorem certificate_values (xActive yActive : Bool) (x : ℝ × ℝ)
    (hx : x ∈ unitSquare.openSet) :
    (certificateConfiguration xActive yActive).spatial.p x = (if xActive then amplitudeS else 0) ∧
    (certificateConfiguration xActive yActive).spatial.r x = (if yActive then amplitudeS else 0) :=
  (certificateConfiguration xActive yActive).profile_match x hx

/-- 全零、两个不对称边层、双向角层的实际取值回归，吸收严格正只用于相应实例。 -/
theorem certificate_four_branches (x : ℝ × ℝ) (hx : x ∈ unitSquare.openSet) :
    ((certificateConfiguration false false).spatial.p x = 0 ∧
      (certificateConfiguration false false).spatial.r x = 0) ∧
    (0 < (certificateConfiguration true false).spatial.p x ∧
      (certificateConfiguration true false).spatial.r x = 0) ∧
    ((certificateConfiguration false true).spatial.p x = 0 ∧
      0 < (certificateConfiguration false true).spatial.r x) ∧
    (0 < (certificateConfiguration true true).spatial.p x ∧
      0 < (certificateConfiguration true true).spatial.r x) := by
  have h00 := certificate_values false false x hx
  have h10 := certificate_values true false x hx
  have h01 := certificate_values false true x hx
  have h11 := certificate_values true true x hx
  simpa only [Bool.false_eq_true, reduceIte] using
    And.intro h00 (And.intro ⟨h10.1.symm ▸ amplitudeS_pos, h10.2⟩
      (And.intro ⟨h01.1, h01.2.symm ▸ amplitudeS_pos⟩
        ⟨h11.1.symm ▸ amplitudeS_pos, h11.2.symm ▸ amplitudeS_pos⟩))

end WeakRegionalAbsorption
end LeanPML.PML
