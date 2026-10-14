import LeanPML.PML.LiftUniqueness
import LeanPML.PML.WeakOriginalSystem
import LeanPML.PML.Energy
import LeanPML.PML.BalanceBlocks
import LeanPML.Examples.WeakSpaces

/-!
# V7 §5.3：同一原状态的合法弱提升唯一

原八变量是实际 L² 商类；合法瞬时提升保存 H₀¹ 原函数、极化原函数及加权辅助场，
以 (2.5)、(6.1) 的重构等式识别同一原状态。下面从两份重构相减推出规范差值约束，
调用已证弱空间消去，最后利用物理恢复映射的单射性证明加权坐标及实际能量相同。
这不是演化保持的输入定义，也不替代初始兼容由原方程保持的证明。
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.Weak

/-- 同一原状态 F 的合法瞬时提升。字段是实际空间成员与重构关系，
不包含提升唯一性、能量选择无关或任何能量不等式。 -/
structure CompatibleLift (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ε κ τ μ : ℝ) (F : OriginalState D) where
  u : zeroBoundaryGraph D
  q : ScalarL2 D.measure
  ψx : WeightedL2 D.measure C.wx
  ψy : WeightedL2 D.measure C.wy
  polar : q + τ • F.P = κ • u.val.val 0
  flux_x : μ • F.Hy = u.val.val 1 + physicalX D.measure C ψx
  flux_y : -μ • F.Hx = u.val.val 2 + physicalY D.measure C ψy
  memory1 : F.Z1 = -ε • C.bCoeff.operator D.measure (u.val.val 0)
  memory2 : F.Z2 = -C.bCoeff.operator D.measure q
  auxiliaryX : F.Qx = C.pCoeff.operator D.measure (physicalY D.measure C ψy)
  auxiliaryY : F.Qy = -C.rCoeff.operator D.measure (physicalX D.measure C ψx)

/-- 区域系数与内部有界代表在 Ω 上相同 ⇒ 实际 L² 乘子相同。
用于保持原 p,r 与用于能量的 SpatialAbsorption 之间的域内一致性。 -/
theorem regional_operator_eq_bounded (D : Rect) (m : RegionalBounded D)
    (k : BoundedCoefficient (ℝ × ℝ))
    (hmatch : ∀ x ∈ D.openSet, m.value x = k.value x)
    (f : ScalarL2 D.measure) : m.operator f = k.operator D.measure f := by
  apply Lp.ext
  filter_upwards [m.operator_ae f,k.coe_operator D.measure f,
    ae_restrict_mem D.openSet_open.measurableSet] with x hm hk hx
  rw [hm,hk,hmatch x hx]

/-- 加权物理辅助场在 a=0 区域 a.e. 为零，复用已证零延拓性质。
它不是在任意普通场上从 p=r=0 推断辅助场为零。 -/
theorem weighted_physical_zero_zone (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ψx : WeightedL2 D.measure C.wx) (ψy : WeightedL2 D.measure C.wy) :
    ∀ᵐ x ∂D.measure, C.p x + C.r x = 0 →
      physicalX D.measure C ψx x = 0 ∧ physicalY D.measure C ψy x = 0 := by
  filter_upwards [physicalL2_zero_on_zero D.measure C.wx C.wx_measurable C.wx_gap ψx,
    physicalL2_zero_on_zero D.measure C.wy C.wy_measurable C.wy_gap ψy]
    with x hx hy hsum
  have hweights := weights_of_sum_zero C.c (C.p x) (C.r x) hsum
  exact ⟨hx hweights.1,hy hweights.2.1⟩

/-- 两份合法提升的梯度差由同一磁通量中的辅助场差给出。
这是从重构等式相减的结论，不把规范差值约束预置为字段。 -/
theorem CompatibleLift.gradient_difference {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)}
    {ε κ τ μ : ℝ} {F : OriginalState D} (L M : CompatibleLift D C ε κ τ μ F) :
    (L.u - M.u).val.val 1 = physicalX D.measure C M.ψx - physicalX D.measure C L.ψx ∧
    (L.u - M.u).val.val 2 = physicalY D.measure C M.ψy - physicalY D.measure C L.ψy := by
  constructor
  · have hflux := L.flux_x.symm.trans M.flux_x
    change L.u.val.val 1 - M.u.val.val 1 = _
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hflux)
  · have hflux := L.flux_y.symm.trans M.flux_y
    change L.u.val.val 2 - M.u.val.val 2 = _
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hflux)

/-- 同一原状态下实际 H₀¹ 提升的唯一性。
分离 W¹,∞ 连续代表只在 Ω 上与 C 对应；辅助重构推出横向约束，
加权零延拓推出零区梯度差为零，再调用真正的规范差值定理。 -/
theorem CompatibleLift.u_unique {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)}
    {ε κ τ μ : ℝ} {F : OriginalState D}
    (m : SeparatedRegionalWeakCoefficients D)
    (hp_match : ∀ x ∈ D.openSet, m.p.value.value x = C.p x)
    (hr_match : ∀ x ∈ D.openSet, m.r.value.value x = C.r x)
    (hp_continuous : ContinuousOn m.p.value.value D.openSet)
    (hr_continuous : ContinuousOn m.r.value.value D.openSet)
    (L M : CompatibleLift D C ε κ τ μ F) : L.u = M.u := by
  let g : zeroBoundaryGraph D := L.u - M.u
  have hgradient := L.gradient_difference M
  have hp_derivative : m.p.value.operator (g.val.val 2) = 0 := by
    rw [regional_operator_eq_bounded D m.p.value C.pCoeff hp_match]
    change C.pCoeff.operator D.measure ((L.u-M.u).val.val 2) = 0
    rw [hgradient.2,map_sub,← M.auxiliaryX,← L.auxiliaryX,sub_self]
  have hr_derivative : m.r.value.operator (g.val.val 1) = 0 := by
    rw [regional_operator_eq_bounded D m.r.value C.rCoeff hr_match]
    change C.rCoeff.operator D.measure ((L.u-M.u).val.val 1) = 0
    rw [hgradient.1,map_sub]
    have haux : C.rCoeff.operator D.measure (physicalX D.measure C M.ψx) =
        C.rCoeff.operator D.measure (physicalX D.measure C L.ψx) := by
      have hneg := M.auxiliaryY.symm.trans L.auxiliaryY
      exact neg_injective hneg
    exact sub_eq_zero.mpr haux
  have hzero_zone : ∀ᵐ x ∂D.measure,
      m.p.value.value x + m.r.value.value x = 0 →
      g.val.val 1 x = 0 ∧ g.val.val 2 x = 0 := by
    have hgx : g.val.val 1 = physicalX D.measure C M.ψx - physicalX D.measure C L.ψx :=
      hgradient.1
    have hgy : g.val.val 2 = physicalY D.measure C M.ψy - physicalY D.measure C L.ψy :=
      hgradient.2
    filter_upwards [weighted_physical_zero_zone D C L.ψx L.ψy,
      weighted_physical_zero_zone D C M.ψx M.ψy,
      Lp.coeFn_sub (physicalX D.measure C M.ψx) (physicalX D.measure C L.ψx),
      Lp.coeFn_sub (physicalY D.measure C M.ψy) (physicalY D.measure C L.ψy),
      ae_restrict_mem D.openSet_open.measurableSet] with x hL hM hsubx hsuby hx hzero
    have hsum : C.p x + C.r x = 0 := by
      rwa [hp_match x hx,hr_match x hx] at hzero
    rw [hgx,hgy,hsubx,hsuby]
    simp only [Pi.sub_apply,(hM hsum).1,(hL hsum).1,(hM hsum).2,(hL hsum).2,sub_self]
    exact ⟨trivial,trivial⟩
  have hzero : g = 0 := weak_lift_difference_zero D m g hp_continuous hr_continuous
    (fun x hx => by rw [hp_match x hx];exact C.p_nonneg x)
    (fun x hx => by rw [hr_match x hx];exact C.r_nonneg x)
    hp_derivative hr_derivative hzero_zone
  exact sub_eq_zero.mp hzero

/-- 合法提升对应现有 (6.2) 的实际 FieldState，不另造能量表达式。 -/
def CompatibleLift.state {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)}
    {ε κ τ μ : ℝ} {F : OriginalState D} (L : CompatibleLift D C ε κ τ μ F) :
    FieldState D.measure C.wx C.wy where
  v := L.u.val.val 0
  V := F.E
  R := F.P
  z := L.q
  ψx := L.ψx
  ψy := L.ψy
  Λx := μ • F.Hy
  Λy := -μ • F.Hx

/-- 同一原状态的合法提升产生完全相同的实际加权状态。
u 唯一后，polar 确定 q；空间重构确定物理 ψ；恢复映射单射确定加权 ψ。 -/
theorem CompatibleLift.state_unique {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)}
    {ε κ τ μ : ℝ} {F : OriginalState D}
    (m : SeparatedRegionalWeakCoefficients D)
    (hp_match : ∀ x ∈ D.openSet, m.p.value.value x = C.p x)
    (hr_match : ∀ x ∈ D.openSet, m.r.value.value x = C.r x)
    (hp_continuous : ContinuousOn m.p.value.value D.openSet)
    (hr_continuous : ContinuousOn m.r.value.value D.openSet)
    (L M : CompatibleLift D C ε κ τ μ F) : L.state = M.state := by
  have hu := CompatibleLift.u_unique m hp_match hr_match hp_continuous hr_continuous L M
  have hq : L.q = M.q := by
    have hpolar := L.polar
    rw [hu] at hpolar
    exact add_right_cancel (hpolar.trans M.polar.symm)
  have hpx : physicalX D.measure C L.ψx = physicalX D.measure C M.ψx := by
    have hflux := L.flux_x.symm.trans M.flux_x
    rw [hu] at hflux
    exact add_left_cancel hflux
  have hpy : physicalY D.measure C L.ψy = physicalY D.measure C M.ψy := by
    have hflux := L.flux_y.symm.trans M.flux_y
    rw [hu] at hflux
    exact add_left_cancel hflux
  have hx : L.ψx = M.ψx := physicalL2_injective D.measure C.wx C.wx_measurable C.wx_gap hpx
  have hy : L.ψy = M.ψy := physicalL2_injective D.measure C.wy C.wy_measurable C.wy_gap hpy
  cases L with
  | mk u q ψx ψy polar flux_x flux_y memory1 memory2 auxiliaryX auxiliaryY =>
    cases M with
    | mk u' q' ψx' ψy' polar' flux_x' flux_y' memory1' memory2' auxiliaryX' auxiliaryY' =>
      dsimp only at hu hq hx hy
      subst u';subst q';subst ψx';subst ψy'
      rfl

/-- V7 §5.3 的实际能量选择无关：同一合法原状态的 F_c 不依赖提升选择。
调用上方状态唯一性和已有 fieldEnergy 定义；不以能量相等作为输入。 -/
theorem CompatibleLift.energy_independent {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)}
    {ε κ τ μ : ℝ} {F : OriginalState D}
    (m : SeparatedRegionalWeakCoefficients D)
    (hp_match : ∀ x ∈ D.openSet, m.p.value.value x = C.p x)
    (hr_match : ∀ x ∈ D.openSet, m.r.value.value x = C.r x)
    (hp_continuous : ContinuousOn m.p.value.value D.openSet)
    (hr_continuous : ContinuousOn m.r.value.value D.openSet)
    (L M : CompatibleLift D C ε κ τ μ F) :
    fieldEnergy D.measure C ε κ τ μ L.state = fieldEnergy D.measure C ε κ τ μ M.state := by
  rw [CompatibleLift.state_unique m hp_match hr_match hp_continuous hr_continuous L M]

/-- 两层 E₇ 同样与各层合法提升选择无关；两层的同源时间性质须由路径另行证明。
本条只组合两份已证静态唯一性，不把两个独立状态称为某个 PDE 的导数层。 -/
theorem CompatibleLift.twoLayerEnergy_independent {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)}
    {ε κ τ μ K : ℝ} {F₀ F₁ : OriginalState D}
    (m : SeparatedRegionalWeakCoefficients D)
    (hp_match : ∀ x ∈ D.openSet, m.p.value.value x = C.p x)
    (hr_match : ∀ x ∈ D.openSet, m.r.value.value x = C.r x)
    (hp_continuous : ContinuousOn m.p.value.value D.openSet)
    (hr_continuous : ContinuousOn m.r.value.value D.openSet)
    (L₀ M₀ : CompatibleLift D C ε κ τ μ F₀)
    (L₁ M₁ : CompatibleLift D C ε κ τ μ F₁) :
    twoLayerEnergy D.measure C ε κ τ μ K L₀.state L₁.state =
      twoLayerEnergy D.measure C ε κ τ μ K M₀.state M₁.state := by
  rw [CompatibleLift.state_unique m hp_match hr_match hp_continuous hr_continuous L₀ M₀,
    CompatibleLift.state_unique m hp_match hr_match hp_continuous hr_continuous L₁ M₁]

/-- 非零瞬时调用所用的全零吸收。零区加权场仍由 WeightedL2 正确处理。
此配置只检验规范唯一性，不声称构造了 PDE 演化解。 -/
def liftExampleAbsorption : SpatialAbsorption (ℝ × ℝ) where
  c := 1
  S := 0
  c_pos := by norm_num
  p := fun _ => 0
  r := fun _ => 0
  p_measurable := measurable_const
  r_measurable := measurable_const
  p_nonneg := by intros;norm_num
  r_nonneg := by intros;norm_num
  p_le_S := by intros;norm_num
  r_le_S := by intros;norm_num
  S_le_quarter := by norm_num

/-- 同一配置的真实分布弱系数，纵横弱导数由旧光滑桥接填入。 -/
def liftExampleWeakCoefficients (D : Rect) : SeparatedRegionalWeakCoefficients D where
  p := weakCoefficientOfSmooth D 0
  r := weakCoefficientOfSmooth D 0
  profileX := fun _ => 0
  profileY := fun _ => 0
  p_separated := by intros;rfl
  r_separated := by intros;rfl

/-- 实际非零二维 bump 放入电场，其他原坐标为零；只是瞬时数据而非时间解。 -/
def liftExampleOriginal : OriginalState ParameterCertificate.unitSquare where
  E := SmoothField.toL2 ParameterCertificate.unitSquare LeanPML.Examples.WeakSpaces.physicalTest.field
  Hx := 0
  Hy := 0
  P := 0
  Z1 := 0
  Z2 := 0
  Qx := 0
  Qy := 0

/-- 该非零原状态确有合法瞬时提升，不把所有兼容性质重新设为假设。 -/
def liftExampleCanonical : CompatibleLift ParameterCertificate.unitSquare
    liftExampleAbsorption 1 1 1 1 liftExampleOriginal where
  u := 0
  q := 0
  ψx := 0
  ψy := 0
  polar := by simp [liftExampleOriginal]
  flux_x := by simp [liftExampleOriginal]
  flux_y := by simp [liftExampleOriginal]
  memory1 := by simp [liftExampleOriginal]
  memory2 := by simp [liftExampleOriginal]
  auxiliaryX := by simp [liftExampleOriginal]
  auxiliaryY := by simp [liftExampleOriginal]

/-- 非零调用：任一同原状态合法提升都给出同一实际 fieldEnergy。
非零性来自已有二维 bump 的 L² 证明，唯一性调用新一般定理。 -/
theorem nonzero_lift_energy_choice_call
    (M : CompatibleLift ParameterCertificate.unitSquare liftExampleAbsorption
      1 1 1 1 liftExampleOriginal) :
    liftExampleOriginal.E ≠ 0 ∧
    fieldEnergy ParameterCertificate.unitSquare.measure liftExampleAbsorption
      1 1 1 1 liftExampleCanonical.state =
      fieldEnergy ParameterCertificate.unitSquare.measure liftExampleAbsorption
        1 1 1 1 M.state := by
  constructor
  · exact LeanPML.Examples.WeakSpaces.physicalTest_nonzero_member.2
  · exact CompatibleLift.energy_independent
      (liftExampleWeakCoefficients ParameterCertificate.unitSquare)
      (by intros;rfl) (by intros;rfl)
      (by exact continuousOn_const) (by exact continuousOn_const)
      liftExampleCanonical M

end LeanPML.PML.Weak
