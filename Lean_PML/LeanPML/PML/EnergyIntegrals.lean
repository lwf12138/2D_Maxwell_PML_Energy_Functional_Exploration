import LeanPML.PML.Energy

/-!
# V7 能量密度的实际空间积分

本文件接续 Energy 的实际 L² 内积定义，核验 (6.2)、(7.2)、(7.7)
中的每个密度可积，并证明积分等于内积表达。测度 ν 可以取整个矩形的
rectangleMeasure；不把积分域缩成物理区。

先读 fieldEnergyDensity_integrable → fieldEnergy_eq_integral →
fieldSpatialDissipation_nonneg。普通交叉项来自 L²×L²⊂L¹；
无界能量权重来自已构造的 WeightedL2，不假设 w 本质有界。
h=Λ−ψ 是实际 L² 分量；与弱梯度的对应仍属后续空间接口。
-/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
open LeanPML.Analysis

namespace LeanPML.Analysis.BoundedCoefficient
variable {α : Type*} [MeasurableSpace α]

/-- 由 V7 (6.2) 推出，原文未单列：有界系数乘 L² 平方可积。
这是已证交叉项定理 f=g 的应用，不额外要求函数逐点有界。 -/
theorem integrable_square (k : BoundedCoefficient α) (ν : Measure α)
    (f : ScalarL2 ν) : Integrable (fun x => k.value x * (f x)^2) ν := by
  simpa only [pow_two, mul_assoc] using k.integrable_product ν f f

/-- (6.2) 有界系数二次项的积分/内积对应，供三个块的组合使用。 -/
theorem inner_operator_square (k : BoundedCoefficient α) (ν : Measure α)
    (f : ScalarL2 ν) :
    ⟪k.operator ν f, f⟫_ℝ = ∫ x, k.value x * (f x)^2 ∂ν := by
  simpa only [pow_two, mul_assoc] using k.inner_operator ν f f
end LeanPML.Analysis.BoundedCoefficient

namespace LeanPML.PML
variable {α : Type*} [MeasurableSpace α]

/-- (6.2) 的电密度可积。ε/2 为常数，交叉项用 L² 乘积可积，
b+ac 是从吸收条件构造的有界系数；不需要状态满足 PDE。 -/
theorem fieldElectric_integrable (ν : Measure α) (C : SpatialAbsorption α) (ε : ℝ)
    (U : FieldState ν C.wx C.wy) :
    Integrable (fun x => electricEnergy ε (C.a x) (C.b x) C.c (U.v x) (U.V x)) ν := by
  have hvelocity : Integrable (fun x => (U.V x)^2) ν := (Lp.memLp U.V).integrable_sq
  have hcross : Integrable (fun x => (2 * C.c) * (U.v x * U.V x)) ν :=
    (Analysis.integrable_product ν U.v U.V).const_mul (2 * C.c)
  have hquadratic := (electricCoefficient C).integrable_square ν U.v
  convert ((hvelocity.fun_add hcross).fun_add hquadratic).const_mul (ε / 2) using 1
  simp only [electricEnergy, electricCoefficient, BoundedCoefficient.add_value,
      BoundedCoefficient.mul_value, BoundedCoefficient.const_value,
      SpatialAbsorption.aCoeff_value, SpatialAbsorption.bCoeff_value, mul_assoc]

/-- (6.2) 电块的实际积分等于既有内积定义。先显式给出各项可积性，
才拆分积分；不能依赖不可积函数积分也有总定义这一实现细节。 -/
theorem fieldElectric_eq_integral (ν : Measure α) (C : SpatialAbsorption α) (ε : ℝ)
    (U : FieldState ν C.wx C.wy) :
    fieldElectric ν C ε U =
      ∫ x, electricEnergy ε (C.a x) (C.b x) C.c (U.v x) (U.V x) ∂ν := by
  have hvelocity : Integrable (fun x => (U.V x)^2) ν := (Lp.memLp U.V).integrable_sq
  have hcross := (Analysis.integrable_product ν U.v U.V).const_mul (2 * C.c)
  have hquadratic := (electricCoefficient C).integrable_square ν U.v
  have hdensity : (fun x => electricEnergy ε (C.a x) (C.b x) C.c (U.v x) (U.V x)) =
      (fun x => ε / 2 * ((U.V x)^2 + (2 * C.c) * (U.v x * U.V x) +
        (electricCoefficient C).value x * (U.v x)^2)) := by
    funext x
    simp only [electricEnergy, electricCoefficient, BoundedCoefficient.add_value,
      BoundedCoefficient.mul_value, BoundedCoefficient.const_value,
      SpatialAbsorption.aCoeff_value, SpatialAbsorption.bCoeff_value, mul_assoc]
  rw [hdensity, integral_const_mul, integral_add (hvelocity.fun_add hcross) hquadratic,
    integral_add hvelocity hcross, integral_const_mul]
  rw [fieldElectric, norm_sq_eq_integral, Analysis.inner_eq_integral,
    BoundedCoefficient.inner_operator_square]

/-- (6.2) 极化密度可积。三个空间系数均有界；κ 的倒数只是常数，
物理模型 κ>0 另由材料条件给出，此处无需通过消分母证明可积性。 -/
theorem fieldPolar_integrable (ν : Measure α) (C : SpatialAbsorption α) (κ τ : ℝ)
    (U : FieldState ν C.wx C.wy) :
    Integrable (fun x => polarEnergy (C.a x) (C.b x) C.c κ τ (U.R x) (U.z x)) ν := by
  have hR := (polarRCoefficient C τ).integrable_square ν U.R
  have hRz := ((polarCrossCoefficient C τ).integrable_product ν U.R U.z).const_mul 2
  have hz := (polarZCoefficient C τ).integrable_square ν U.z
  convert ((hR.fun_add hRz).fun_add hz).div_const (2 * κ) using 1
  simp only [polarEnergy, polarQuadratic, polarRCoefficient, polarCrossCoefficient,
      polarZCoefficient, BoundedCoefficient.add_value, BoundedCoefficient.mul_value,
      BoundedCoefficient.const_value, SpatialAbsorption.aCoeff_value,
      SpatialAbsorption.bCoeff_value, mul_assoc]

/-- (6.2) 极化块积分/内积对应。因子 2 与 1/(2κ) 与 LocalDebye 完全一致；
这是表示定理，不是正定性或耗散结论。 -/
theorem fieldPolar_eq_integral (ν : Measure α) (C : SpatialAbsorption α) (κ τ : ℝ)
    (U : FieldState ν C.wx C.wy) :
    fieldPolar ν C κ τ U =
      ∫ x, polarEnergy (C.a x) (C.b x) C.c κ τ (U.R x) (U.z x) ∂ν := by
  have hR := (polarRCoefficient C τ).integrable_square ν U.R
  have hRz := ((polarCrossCoefficient C τ).integrable_product ν U.R U.z).const_mul 2
  have hz := (polarZCoefficient C τ).integrable_square ν U.z
  have hdensity : (fun x => polarEnergy (C.a x) (C.b x) C.c κ τ (U.R x) (U.z x)) =
      (fun x => ((polarRCoefficient C τ).value x * (U.R x)^2 +
        2 * ((polarCrossCoefficient C τ).value x * U.R x * U.z x) +
        (polarZCoefficient C τ).value x * (U.z x)^2) / (2 * κ)) := by
    funext x
    simp only [polarEnergy, polarQuadratic, polarRCoefficient, polarCrossCoefficient,
      polarZCoefficient, BoundedCoefficient.add_value, BoundedCoefficient.mul_value,
      BoundedCoefficient.const_value, SpatialAbsorption.aCoeff_value,
      SpatialAbsorption.bCoeff_value, mul_assoc]
  rw [hdensity, integral_div, integral_add (hR.fun_add hRz) hz, integral_add hR hRz,
    integral_const_mul]
  rw [fieldPolar, BoundedCoefficient.inner_operator_square,
    BoundedCoefficient.inner_operator, BoundedCoefficient.inner_operator_square]

/-- (6.2) 空间密度：保留两个普通平方和两个加权平方。
ψ 是已证明的普通 L² 零延拓；wψ² 可积依赖加权成员证据，非 w 的有界性。 -/
def fieldSpatialDensity (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) (x : α) : ℝ :=
  ((U.Λx x)^2 + (U.Λy x)^2 +
    C.wx x * (physicalX ν C U.ψx x)^2 + C.wy x * (physicalY ν C U.ψy x)^2) / 2

/-- (6.2) 空间块可积。四项分别由普通 L² 或实际加权 L² 的平方可积性保证。 -/
theorem fieldSpatial_integrable (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) : Integrable (fieldSpatialDensity ν C U) ν := by
  have hx := (Lp.memLp U.Λx).integrable_sq
  have hy := (Lp.memLp U.Λy).integrable_sq
  have hψx := integrable_weighted_square ν C.wx C.wx_measurable C.wx_gap U.ψx
  have hψy := integrable_weighted_square ν C.wy C.wy_measurable C.wy_gap U.ψy
  exact (((hx.fun_add hy).fun_add hψx).fun_add hψy).div_const 2

/-- (6.2) 空间块积分等于四项 Hilbert 范数平方之和。
加权范数公式已在具体空间证明；这里不是对任意实数范数槽的代数命名。 -/
theorem fieldSpatial_eq_integral (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) :
    fieldSpatial U = ∫ x, fieldSpatialDensity ν C U x ∂ν := by
  have hx := (Lp.memLp U.Λx).integrable_sq
  have hy := (Lp.memLp U.Λy).integrable_sq
  have hψx := integrable_weighted_square ν C.wx C.wx_measurable C.wx_gap U.ψx
  have hψy := integrable_weighted_square ν C.wy C.wy_measurable C.wy_gap U.ψy
  unfold fieldSpatialDensity physicalX physicalY
  rw [integral_div, integral_add ((hx.fun_add hy).fun_add hψx) hψy,
    integral_add (hx.fun_add hy) hψx, integral_add hx hy]
  rw [fieldSpatial, norm_sq_eq_integral ν U.Λx, norm_sq_eq_integral ν U.Λy,
    weighted_norm_sq_eq_integral ν C.wx C.wx_measurable C.wx_gap U.ψx,
    weighted_norm_sq_eq_integral ν C.wy C.wy_measurable C.wy_gap U.ψy]
  -- 此时积分分析已完成，ring 只把四个 /2 合并。
  change _ + _ + _ + _ = (_ + _ + _ + _) / 2
  ring

/-- (6.2) 与 v0.2 的三个旧块逐点相同；f=l−h 在本表示中化为物理 ψ。
这里只展开局部定义并整理多项式，积分合法性由下方另证。 -/
theorem fieldEnergyDensity_eq_blocks (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) (U : FieldState ν C.wx C.wy) (x : α) :
    fieldEnergyDensity ν C ε κ τ μ U x =
      μ * electricEnergy ε (C.a x) (C.b x) C.c (U.v x) (U.V x) +
      μ * polarEnergy (C.a x) (C.b x) C.c κ τ (U.R x) (U.z x) +
      fieldSpatialDensity ν C U x := by
  unfold fieldEnergyDensity Obstructions.singleLayerEnergy spatialEnergy2D
    fieldSpatialDensity SpatialAbsorption.a SpatialAbsorption.b
    SpatialAbsorption.wx SpatialAbsorption.wy
  ring

/-- V7 (6.2) 整个单层局部密度可积，来源是各实际 L² 块。
不输入目标积分能量律；任意实际 FieldState 都有此可积性。 -/
theorem fieldEnergyDensity_integrable (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) (U : FieldState ν C.wx C.wy) :
    Integrable (fieldEnergyDensity ν C ε κ τ μ U) ν := by
  have he := (fieldElectric_integrable ν C ε U).const_mul μ
  have hD := (fieldPolar_integrable ν C κ τ U).const_mul μ
  have hsp := fieldSpatial_integrable ν C U
  apply ((he.fun_add hD).fun_add hsp).congr
  filter_upwards [] with x
  exact (fieldEnergyDensity_eq_blocks ν C ε κ τ μ U x).symm

/-- 本阶段 (6.2) 的主要表示结论：真实内积能量等于旧块密度的实际积分。
µ、ε、κ 和 1/2 均由块对应核对；其可积性由 fieldEnergyDensity_integrable 保证。
这不是 PDE 能量律，也没有证明能量正定性。 -/
theorem fieldEnergy_eq_integral (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) (U : FieldState ν C.wx C.wy) :
    fieldEnergy ν C ε κ τ μ U =
      ∫ x, fieldEnergyDensity ν C ε κ τ μ U x ∂ν := by
  have he := (fieldElectric_integrable ν C ε U).const_mul μ
  have hD := (fieldPolar_integrable ν C κ τ U).const_mul μ
  have hsp := fieldSpatial_integrable ν C U
  simp only [fieldEnergyDensity_eq_blocks]
  rw [integral_add (he.fun_add hD) hsp, integral_add he hD,
    integral_const_mul, integral_const_mul]
  rw [fieldEnergy, fieldElectric_eq_integral, fieldPolar_eq_integral, fieldSpatial_eq_integral]


/-- V7 (7.2) 的实际分量密度。空间分量是 L² 元 Λ−ψ；
尚未声称它等于弱梯度。分支使用旧 spatialDissipation2D，保留 Z 上 c|h|²。 -/
def fieldSpatialDissipationDensity (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) (x : α) : ℝ :=
  spatialDissipation2D C.c (C.p x) (C.r x)
    (spatialComponentX U x) (spatialComponentY U x) (U.Λx x) (U.Λy x)

/-- V7 (7.2) 的实际空间耗散内积表示；四个有界乘子已按方向和零区构造。 -/
def fieldSpatialDissipation (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) : ℝ :=
  ⟪C.plusX.operator ν U.Λx, U.Λx⟫_ℝ +
    ⟪C.minusX.operator ν (spatialComponentX U), spatialComponentX U⟫_ℝ +
    ⟪C.plusY.operator ν U.Λy, U.Λy⟫_ℝ +
    ⟪C.minusY.operator ν (spatialComponentY U), spatialComponentY U⟫_ℝ

/-- (7.2) 的分量密度可积：有界耗散系数乘 L² 平方。
能量权重可无界，与这里的耗散系数有界并不矛盾。 -/
theorem fieldSpatialDissipation_integrable (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) :
    Integrable (fieldSpatialDissipationDensity ν C U) ν := by
  have hlx := C.plusX.integrable_square ν U.Λx
  have hhx := C.minusX.integrable_square ν (spatialComponentX U)
  have hly := C.plusY.integrable_square ν U.Λy
  have hhy := C.minusY.integrable_square ν (spatialComponentY U)
  apply (((hlx.fun_add hhx).fun_add hly).fun_add hhy).congr
  filter_upwards [] with x
  exact (C.spatialDissipation_eq x _ _ _ _).symm

/-- (7.2) 的真实积分/内积对应，域为 ν 的整个空间。
不使用 Green 公式，也不把分量命名直接升级为真实梯度。 -/
theorem fieldSpatialDissipation_eq_integral (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) :
    fieldSpatialDissipation ν C U = ∫ x, fieldSpatialDissipationDensity ν C U x ∂ν := by
  have hlx := C.plusX.integrable_square ν U.Λx
  have hhx := C.minusX.integrable_square ν (spatialComponentX U)
  have hly := C.plusY.integrable_square ν U.Λy
  have hhy := C.minusY.integrable_square ν (spatialComponentY U)
  simp only [fieldSpatialDissipationDensity, C.spatialDissipation_eq]
  rw [integral_add ((hlx.fun_add hhx).fun_add hly) hhy,
    integral_add (hlx.fun_add hhx) hly, integral_add hlx hhx]
  simp only [fieldSpatialDissipation, BoundedCoefficient.inner_operator_square]

/-- (7.2) 非负空间耗散的实际分量积分版本。
旧点态结论使用 c>0、非负吸收及幅度条件；积分保持非负。
该结论不推出单层 D_c 非负，更不是完整 PDE 能量律。 -/
theorem fieldSpatialDissipation_nonneg (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) : 0 ≤ fieldSpatialDissipation ν C U := by
  rw [fieldSpatialDissipation_eq_integral]
  apply integral_nonneg
  intro x
  exact spatialDissipation2D_nonneg C.c (C.p x) (C.r x) C.S
    (spatialComponentX U x) (spatialComponentY U x) (U.Λx x) (U.Λy x)
    C.c_pos (C.p_nonneg x) (C.r_nonneg x) (C.p_le_S x) (C.r_le_S x) C.S_le_quarter

/-- (7.2) 全零吸收的实际积分：S=c(‖h_x‖²+‖h_y‖²)。
输入只要求 a=0 a.e.；普通场和零区耗散保留，不被加权空间退化删除。 -/
theorem fieldSpatialDissipation_of_zeroAbsorption
    (ν : Measure α) (C : SpatialAbsorption α) (U : FieldState ν C.wx C.wy)
    (ha_zero : ∀ᵐ x ∂ν, C.a x = 0) :
    fieldSpatialDissipation ν C U =
      C.c * (‖spatialComponentX U‖^2 + ‖spatialComponentY U‖^2) := by
  rw [fieldSpatialDissipation_eq_integral]
  have hdensity : fieldSpatialDissipationDensity ν C U =ᵐ[ν]
      (fun x => C.c * ((spatialComponentX U x)^2 + (spatialComponentY U x)^2)) := by
    filter_upwards [ha_zero] with x hx
    exact spatialDissipation2D_of_sum_zero C.c (C.p x) (C.r x)
      (spatialComponentX U x) (spatialComponentY U x) (U.Λx x) (U.Λy x) hx
  rw [integral_congr_ae hdensity, integral_const_mul,
    integral_add (Lp.memLp (spatialComponentX U)).integrable_sq
      (Lp.memLp (spatialComponentY U)).integrable_sq,
    ← norm_sq_eq_integral ν (spatialComponentX U),
    ← norm_sq_eq_integral ν (spatialComponentY U)]

/-- (7.7) 中 b c 的有界系数。只组合已证明界，不假设余项非负。 -/
def bcCoefficient (C : SpatialAbsorption α) : BoundedCoefficient α :=
  C.bCoeff.mul (BoundedCoefficient.const C.c)

/-- (7.7) 电余项的内积表达，已含 ε，完整耗散另乘 μ。 -/
def fieldElectricRemainder (ν : Measure α) (C : SpatialAbsorption α) (ε : ℝ)
    (U : FieldState ν C.wx C.wy) : ℝ :=
  ε * (⟪(C.aCoeff.sub (BoundedCoefficient.const C.c)).operator ν U.V, U.V⟫_ℝ +
    ⟪(bcCoefficient C).operator ν U.v, U.v⟫_ℝ)

/-- (7.7) 极化余项。Rdot 是实际 L² 导数数据槽；
在时间路径应用中应传入 StateHasDerivAt.R 绑定的导数，而非仅凭名字认定。 -/
def fieldPolarRemainder (ν : Measure α) (C : SpatialAbsorption α) (κ τ : ℝ)
    (U : FieldState ν C.wx C.wy) (Rdot : ScalarL2 ν) : ℝ :=
  (τ * ‖Rdot‖^2 +
    ⟪(polarRemainderCoefficient C τ).operator ν U.R, U.R⟫_ℝ +
    ⟪(bcCoefficient C).operator ν U.z, U.z⟫_ℝ) / κ

/-- (7.7) 的合法内积定义 D_c。a−c 等系数可负，不附带非负性假设或结论。 -/
def fieldDissipation (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    (U : FieldState ν C.wx C.wy) (Rdot : ScalarL2 ν) : ℝ :=
  μ * fieldElectricRemainder ν C ε U +
    μ * fieldPolarRemainder ν C κ τ U Rdot + fieldSpatialDissipation ν C U

/-- (7.7) 的旧局部耗散密度，直接调用 v0.2.4 三块组合。
h 分量用实际 L² 的 Λ−ψ；未声称它已经是弱梯度。 -/
def fieldDissipationDensity (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    (U : FieldState ν C.wx C.wy) (Rdot : ScalarL2 ν) (x : α) : ℝ :=
  Obstructions.singleLayerDissipation ε κ τ μ C.c (C.p x) (C.r x)
    (U.v x) (U.V x) (U.R x) (U.z x) (Rdot x)
    (spatialComponentX U x) (spatialComponentY U x) (U.Λx x) (U.Λy x)

/-- (7.7) 电余项可积。a−c、bc 虽有界，但前者允许为负。 -/
theorem fieldElectricRemainder_integrable (ν : Measure α) (C : SpatialAbsorption α)
    (ε : ℝ) (U : FieldState ν C.wx C.wy) :
    Integrable (fun x => electricRemainder ε (C.a x) (C.b x) C.c (U.v x) (U.V x)) ν := by
  have hV := (C.aCoeff.sub (BoundedCoefficient.const C.c)).integrable_square ν U.V
  have hv := (bcCoefficient C).integrable_square ν U.v
  convert (hV.fun_add hv).const_mul ε using 1
  simp only [electricRemainder, bcCoefficient, BoundedCoefficient.sub_value,
      BoundedCoefficient.mul_value, BoundedCoefficient.const_value,
      SpatialAbsorption.aCoeff_value, SpatialAbsorption.bCoeff_value]

/-- (7.7) 电余项的积分与内积相等；仅表示对应，无符号承诺。 -/
theorem fieldElectricRemainder_eq_integral (ν : Measure α) (C : SpatialAbsorption α)
    (ε : ℝ) (U : FieldState ν C.wx C.wy) :
    fieldElectricRemainder ν C ε U =
      ∫ x, electricRemainder ε (C.a x) (C.b x) C.c (U.v x) (U.V x) ∂ν := by
  have hV := (C.aCoeff.sub (BoundedCoefficient.const C.c)).integrable_square ν U.V
  have hv := (bcCoefficient C).integrable_square ν U.v
  have hdensity : (fun x => electricRemainder ε (C.a x) (C.b x) C.c (U.v x) (U.V x)) =
      (fun x => ε * ((C.aCoeff.sub (BoundedCoefficient.const C.c)).value x * (U.V x)^2 +
        (bcCoefficient C).value x * (U.v x)^2)) := by
    funext x
    rfl
  rw [hdensity, integral_const_mul, integral_add hV hv]
  simp only [fieldElectricRemainder, BoundedCoefficient.inner_operator_square]

/-- (7.7) 极化余项可积。τRdot² 可积由真实 L² 成员资格给出。 -/
theorem fieldPolarRemainder_integrable (ν : Measure α) (C : SpatialAbsorption α)
    (κ τ : ℝ) (U : FieldState ν C.wx C.wy) (Rdot : ScalarL2 ν) :
    Integrable (fun x => polarRemainder (C.a x) (C.b x) C.c κ τ
      (U.R x) (U.z x) (Rdot x)) ν := by
  have hRt := (Lp.memLp Rdot).integrable_sq.const_mul τ
  have hR := (polarRemainderCoefficient C τ).integrable_square ν U.R
  have hz := (bcCoefficient C).integrable_square ν U.z
  convert ((hRt.fun_add hR).fun_add hz).div_const κ using 1
  simp only [polarRemainder, polarRemainderCoefficient, bcCoefficient,
      BoundedCoefficient.add_value, BoundedCoefficient.sub_value,
      BoundedCoefficient.mul_value, BoundedCoefficient.const_value,
      SpatialAbsorption.aCoeff_value, SpatialAbsorption.bCoeff_value]

/-- (7.7) 极化余项的实际积分/内积对应，不使用目标能量律。 -/
theorem fieldPolarRemainder_eq_integral (ν : Measure α) (C : SpatialAbsorption α)
    (κ τ : ℝ) (U : FieldState ν C.wx C.wy) (Rdot : ScalarL2 ν) :
    fieldPolarRemainder ν C κ τ U Rdot =
      ∫ x, polarRemainder (C.a x) (C.b x) C.c κ τ (U.R x) (U.z x) (Rdot x) ∂ν := by
  have hRt := (Lp.memLp Rdot).integrable_sq.const_mul τ
  have hR := (polarRemainderCoefficient C τ).integrable_square ν U.R
  have hz := (bcCoefficient C).integrable_square ν U.z
  have hdensity : (fun x => polarRemainder (C.a x) (C.b x) C.c κ τ
      (U.R x) (U.z x) (Rdot x)) =
      (fun x => (τ * (Rdot x)^2 + (polarRemainderCoefficient C τ).value x * (U.R x)^2 +
        (bcCoefficient C).value x * (U.z x)^2) / κ) := by
    funext x
    rfl
  rw [hdensity, integral_div, integral_add (hRt.fun_add hR) hz, integral_add hRt hR,
    integral_const_mul]
  simp only [fieldPolarRemainder, norm_sq_eq_integral,
    BoundedCoefficient.inner_operator_square]

/-- V7 (7.7) 的总耗散密度可积。结论只说积分存在，不说 D_c≥0。 -/
theorem fieldDissipationDensity_integrable (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) (U : FieldState ν C.wx C.wy) (Rdot : ScalarL2 ν) :
    Integrable (fieldDissipationDensity ν C ε κ τ μ U Rdot) ν :=
  (((fieldElectricRemainder_integrable ν C ε U).const_mul μ).add
    ((fieldPolarRemainder_integrable ν C κ τ U Rdot).const_mul μ)).add
    (fieldSpatialDissipation_integrable ν C U)

/-- V7 (7.7) 的完整表达式已成为实际空间积分。
对应旧局部块但尚未代入 PDE；不得把本表示等式称为 F_c'=−D_c。 -/
theorem fieldDissipation_eq_integral (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) (U : FieldState ν C.wx C.wy) (Rdot : ScalarL2 ν) :
    fieldDissipation ν C ε κ τ μ U Rdot =
      ∫ x, fieldDissipationDensity ν C ε κ τ μ U Rdot x ∂ν := by
  have he := (fieldElectricRemainder_integrable ν C ε U).const_mul μ
  have hD := (fieldPolarRemainder_integrable ν C κ τ U Rdot).const_mul μ
  have hsp := fieldSpatialDissipation_integrable ν C U
  change _ = ∫ x, μ * electricRemainder ε (C.a x) (C.b x) C.c (U.v x) (U.V x) +
    μ * polarRemainder (C.a x) (C.b x) C.c κ τ (U.R x) (U.z x) (Rdot x) +
    fieldSpatialDissipationDensity ν C U x ∂ν
  rw [integral_add (he.fun_add hD) hsp, integral_add he hD,
    integral_const_mul, integral_const_mul]
  rw [fieldDissipation, fieldElectricRemainder_eq_integral,
    fieldPolarRemainder_eq_integral, fieldSpatialDissipation_eq_integral]

/-- (7.8) 左半的两层耗散定义；论文应用使用同源路径的两个 R 导数槽。
此定义不包含右半能量律或 D₇ 非负性。 -/
def twoLayerDissipation (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ K : ℝ)
    (U₀ U₁ : FieldState ν C.wx C.wy) (Rdot₀ Rdot₁ : ScalarL2 ν) : ℝ :=
  fieldDissipation ν C ε κ τ μ U₀ Rdot₀ + K * fieldDissipation ν C ε κ τ μ U₁ Rdot₁

/-- (7.8) 的两层密度确实可积，K 为时间不变实常数，不要求符号。 -/
theorem twoLayerDissipation_integrable (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ K : ℝ) (U₀ U₁ : FieldState ν C.wx C.wy) (Rdot₀ Rdot₁ : ScalarL2 ν) :
    Integrable (fun x => fieldDissipationDensity ν C ε κ τ μ U₀ Rdot₀ x +
      K * fieldDissipationDensity ν C ε κ τ μ U₁ Rdot₁ x) ν :=
  (fieldDissipationDensity_integrable ν C ε κ τ μ U₀ Rdot₀).add
    ((fieldDissipationDensity_integrable ν C ε κ τ μ U₁ Rdot₁).const_mul K)

/-- (7.8) 左半是两个实际合法积分的线性组合；右半 PDE 能量律仍待完成。 -/
theorem twoLayerDissipation_eq_integral (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ K : ℝ) (U₀ U₁ : FieldState ν C.wx C.wy) (Rdot₀ Rdot₁ : ScalarL2 ν) :
    twoLayerDissipation ν C ε κ τ μ K U₀ U₁ Rdot₀ Rdot₁ =
      ∫ x, fieldDissipationDensity ν C ε κ τ μ U₀ Rdot₀ x +
        K * fieldDissipationDensity ν C ε κ τ μ U₁ Rdot₁ x ∂ν := by
  have hD₀ := fieldDissipationDensity_integrable ν C ε κ τ μ U₀ Rdot₀
  have hD₁ := (fieldDissipationDensity_integrable ν C ε κ τ μ U₁ Rdot₁).const_mul K
  rw [integral_add hD₀ hD₁, integral_const_mul, twoLayerDissipation,
    fieldDissipation_eq_integral, fieldDissipation_eq_integral]


/-- V7 (6.2) 的实际空间积分沿时间求导。先使用真实 L²/加权路径求导，
再由积分/内积表示改写整个函数；没有逐点微分与空间积分交换假设。
输出仍为明确内积表达式 fieldEnergyRate，尚未使用 primitive 或 Green/PEC。 -/
theorem hasDerivAt_integral_fieldEnergy (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) {U : ℝ → FieldState ν C.wx C.wy}
    {dU : FieldState ν C.wx C.wy} {t : ℝ} (hU : StateHasDerivAt U dU t) :
    HasDerivAt (fun s => ∫ x, fieldEnergyDensity ν C ε κ τ μ (U s) x ∂ν)
      (fieldEnergyRate ν C ε κ τ μ (U t) dU) t := by
  have henergy := hasDerivAt_fieldEnergy ν C ε κ τ μ hU
  -- 表示定理对每个状态成立，故这里改写整个时间函数，而非仅改写求导点的值。
  simpa only [fieldEnergy_eq_integral] using henergy

/-- V7 (7.8) 左半的论文同源入口：K 使用既定 scaleK，
U₀ 的 R_t 取 first.R=P_t，U₁ 的 R_t 取 second.R=P_tt。
这些坐标的真实导数证据保存在 SameSourcePath，不允许独立挑选两个耗散导数槽。 -/
def dissipation7 (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ CP : ℝ)
    {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I) (t : ℝ) : ℝ :=
  twoLayerDissipation ν C ε κ τ μ (scaleK ε κ μ CP)
    (path.base t) (path.first t) (path.first t).R (path.second t).R


end LeanPML.PML
