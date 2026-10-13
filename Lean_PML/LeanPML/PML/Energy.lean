import LeanPML.PML.State
import LeanPML.PML.SpatialCoefficients
import LeanPML.PML.Obstructions.SingleLayer

/-!
# 实际空间能量：从局部密度到 L² 内积

V7 (6.2)–(6.5)、(7.2)、(7.7)–(7.8) 的定义部分。
阅读顺序：fieldEnergy → EnergyIntegrals 中的 fieldEnergy_eq_integral → hasDerivAt_fieldEnergy。
ν 是整个空间域上的测度；矩形入口采用限制到整个开矩形的二维 Lebesgue 测度。

普通系数 a、b 由实际吸收函数产生，是有界乘子；无界的 w 由 WeightedL2 承载。
空间分量 h=Λ−ψ 在此确实属于 L²，但只有兑现 State 中的空间域接口后，
才可解释为 ∇v。本文件不使用 Green/PEC，也不将导数化为 −D_c。
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open LeanPML.Analysis

namespace LeanPML.PML

variable {α : Type*} [MeasurableSpace α]

/-- (6.2) 电块的有界空间系数 b+ac；界由原吸收条件和系数代数构造推出。 -/
def electricCoefficient (C : SpatialAbsorption α) : BoundedCoefficient α :=
  C.bCoeff.add (C.aCoeff.mul (BoundedCoefficient.const C.c))

/-- (6.2) 极化平方系数 1+(a+c)τ，τ 是时间常参数。 -/
def polarRCoefficient (C : SpatialAbsorption α) (τ : ℝ) : BoundedCoefficient α :=
  (BoundedCoefficient.const 1).add
    ((C.aCoeff.add (BoundedCoefficient.const C.c)).mul (BoundedCoefficient.const τ))

/-- (6.2) 极化交叉系数 c+bτ；内积中另保留因子 2。 -/
def polarCrossCoefficient (C : SpatialAbsorption α) (τ : ℝ) : BoundedCoefficient α :=
  (BoundedCoefficient.const C.c).add (C.bCoeff.mul (BoundedCoefficient.const τ))

/-- (6.2) 极化 z² 系数 ac+b(1+cτ)。 -/
def polarZCoefficient (C : SpatialAbsorption α) (τ : ℝ) : BoundedCoefficient α :=
  (C.aCoeff.mul (BoundedCoefficient.const C.c)).add
    (C.bCoeff.mul (BoundedCoefficient.const (1 + C.c * τ)))

/-- (7.7) 极化余项系数 a−c+τ(ac−b)，允许取负值。 -/
def polarRemainderCoefficient (C : SpatialAbsorption α) (τ : ℝ) :
    BoundedCoefficient α :=
  (C.aCoeff.sub (BoundedCoefficient.const C.c)).add
    ((BoundedCoefficient.const τ).mul
      ((C.aCoeff.mul (BoundedCoefficient.const C.c)).sub C.bCoeff))

/-- (5.6) 到普通 L² 的已证明映射，使用物理系数推出的可测性和正区下界。 -/
def physicalX (ν : Measure α) (C : SpatialAbsorption α) :
    WeightedL2 ν C.wx →L[ℝ] ScalarL2 ν :=
  physicalL2 ν C.wx C.wx_measurable C.wx_gap

/-- y 方向零延拓；与 x 分开保留权重次序。 -/
def physicalY (ν : Measure α) (C : SpatialAbsorption α) :
    WeightedL2 ν C.wy →L[ℝ] ScalarL2 ν :=
  physicalL2 ν C.wy C.wy_measurable C.wy_gap

/-- (6.1) 的待解释空间分量 Λx−ψx。它是实际 L²，但尚未自动成为弱偏导。 -/
def spatialComponentX {ν : Measure α} {C : SpatialAbsorption α}
    (U : FieldState ν C.wx C.wy) : ScalarL2 ν := U.Λx - physicalX ν C U.ψx

/-- (6.1) 的 y 分量；后续空间约束应证明它等于真实弱偏导。 -/
def spatialComponentY {ν : Measure α} {C : SpatialAbsorption α}
    (U : FieldState ν C.wx C.wy) : ScalarL2 ν := U.Λy - physicalY ν C U.ψy

/-- (6.2) 电块的实际内积表示，不含外部 μ。ε/2 与 LocalElectric 一致。 -/
def fieldElectric (ν : Measure α) (C : SpatialAbsorption α) (ε : ℝ)
    (U : FieldState ν C.wx C.wy) : ℝ :=
  ε / 2 * (‖U.V‖ ^ 2 + 2 * C.c * ⟪U.v, U.V⟫_ℝ +
    ⟪(electricCoefficient C).operator ν U.v, U.v⟫_ℝ)

/-- (6.2) 极化块的实际内积表示，不含外部 μ；包含 1/(2κ)。 -/
def fieldPolar (ν : Measure α) (C : SpatialAbsorption α) (κ τ : ℝ)
    (U : FieldState ν C.wx C.wy) : ℝ :=
  (⟪(polarRCoefficient C τ).operator ν U.R, U.R⟫_ℝ +
    2 * ⟪(polarCrossCoefficient C τ).operator ν U.R, U.z⟫_ℝ +
    ⟪(polarZCoefficient C τ).operator ν U.z, U.z⟫_ℝ) / (2 * κ)

/-- (6.2) 空间块：两个普通平方与两个实际加权平方，各乘 1/2。
使用平方和，未把普通乘积类型的范数误当欧氏范数。 -/
def fieldSpatial {ν : Measure α} {C : SpatialAbsorption α}
    (U : FieldState ν C.wx C.wy) : ℝ :=
  ‖U.Λx‖ ^ 2 / 2 + ‖U.Λy‖ ^ 2 / 2 + ‖U.ψx‖ ^ 2 / 2 + ‖U.ψy‖ ^ 2 / 2

/-- V7 (6.2) 的单层空间能量 F_c；三个块复用相同因子。
这是定义；正定性、primitive 能量律和单调性不是定义的字段。 -/
def fieldEnergy (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    (U : FieldState ν C.wx C.wy) : ℝ :=
  μ * fieldElectric ν C ε U + μ * fieldPolar ν C κ τ U + fieldSpatial U

/-- (6.4) 两层能量定义。用于论文路径时，应调用 SameSourcePath 的 base/first，
不能把任意两状态独立命名为原层与导数层。 -/
def twoLayerEnergy (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ K : ℝ)
    (U₀ U₁ : FieldState ν C.wx C.wy) : ℝ :=
  fieldEnergy ν C ε κ τ μ U₀ + K * fieldEnergy ν C ε κ τ μ U₁

/-- (6.5) 图范数平方候选。未包含独立 v,z；在兑现空间约束和零分离前，
不为任意 FieldState 安装范数结构。 -/
def graphSquare {ν : Measure α} {C : SpatialAbsorption α} (ε κ μ : ℝ)
    (U : FieldState ν C.wx C.wy) : ℝ :=
  μ * ε * ‖U.V‖ ^ 2 + μ / κ * ‖U.R‖ ^ 2 +
    (‖U.Λx‖ ^ 2 + ‖U.Λy‖ ^ 2) + (‖U.ψx‖ ^ 2 + ‖U.ψy‖ ^ 2)

/-- (6.5) 的 N₀²+K N₁²；这是候选表达式的组合，不是已证范数等价。 -/
def twoLayerGraphSquare {ν : Measure α} {C : SpatialAbsorption α} (ε κ μ K : ℝ)
    (U₀ U₁ : FieldState ν C.wx C.wy) : ℝ :=
  graphSquare ε κ μ U₀ + K * graphSquare ε κ μ U₁

/-- (6.2) 对应旧模块的原始局部密度；使用 L² 的可测代表函数，
最终积分通过 a.e. 等式证明不依赖代表元。 -/
def fieldEnergyDensity (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    (U : FieldState ν C.wx C.wy) (x : α) : ℝ :=
  Obstructions.singleLayerEnergy ε κ τ μ C.c (C.p x) (C.r x)
    (U.v x) (U.V x) (U.R x) (U.z x)
    (U.Λx x - physicalX ν C U.ψx x) (U.Λy x - physicalY ν C U.ψy x)
    (U.Λx x) (U.Λy x)

/-- (6.2) 电块求导的明确内积表达式，原文未单列。
dU 只有与 StateHasDerivAt 配合时才是实际导数数据。 -/
def electricRate (ν : Measure α) (C : SpatialAbsorption α) (ε : ℝ)
    (U dU : FieldState ν C.wx C.wy) : ℝ :=
  ε / 2 * (2 * ⟪U.V, dU.V⟫_ℝ +
    2 * C.c * (⟪U.v, dU.V⟫_ℝ + ⟪dU.v, U.V⟫_ℝ) +
    (⟪(electricCoefficient C).operator ν U.v, dU.v⟫_ℝ +
      ⟪(electricCoefficient C).operator ν dU.v, U.v⟫_ℝ))

/-- (6.2) 极化块逐项求导；保留两个交叉贡献，不借用未证明的 PDE 抵消。 -/
def polarRate (ν : Measure α) (C : SpatialAbsorption α) (κ τ : ℝ)
    (U dU : FieldState ν C.wx C.wy) : ℝ :=
  ((⟪(polarRCoefficient C τ).operator ν U.R, dU.R⟫_ℝ +
      ⟪(polarRCoefficient C τ).operator ν dU.R, U.R⟫_ℝ) +
    2 * (⟪(polarCrossCoefficient C τ).operator ν U.R, dU.z⟫_ℝ +
      ⟪(polarCrossCoefficient C τ).operator ν dU.R, U.z⟫_ℝ) +
    (⟪(polarZCoefficient C τ).operator ν U.z, dU.z⟫_ℝ +
      ⟪(polarZCoefficient C τ).operator ν dU.z, U.z⟫_ℝ)) / (2 * κ)

/-- 两方向普通/加权空间平方的真实求导值。原文 (6.2) 链式法则的分量版本。 -/
def spatialRate {ν : Measure α} {C : SpatialAbsorption α}
    (U dU : FieldState ν C.wx C.wy) : ℝ :=
  ⟪U.Λx, dU.Λx⟫_ℝ + ⟪U.Λy, dU.Λy⟫_ℝ +
    ⟪U.ψx, dU.ψx⟫_ℝ + ⟪U.ψy, dU.ψy⟫_ℝ

/-- F_c 的空间内积求导表达式。它还不是 −D_c；v0.3.2 需再输入演化和 Green 接口。 -/
def fieldEnergyRate (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    (U dU : FieldState ν C.wx C.wy) : ℝ :=
  μ * electricRate ν C ε U dU + μ * polarRate ν C κ τ U dU + spatialRate U dU

/-- 由 (6.2) 推出的实际 L² 电块求导。
平方范数、交叉内积和固定有界乘子分别应用已证分析规则；无积分/导数交换假设。 -/
theorem hasDerivAt_fieldElectric (ν : Measure α) (C : SpatialAbsorption α) (ε : ℝ)
    {U : ℝ → FieldState ν C.wx C.wy} {dU : FieldState ν C.wx C.wy} {t : ℝ}
    (hU : StateHasDerivAt U dU t) :
    HasDerivAt (fun s => fieldElectric ν C ε (U s))
      (electricRate ν C ε (U t) dU) t := by
  have hvelocity := hU.V.norm_sq
  have hcross := (Analysis.hasDerivAt_inner hU.v hU.V).const_mul (2 * C.c)
  have hquadratic := Analysis.hasDerivAt_operator_quadratic
    ((electricCoefficient C).operator ν) hU.v
  exact ((hvelocity.add hcross).add hquadratic).const_mul (ε / 2)

/-- 由 (6.2) 推出的实际 L² 极化块求导。
κ≠0 是物理解释所需条件；作为实数恒定缩放的求导法则本身不需要除法消元。 -/
theorem hasDerivAt_fieldPolar (ν : Measure α) (C : SpatialAbsorption α) (κ τ : ℝ)
    {U : ℝ → FieldState ν C.wx C.wy} {dU : FieldState ν C.wx C.wy} {t : ℝ}
    (hU : StateHasDerivAt U dU t) :
    HasDerivAt (fun s => fieldPolar ν C κ τ (U s))
      (polarRate ν C κ τ (U t) dU) t := by
  have hR := Analysis.hasDerivAt_operator_quadratic ((polarRCoefficient C τ).operator ν) hU.R
  have hRz := (Analysis.hasDerivAt_operator_inner
    ((polarCrossCoefficient C τ).operator ν) hU.R hU.z).const_mul 2
  have hz := Analysis.hasDerivAt_operator_quadratic ((polarZCoefficient C τ).operator ν) hU.z
  exact ((hR.add hRz).add hz).div_const (2 * κ)

/-- (6.2) 空间块的实际时间求导。ψ 使用 WeightedL2 自己的内积与导数证据，
即使 w 无界也没有把普通 L² 可导性冒充加权可导性。 -/
theorem hasDerivAt_fieldSpatial {ν : Measure α} {C : SpatialAbsorption α}
    {U : ℝ → FieldState ν C.wx C.wy} {dU : FieldState ν C.wx C.wy} {t : ℝ}
    (hU : StateHasDerivAt U dU t) :
    HasDerivAt (fun s => fieldSpatial (U s)) (spatialRate (U t) dU) t := by
  have hx := Analysis.hasDerivAt_half_norm_sq hU.Λx
  have hy := Analysis.hasDerivAt_half_norm_sq hU.Λy
  have hψx := hasDerivAt_weighted_half_norm_sq ν C.wx hU.ψx
  have hψy := hasDerivAt_weighted_half_norm_sq ν C.wy hU.ψy
  exact ((hx.add hy).add hψx).add hψy

/-- 本阶段主求导入口：实际单层空间能量沿真实状态路径可导。
输入为各分量（含加权分量）的 HasDerivAt，输出明确内积表达式 fieldEnergyRate。
这里没有使用 primitive 方程、Green/PEC、两层耗散非负，也不声称 F_c'=−D_c。 -/
theorem hasDerivAt_fieldEnergy (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    {U : ℝ → FieldState ν C.wx C.wy} {dU : FieldState ν C.wx C.wy} {t : ℝ}
    (hU : StateHasDerivAt U dU t) :
    HasDerivAt (fun s => fieldEnergy ν C ε κ τ μ (U s))
      (fieldEnergyRate ν C ε κ τ μ (U t) dU) t := by
  have he := (hasDerivAt_fieldElectric ν C ε hU).const_mul μ
  have hD := (hasDerivAt_fieldPolar ν C κ τ hU).const_mul μ
  have hsp := hasDerivAt_fieldSpatial hU
  exact (he.add hD).add hsp

/-- (6.3)–(6.4) 同源两层的实际求导接口，仅作和与常数倍求导。
R_t 的两个槽分别是 first.R 与 second.R；未证明两层满足同一 primitive 系统。 -/
theorem hasDerivAt_sameSourceEnergy (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ K : ℝ) {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => twoLayerEnergy ν C ε κ τ μ K (path.base s) (path.first s))
      (fieldEnergyRate ν C ε κ τ μ (path.base t) (path.first t) +
        K * fieldEnergyRate ν C ε κ τ μ (path.first t) (path.second t)) t := by
  exact (hasDerivAt_fieldEnergy ν C ε κ τ μ (path.deriv_base t ht)).add
    ((hasDerivAt_fieldEnergy ν C ε κ τ μ (path.deriv_first t ht)).const_mul K)


/-- 由 (6.2) 推出的接口测试状态，原文未单列。
只有加权 x 辅助分量非零，其他槽为零；不声称满足空间约束或 PDE。 -/
def auxiliaryState (ν : Measure α) (C : SpatialAbsorption α)
    (X : WeightedL2 ν C.wx) : FieldState ν C.wx C.wy :=
  ⟨0, 0, 0, 0, X, 0, 0, 0⟩

/-- 非恒定实际空间值路径：ψx(t)=(t+1)X。
X 是实际加权空间成员，不是任意实数；后面用矩形上的非零成员实例化。 -/
def auxiliaryPath (ν : Measure α) (C : SpatialAbsorption α)
    (X : WeightedL2 ν C.wx) (t : ℝ) : FieldState ν C.wx C.wy :=
  auxiliaryState ν C ((t + 1) • X)

/-- 该路径的每个导数都是真实空间导数。smul_const 对固定向量 X 求导，
常零槽由 hasDerivAt_const 给出；没有用逐点可导替代加权路径可导。 -/
theorem auxiliaryPath_hasDerivAt (ν : Measure α) (C : SpatialAbsorption α)
    (X : WeightedL2 ν C.wx) (t : ℝ) :
    StateHasDerivAt (auxiliaryPath ν C X) (auxiliaryState ν C X) t := by
  have hweighted : HasDerivAt (fun s : ℝ => (s + 1) • X) X t := by
    simpa using ((hasDerivAt_id t).add_const 1).smul_const X
  exact ⟨hasDerivAt_const t 0, hasDerivAt_const t 0,
    hasDerivAt_const t 0, hasDerivAt_const t 0, hweighted,
    hasDerivAt_const t 0, hasDerivAt_const t 0, hasDerivAt_const t 0⟩

/-- 测试状态的能量确实是加权范数的一半；普通项不会凭空贡献能量。 -/
theorem fieldEnergy_auxiliaryState (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) (X : WeightedL2 ν C.wx) :
    fieldEnergy ν C ε κ τ μ (auxiliaryState ν C X) = ‖X‖ ^ 2 / 2 := by
  simp [fieldEnergy, fieldElectric, fieldPolar, fieldSpatial, auxiliaryState]

/-- 正式调用本阶段能量主求导定理，得到非恒定加权路径的空间能量导数。
这是空间计算接口实例，不是二维 PDE 解。 -/
theorem hasDerivAt_auxiliaryPath_energy (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) (X : WeightedL2 ν C.wx) (t : ℝ) :
    HasDerivAt (fun s => fieldEnergy ν C ε κ τ μ (auxiliaryPath ν C X s))
      ((t + 1) * ‖X‖ ^ 2) t := by
  have henergy := hasDerivAt_fieldEnergy ν C ε κ τ μ
    (auxiliaryPath_hasDerivAt ν C X t)
  convert henergy using 1
  simp [fieldEnergyRate, electricRate, polarRate, spatialRate,
    auxiliaryPath, auxiliaryState, real_inner_smul_left]

/-- X≠0 时该空间路径的能量从 t=0 到 t=1 严格增加，故既非零也非恒定。
这里没有输入 primitive 方程，因此此例只检验求导接口，不反驳 PML 主定理。 -/
theorem auxiliaryPath_energy_nonconstant (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) (X : WeightedL2 ν C.wx) (hX_ne : X ≠ 0) :
    fieldEnergy ν C ε κ τ μ (auxiliaryPath ν C X 0) <
      fieldEnergy ν C ε κ τ μ (auxiliaryPath ν C X 1) := by
  have hnorm_pos : 0 < ‖X‖ := norm_pos_iff.mpr hX_ne
  change 0 < ‖(X : ScalarL2 ν)‖ at hnorm_pos
  simp only [auxiliaryPath, fieldEnergy_auxiliaryState, zero_add, one_smul,
    norm_smul, Real.norm_eq_abs]
  norm_num
  nlinarith [sq_pos_of_pos hnorm_pos]



/-- V7 (5.6) 中 Z={a=0} 的实际 a.e. 零区条件。
来自已构造恢复映射与分支权重；并未把整个计算域缩小到 Ω₊。 -/
theorem physical_zero_on_absorption_zero (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) :
    ∀ᵐ x ∂ν, C.a x = 0 →
      physicalX ν C U.ψx x = 0 ∧ physicalY ν C U.ψy x = 0 := by
  have hx := physicalL2_zero_on_zero ν C.wx C.wx_measurable C.wx_gap U.ψx
  have hy := physicalL2_zero_on_zero ν C.wy C.wy_measurable C.wy_gap U.ψy
  filter_upwards [hx, hy] with x hx_zero hy_zero
  intro ha_zero
  have hwx_zero : C.wx x = 0 := (C.wx_eq_zero_iff x).mpr ha_zero
  have hwy_zero : C.wy x = 0 := (C.wy_eq_zero_iff x).mpr ha_zero
  exact ⟨hx_zero hwx_zero, hy_zero hwy_zero⟩

/-- (5.6) 后嵌入的二维平方和版本；普通向量长度明确按分量平方相加。 -/
theorem auxiliary_embedding_square (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) :
    ‖physicalX ν C U.ψx‖ ^ 2 + ‖physicalY ν C U.ψy‖ ^ 2 ≤
      ‖U.ψx‖ ^ 2 + ‖U.ψy‖ ^ 2 :=
  add_le_add
    (physicalL2_norm_sq_le ν C.wx C.wx_measurable C.wx_gap U.ψx)
    (physicalL2_norm_sq_le ν C.wy C.wy_measurable C.wy_gap U.ψy)

/-- (6.1) 的条件性空间约束，固定使用本项目实际零延拓映射。
尚待 v0.3.2 及具体 Sobolev 实现赋予空间域以真实梯度/零迹含义。 -/
def FieldSpatialConstraint (ν : Measure α) (C : SpatialAbsorption α)
    (spatial : ConditionalSpatialDomain ν) (U : FieldState ν C.wx C.wy) : Prop :=
  ConditionalSpatialConstraint spatial (physicalX ν C) (physicalY ν C) U


/-- V7 (6.4) 的论文专用 E₇：K 固定为 (5.2) 的 8μ(ε+2κ)C_P²，
两层固定取同源路径的 base/first。C_P 此处仍是参数，未证明 Poincaré。 -/
def energy7 (ν : Measure α) (C : SpatialAbsorption α) (ε κ τ μ C_P : ℝ)
    {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I) (t : ℝ) : ℝ :=
  twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ C_P) (path.base t) (path.first t)

/-- V7 (6.5) 的论文两层候选平方，使用同一个 K 和同源两层。
其中 N₀²、N₁² 分别是 graphSquare 在 base、first 上的值。 -/
def graphSquare7 (ν : Measure α) (C : SpatialAbsorption α) (ε κ μ C_P : ℝ)
    {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I) (t : ℝ) : ℝ :=
  twoLayerGraphSquare ε κ μ (scaleK ε κ μ C_P) (path.base t) (path.first t)

/-- E₇ 的真实求导仍是两个明确内积表达式的和，不是 (7.8) 的 PDE 能量律。
只用同源路径导数及固定 K；后续 v0.3.2 才能代入演化和 Green 关系。 -/
theorem hasDerivAt_energy7 (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ C_P : ℝ) {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (energy7 ν C ε κ τ μ C_P path)
      (fieldEnergyRate ν C ε κ τ μ (path.base t) (path.first t) +
        scaleK ε κ μ C_P * fieldEnergyRate ν C ε κ τ μ (path.first t) (path.second t)) t :=
  hasDerivAt_sameSourceEnergy ν C ε κ τ μ (scaleK ε κ μ C_P) path ht

namespace SpaceExample

/-- 仅用于接口测试的分离吸收：c=4、S=1、p=1、r=0。
主定理仍允许全零和双向吸收；本例选择边层以得到非零加权分量。 -/
def absorption : SpatialAbsorption (ℝ × ℝ) :=
  SpatialAbsorption.separated 4 1 (by norm_num) (fun _ => 1) (fun _ => 0)
    measurable_const measurable_const (by intro x; norm_num) (by intro x; norm_num)
    (by intro x; norm_num) (by intro x; norm_num) (by norm_num)

/-- 实例的整个域是单位开矩形，普通场与加权场均在此测度上取商。 -/
abbrev ν : Measure (ℝ × ℝ) := rectangleMeasure 0 1 0 1

/-- 单位矩形的实际二维 Lebesgue 测度为 1；用于常数 L² 成员与非零证据。 -/
theorem measure_univ : ν Set.univ = 1 := by
  simp [ν, rectangleMeasure, rectangleDomain, Measure.volume_eq_prod,
    Measure.prod_prod]

instance : IsFiniteMeasure ν := ⟨by rw [measure_univ]; norm_num⟩

instance : NeZero ν := ⟨by
  intro hzero
  have hmass := measure_univ
  rw [hzero] at hmass
  simp at hmass⟩

/-- 本例的 w_x=4；只用于构造实例，不把有界权重加入一般定理。 -/
theorem wx_value (x : ℝ × ℝ) : absorption.wx x = 4 := by
  norm_num [absorption, SpatialAbsorption.separated, SpatialAbsorption.wx,
    energyWeightX, absorptionSum]

/-- 平方根坐标 X₀=1 的真实加权成员；恢复后物理分量 ψx=1/2。
成员资格由单位矩形有限测度与实际 L² 构造给出。 -/
def seed : WeightedL2 ν absorption.wx :=
  weightedConstant ν absorption.wx (fun x => by rw [wx_value]; norm_num)

/-- seed 在 L² 商类中非零；证明使用测度非零，而非任取一点的函数值。 -/
theorem seed_ne_zero : seed ≠ 0 :=
  weightedConstant_ne_zero ν absorption.wx _

/-- 单位矩形上的实际非零非恒定空间值路径，调用整个单层空间能量求导定理。
材料取 ε=κ=τ=μ=1；这是计算接口实例，没有声称满足完整 PDE。 -/
theorem hasDerivAt_energy (t : ℝ) :
    HasDerivAt (fun s => fieldEnergy ν absorption 1 1 1 1
      (auxiliaryPath ν absorption seed s)) ((t + 1) * ‖seed‖ ^ 2) t :=
  hasDerivAt_auxiliaryPath_energy ν absorption 1 1 1 1 seed t

/-- 上述实例确实非恒定，且调用一般状态路径结论而非只检验数值代入。 -/
theorem energy_nonconstant :
    fieldEnergy ν absorption 1 1 1 1 (auxiliaryPath ν absorption seed 0) <
      fieldEnergy ν absorption 1 1 1 1 (auxiliaryPath ν absorption seed 1) :=
  auxiliaryPath_energy_nonconstant ν absorption 1 1 1 1 seed seed_ne_zero

end SpaceExample

end LeanPML.PML
