import LeanPML.PML.DissipationClosure
import LeanPML.PML.PhysicalControl
import LeanPML.PML.BalanceAbstract
import LeanPML.Time.Monotonicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# V7 (6.8)–(6.10)：有限时间区间的条件性能量定理

先读 StateContinuousOn，再读 energy7_antitoneOn_Conditional 与
energy7_integral_balance_Conditional。闭区间连续性逐个要求普通/加权空间路径连续；
SameSourcePath 的导数和 primitive 方程仅在 (0,T) 内要求。
积分平衡还需 second.R=P_tt 连续，它比单调性多用了一项时间正则性。
Green、同一迹下的 Poincaré 及时间/空间交换仍是具体矩形模型待兑现的接口。
-/

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace Interval
open LeanPML.Analysis

namespace LeanPML.PML

variable {α : Type*} [MeasurableSpace α]

/-- 由 V7 (6.6) 提取的闭区间正则性，原文未单列。
每个字段是实际空间路径的 ContinuousOn；ψ 的连续性在加权范数中要求。
这里没有能量连续、耗散符号或单调性字段，下面从这些原始条件逐项推导。 -/
structure StateContinuousOn {ν : Measure α} {wx wy : α → ℝ}
    (U : ℝ → FieldState ν wx wy) (I : Set ℝ) : Prop where
  v : ContinuousOn (fun t => (U t).v) I
  V : ContinuousOn (fun t => (U t).V) I
  R : ContinuousOn (fun t => (U t).R) I
  z : ContinuousOn (fun t => (U t).z) I
  ψx : ContinuousOn (fun t => (U t).ψx) I
  ψy : ContinuousOn (fun t => (U t).ψy) I
  Λx : ContinuousOn (fun t => (U t).Λx) I
  Λy : ContinuousOn (fun t => (U t).Λy) I

/-- (6.2) 的时间连续性辅助结论，原文未单列：固定有界乘子的二次型连续。
只使用 mathlib 连续线性映射与内积的连续性，未交换点态极限和积分。 -/
theorem continuousOn_coefficient_quadratic (ν : Measure α) (m : BoundedCoefficient α)
    {X : ℝ → ScalarL2 ν} {I : Set ℝ} (hX : ContinuousOn X I) :
    ContinuousOn (fun t => ⟪m.operator ν (X t), X t⟫_ℝ) I :=
  ((m.operator ν).continuous.comp_continuousOn hX).inner hX

/-- V7 (6.2) 的实际单层能量在闭集上连续。
电块、极化块和加权空间平方项分别由原路径连续性取得；不要求端点导数。 -/
theorem continuousOn_fieldEnergy (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) {U : ℝ → FieldState ν C.wx C.wy} {I : Set ℝ}
    (hU : StateContinuousOn U I) :
    ContinuousOn (fun t => fieldEnergy ν C ε κ τ μ (U t)) I := by
  have helectric : ContinuousOn (fun t => fieldElectric ν C ε (U t)) I := by
    exact ((hU.V.norm.pow 2).add
      ((hU.v.inner hU.V).const_mul (2*C.c)) |>.add
      (continuousOn_coefficient_quadratic ν (electricCoefficient C) hU.v)).const_mul (ε/2)
  have hcross : ContinuousOn (fun t =>
      ⟪(polarCrossCoefficient C τ).operator ν (U t).R, (U t).z⟫_ℝ) I :=
    (((polarCrossCoefficient C τ).operator ν).continuous.comp_continuousOn hU.R).inner hU.z
  have hpolar : ContinuousOn (fun t => fieldPolar ν C κ τ (U t)) I := by
    exact (((continuousOn_coefficient_quadratic ν (polarRCoefficient C τ) hU.R).add
      (hcross.const_mul 2)).add
      (continuousOn_coefficient_quadratic ν (polarZCoefficient C τ) hU.z)).div_const (2*κ)
  have hspatial : ContinuousOn (fun t => fieldSpatial (U t)) I :=
    ((((hU.Λx.norm.pow 2).div_const 2).add ((hU.Λy.norm.pow 2).div_const 2)).add
      ((hU.ψx.norm.pow 2).div_const 2)).add ((hU.ψy.norm.pow 2).div_const 2)
  exact ((helectric.const_mul μ).add (hpolar.const_mul μ)).add hspatial

/-- V7 (6.4) 的两层能量连续性，从两层普通/加权坐标的连续性推出。
闭区间 I 可以与 path 的开区间 J 不同；因此没有偷偷要求端点双侧可导。 -/
theorem continuousOn_energy7 (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) {I J : Set ℝ} (path : SameSourcePath ν C.wx C.wy J)
    (hbase : StateContinuousOn path.base I) (hfirst : StateContinuousOn path.first I) :
    ContinuousOn (energy7 ν C ε κ τ μ CP path) I :=
  (continuousOn_fieldEnergy ν C ε κ τ μ hbase).add
    ((continuousOn_fieldEnergy ν C ε κ τ μ hfirst).const_mul (scaleK ε κ μ CP))

/-- V7 (7.7) 的实际单层耗散连续性，原文未单列。
固定耗散系数是已有有界乘子；无界能量权重仍由 WeightedL2 承载。
额外输入 Rdot 的 L² 连续性，而不假定它的平方积分已经连续。 -/
theorem continuousOn_fieldDissipation (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) {U : ℝ → FieldState ν C.wx C.wy} {Rdot : ℝ → ScalarL2 ν}
    {I : Set ℝ} (hU : StateContinuousOn U I) (hRdot : ContinuousOn Rdot I) :
    ContinuousOn (fun t => fieldDissipation ν C ε κ τ μ (U t) (Rdot t)) I := by
  have helectric : ContinuousOn (fun t => fieldElectricRemainder ν C ε (U t)) I :=
    ((continuousOn_coefficient_quadratic ν
      (C.aCoeff.sub (BoundedCoefficient.const C.c)) hU.V).add
      (continuousOn_coefficient_quadratic ν (bcCoefficient C) hU.v)).const_mul ε
  have hpolar : ContinuousOn (fun t => fieldPolarRemainder ν C κ τ (U t) (Rdot t)) I :=
    ((((hRdot.norm.pow 2).const_mul τ).add
      (continuousOn_coefficient_quadratic ν (polarRemainderCoefficient C τ) hU.R)).add
      (continuousOn_coefficient_quadratic ν (bcCoefficient C) hU.z)).div_const κ
  -- Λ−ψ 的连续性来自已证明的 physicalX/Y 连续映射；不用任意点取值。
  have hx : ContinuousOn (fun t => spatialComponentX (U t)) I :=
    hU.Λx.sub ((physicalX ν C).continuous.comp_continuousOn hU.ψx)
  have hy : ContinuousOn (fun t => spatialComponentY (U t)) I :=
    hU.Λy.sub ((physicalY ν C).continuous.comp_continuousOn hU.ψy)
  have hspatial : ContinuousOn (fun t => fieldSpatialDissipation ν C (U t)) I :=
    (((continuousOn_coefficient_quadratic ν C.plusX hU.Λx).add
      (continuousOn_coefficient_quadratic ν C.minusX hx)).add
      (continuousOn_coefficient_quadratic ν C.plusY hU.Λy)).add
      (continuousOn_coefficient_quadratic ν C.minusY hy)
  exact ((helectric.const_mul μ).add (hpolar.const_mul μ)).add hspatial

/-- V7 (7.8) 耗散的时间连续性，供 (6.9) 的 FTC 使用。
first.R=P_t 来自原层真实导数；second.R=P_tt 来自导数层真实导数。
second.R 在闭区间连续是积分平衡的额外正则性，不用于证明单调性。 -/
theorem continuousOn_dissipation7 (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) {I J : Set ℝ} (path : SameSourcePath ν C.wx C.wy J)
    (hbase : StateContinuousOn path.base I) (hfirst : StateContinuousOn path.first I)
    (hsecondR : ContinuousOn (fun t => (path.second t).R) I) :
    ContinuousOn (dissipation7 ν C ε κ τ μ CP path) I :=
  (continuousOn_fieldDissipation ν C ε κ τ μ hbase hfirst.R).add
    ((continuousOn_fieldDissipation ν C ε κ τ μ hfirst hsecondR).const_mul
      (scaleK ε κ μ CP))

/-- V7 (6.9) 的纯时间接口：闭区间连续、内部导数为 −D、且 D 在区间可积，
推出有限区间平衡。这里允许通用输入；最终 PML 入口会从场正则性证明这些条件。
调用 mathlib FTC，不需要端点普通双侧导数；a=b 也包含在 hab 中。 -/
theorem integral_balance_of_hasDerivAt {F D : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn F (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt F (-D t) t)
    (hint : IntervalIntegrable D volume a b) :
    F b + ∫ t in a..b, D t = F a := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint.neg
  rw [intervalIntegral.integral_neg] at hFTC
  linarith


/-- 有限区间的原始输入包，对应 (6.1)、(6.6) 和 primitive 演化。
path 的时间集合严格取 (0,T)，端点只要求分量连续与静态兼容。
static_base/first 仅含极化、空间和零迹约束；T=0 时这些条件仍有数学内容。
结构中没有 (9.5)、耗散符号、能量率、单调性或积分平衡字段。
Poincaré 的零迹子域固定为 G.trace 的核，避免前后使用不一致的边界接口。 -/
structure FiniteIntervalProblemConditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
    (ε κ τ μ CP T : ℝ)
    (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
      ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
        (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2)) where
  T_nonneg : 0 ≤ T
  path : SameSourcePath ν C.wx C.wy (Set.Ioo 0 T)
  regular : ConditionalSpatialPath G C path
  base_evolution : ∀ t ∈ Set.Ioo 0 T, PrimitiveAtConditional G C ε κ τ μ
    (path.base t) (path.first t) (regular.base_v t) (regular.base_flux t)
  continuous_base : StateContinuousOn path.base (Set.Icc 0 T)
  continuous_first : StateContinuousOn path.first (Set.Icc 0 T)
  static_base : ∀ t ∈ Set.Icc 0 T, StateCoercivityConstraints ν C G.spatial
    (ConditionalPoincare.ofGreenTrace G CP estimate) κ τ (path.base t)
  static_first : ∀ t ∈ Set.Icc 0 T, StateCoercivityConstraints ν C G.spatial
    (ConditionalPoincare.ofGreenTrace G CP estimate) κ τ (path.first t)


/-- (6.10)、(8.4)–(8.8) 接到初始能量后的输出包。
各字段是结论，不是解或路径的输入；每一右端都使用同一真实 energy7(path,0)。 -/
structure PhysicalInitialControlBounds (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I) (t : ℝ) : Prop where
  physical : ε * ‖(path.base t).V‖^2 +
    μ * (‖reconstructHx μ (path.base t)‖^2 + ‖reconstructHy μ (path.base t)‖^2) +
    κ⁻¹ * ‖(path.base t).R‖^2 ≤ (4/μ) * energy7 ν C ε κ τ μ CP path 0
  displacement : ‖(path.base t).v‖^2 ≤ 8*CP^2 * energy7 ν C ε κ τ μ CP path 0
  auxiliary : ‖physicalX ν C (path.base t).ψx‖^2 +
    ‖physicalY ν C (path.base t).ψy‖^2 ≤ 4 * energy7 ν C ε κ τ μ CP path 0
  primitivePolar : ‖reconstructQ κ τ (path.base t)‖^2 ≤
    (16*κ^2*CP^2 + 8*κ*τ^2/μ) * energy7 ν C ε κ τ μ CP path 0
  electricMemory : ‖reconstructZ1 ν C ε (path.base t)‖^2 ≤
    8*ε^2*C.S^4*CP^2 * energy7 ν C ε κ τ μ CP path 0
  polarMemory : ‖reconstructZ2 ν C κ τ (path.base t)‖^2 ≤
    C.S^4*(16*κ^2*CP^2 + 8*κ*τ^2/μ) * energy7 ν C ε κ τ μ CP path 0
  magneticAuxiliary : ‖reconstructAuxX ν C (path.base t)‖^2 +
    ‖reconstructAuxY ν C (path.base t)‖^2 ≤ 4*C.S^2 * energy7 ν C ε κ τ μ CP path 0


/-- T=0 时，[0,0] 是单点；任意实际 energy7 路径都单调不增。
本条不输入演化、连续性或导数。能量非负另由闭区间静态约束证明。 -/
theorem energy7_antitoneOn_zero_time (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (path : SameSourcePath ν C.wx C.wy (Set.Ioo 0 0)) :
    AntitoneOn (energy7 ν C ε κ τ μ CP path) (Set.Icc 0 0) :=
  LeanPML.Time.antitoneOn_Icc_self _ 0

section FiniteInterval
variable {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
variable (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
variable (ε κ τ μ CP T : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
variable (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
  ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
    (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2))
variable (problem : FiniteIntervalProblemConditional G C ε κ τ μ CP T estimate)

include hp in
/-- (6.7) 在有限闭区间每个时刻的版本，包括 T=0 和两个端点。
调用 v0.3.3 已证的图范数界；端点兼容来自显式 static 字段，不从空内部方程推出。 -/
theorem energy7_bounds_on_Icc_Conditional {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    graphSquare7 ν C ε κ μ CP problem.path t / 4 ≤
      energy7 ν C ε κ τ μ CP problem.path t ∧
    energy7 ν C ε κ τ μ CP problem.path t ≤
      graphSquare7 ν C ε κ μ CP problem.path t :=
  energy7_bounds_Conditional ν C ε κ τ μ CP hp G.spatial
    (ConditionalPoincare.ofGreenTrace G CP estimate) problem.path t
    (problem.static_base t ht) (problem.static_first t ht)

include hp in
/-- 从 (6.7) 与实际平方范数非负推出能量非负。
此条完全是静态结论，不需要任何内部导数，也不从耗散符号倒推能量正性。 -/
theorem energy7_nonneg_on_Icc_Conditional {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    0 ≤ energy7 ν C ε κ τ μ CP problem.path t := by
  have hbase_nonneg : 0 ≤ graphSquare ε κ μ (problem.path.base t) :=
    graphSquare_nonneg ε κ μ hp.ε_pos.le hp.κ_pos.le hp.μ_pos.le _
  have hfirst_nonneg : 0 ≤ graphSquare ε κ μ (problem.path.first t) :=
    graphSquare_nonneg ε κ μ hp.ε_pos.le hp.κ_pos.le hp.μ_pos.le _
  have hK_pos : 0 < scaleK ε κ μ CP :=
    scaleK_pos ε κ μ CP hp.ε_pos hp.κ_pos hp.μ_pos hp.CP_pos
  have hgraph_nonneg : 0 ≤ graphSquare7 ν C ε κ μ CP problem.path t :=
    add_nonneg hbase_nonneg (mul_nonneg hK_pos.le hfirst_nonneg)
  have hbound := (energy7_bounds_on_Icc_Conditional G C ε κ τ μ CP T hp
    estimate problem ht).1
  exact (div_nonneg hgraph_nonneg (by norm_num)).trans hbound


include hp in
/-- (7.8) 的有限区间桥接：原演化只要求在 (0,T)，因此端点不增加导数要求。
调用 v0.3.2 的同源两层能量律；这里尚未使用耗散非负性。 -/
theorem hasDerivAt_energy7_on_Ioo_Conditional {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (energy7 ν C ε κ τ μ CP problem.path)
      (-dissipation7 ν C ε κ τ μ CP problem.path t) t := by
  have ht_interior : t ∈ interior (Set.Ioo 0 T) := by
    simpa only [isOpen_Ioo.interior_eq] using ht
  exact hasDerivAt_energy7_Conditional G C ε κ τ μ CP (ne_of_gt hp.κ_pos)
    problem.path problem.regular problem.base_evolution ht_interior

/-- (6.9) 使用的耗散时间可积性。闭区间普通/加权状态连续，另要求 P_tt 连续，
便可在任意 [t₁,t₂]⊆[0,T] 积分。来自实际二次型的连续性，不靠积分的总定义。 -/
theorem intervalIntegrable_dissipation7_Conditional
    (hsecondR : ContinuousOn (fun t => (problem.path.second t).R) (Set.Icc 0 T))
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂) (ht₂ : t₂ ≤ T) :
    IntervalIntegrable (dissipation7 ν C ε κ τ μ CP problem.path) volume t₁ t₂ := by
  have hcont := continuousOn_dissipation7 ν C ε κ τ μ CP problem.path
    problem.continuous_base problem.continuous_first hsecondR
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Icc 0 T :=
    fun _ hs => ⟨ht₁.trans hs.1, hs.2.trans ht₂⟩
  exact (hcont.mono hsub).intervalIntegrable_of_Icc ht₁₂

include hp in
/-- V7 (6.9) 的真实时间积分平衡。
从原演化推导 HasDerivAt，从场正则性推导 energy7 连续与 D₇ 可积，再调用 FTC。
这一步与单调性不同，甚至不需要 D₇ 的符号；t₁=t₂、t₁=0、t₂=T 均可直接使用。 -/
theorem energy7_integral_balance_Conditional
    (hsecondR : ContinuousOn (fun t => (problem.path.second t).R) (Set.Icc 0 T))
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂) (ht₂ : t₂ ≤ T) :
    energy7 ν C ε κ τ μ CP problem.path t₂ +
      ∫ t in t₁..t₂, dissipation7 ν C ε κ τ μ CP problem.path t =
      energy7 ν C ε κ τ μ CP problem.path t₁ := by
  have hcontinuous := continuousOn_energy7 ν C ε κ τ μ CP problem.path
    problem.continuous_base problem.continuous_first
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Icc 0 T :=
    fun _ hs => ⟨ht₁.trans hs.1, hs.2.trans ht₂⟩
  have hderivative : ∀ t ∈ Set.Ioo t₁ t₂,
      HasDerivAt (energy7 ν C ε κ τ μ CP problem.path)
        (-dissipation7 ν C ε κ τ μ CP problem.path t) t := by
    intro t ht
    have ht_global : t ∈ Set.Ioo 0 T :=
      ⟨lt_of_le_of_lt ht₁ ht.1, lt_of_lt_of_le ht.2 ht₂⟩
    exact hasDerivAt_energy7_on_Ioo_Conditional G C ε κ τ μ CP T hp
      estimate problem ht_global
  have hintegrable := intervalIntegrable_dissipation7_Conditional G C ε κ τ μ CP T
    estimate problem hsecondR ht₁ ht₁₂ ht₂
  exact integral_balance_of_hasDerivAt ht₁₂ (hcontinuous.mono hsub) hderivative hintegrable

/-- 单点时间区间的积分平衡无需任何内部方程或端点导数。
这是 mathlib intervalIntegral.integral_same 的直接实例，适用于 T=0。 -/
theorem energy7_integral_balance_same (t : ℝ) :
    energy7 ν C ε κ τ μ CP problem.path t +
      ∫ s in t..t, dissipation7 ν C ε κ τ μ CP problem.path s =
      energy7 ν C ε κ τ μ CP problem.path t := by
  simp only [intervalIntegral.integral_same, add_zero]



include hp in
/-- (6.9) 取 t₁=0、t₂=T 的端点版本；T=0 也直接由同一 FTC 接口覆盖。
端点只有区间内连续性和静态约束，不额外要求普通双侧导数。 -/
theorem energy7_integral_balance_endpoints_Conditional
    (hsecondR : ContinuousOn (fun t => (problem.path.second t).R) (Set.Icc 0 T)) :
    energy7 ν C ε κ τ μ CP problem.path T +
      ∫ t in (0 : ℝ)..T, dissipation7 ν C ε κ τ μ CP problem.path t =
      energy7 ν C ε κ τ μ CP problem.path 0 :=
  energy7_integral_balance_Conditional G C ε κ τ μ CP T hp estimate problem
    hsecondR le_rfl problem.T_nonneg le_rfl

variable [Nonempty α]

include hp in
/-- V7 (6.8) 的导数符号结论：先由原演化取得真实导数，再由第 9 节闭合估计
证明其非正。Nonempty α 仅说明空间载体非空（矩形载体 ℝ×ℝ 自动满足），
用于从吸收幅度假设取得 S≥0，不要求测度非零或吸收有正下界。 -/
theorem energy7_derivative_nonpos_Conditional {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (energy7 ν C ε κ τ μ CP problem.path)
      (-dissipation7 ν C ε κ τ μ CP problem.path t) t ∧
      -dissipation7 ν C ε κ τ μ CP problem.path t ≤ 0 := by
  have ht_interior : t ∈ interior (Set.Ioo 0 T) := by
    simpa only [isOpen_Ioo.interior_eq] using ht
  have hnonneg := dissipation7_nonneg_Conditional G C ε κ τ μ CP hp estimate
    problem.path problem.regular problem.base_evolution ht_interior
  exact ⟨hasDerivAt_energy7_on_Ioo_Conditional G C ε κ τ μ CP T hp estimate problem ht,
    neg_nonpos.mpr hnonneg⟩

include hp in
/-- (6.8) 的两种不同信息并列输出：真实能量导数，以及精确定量耗散下界。
结论仅对开区间成立；没有把内部方程扩展到端点。
空间耗散保留一半，Debye 平方项保留 μτ/(4κ)，不重复使用正项。 -/
theorem energy7_law_and_closure_Conditional {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (energy7 ν C ε κ τ μ CP problem.path)
      (-dissipation7 ν C ε κ τ μ CP problem.path t) t ∧
    (fieldSpatialDissipation ν C (problem.path.base t) +
      scaleK ε κ μ CP * fieldSpatialDissipation ν C (problem.path.first t))/2 +
      μ*τ/(4*κ) * (‖(problem.path.first t).R‖^2 +
        scaleK ε κ μ CP * ‖(problem.path.second t).R‖^2) ≤
      dissipation7 ν C ε κ τ μ CP problem.path t ∧
    0 ≤ dissipation7 ν C ε κ τ μ CP problem.path t := by
  have ht_interior : t ∈ interior (Set.Ioo 0 T) := by
    simpa only [isOpen_Ioo.interior_eq] using ht
  exact ⟨hasDerivAt_energy7_on_Ioo_Conditional G C ε κ τ μ CP T hp estimate problem ht,
    dissipation7_lower_Conditional G C ε κ τ μ CP hp estimate
      problem.path problem.regular problem.base_evolution ht_interior,
    dissipation7_nonneg_Conditional G C ε κ τ μ CP hp estimate
      problem.path problem.regular problem.base_evolution ht_interior⟩

include hp in
/-- V7 (6.9) 的有限闭区间单调性。
ContinuousOn 从实际场路径推出；内部真实导数与符号分别由能量律和耗散闭合取得。
复用 Time.antitoneOn_Icc_of_hasDerivAt_nonpos，无需端点可导，T=0 也适用。 -/
theorem energy7_antitoneOn_Conditional :
    AntitoneOn (energy7 ν C ε κ τ μ CP problem.path) (Set.Icc 0 T) := by
  have hcontinuous := continuousOn_energy7 ν C ε κ τ μ CP problem.path
    problem.continuous_base problem.continuous_first
  apply LeanPML.Time.antitoneOn_Icc_of_hasDerivAt_nonpos hcontinuous
  · intro t ht
    exact (energy7_derivative_nonpos_Conditional G C ε κ τ μ CP T hp estimate problem ht).1
  · intro t ht
    exact (energy7_derivative_nonpos_Conditional G C ε κ τ μ CP T hp estimate problem ht).2

include hp in
/-- (6.7)、(6.9) 合用得到 0≤E₇(t)≤E₇(0)。
非负性使用闭区间静态约束，初值上界使用单调性；二者逻辑来源不同。 -/
theorem energy7_initial_bounds_Conditional {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    0 ≤ energy7 ν C ε κ τ μ CP problem.path t ∧
      energy7 ν C ε κ τ μ CP problem.path t ≤ energy7 ν C ε κ τ μ CP problem.path 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, problem.T_nonneg⟩
  exact ⟨energy7_nonneg_on_Icc_Conditional G C ε κ τ μ CP T hp estimate problem ht,
    energy7_antitoneOn_Conditional G C ε κ τ μ CP T hp estimate problem hzero ht ht.1⟩

include hp in
/-- (6.7) 与单调性得到同源两层图平方的初值控制，保留原文因子 4。 -/
theorem graphSquare7_initial_bound_Conditional {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    graphSquare7 ν C ε κ μ CP problem.path t ≤
      4 * energy7 ν C ε κ τ μ CP problem.path 0 := by
  have hgraph := (energy7_bounds_on_Icc_Conditional G C ε κ τ μ CP T hp
    estimate problem ht).1
  have henergy := (energy7_initial_bounds_Conditional G C ε κ τ μ CP T hp
    estimate problem ht).2
  linarith



include hp in
/-- (6.10)、(8.4)–(8.8) 的兼容重构初值控制。
先调用 v0.3.3 实际 L² 重构估计，再用本轮单调性降低每个右端。
所有乘数非负由原材料正性与平方非负取得，没有加入目标控制式作为条件。 -/
theorem physicalControl_initial_Conditional {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    PhysicalInitialControlBounds ν C ε κ τ μ CP problem.path t := by
  have hcontrol := physicalControl_Conditional ν C ε κ τ μ CP hp G.spatial
    (ConditionalPoincare.ofGreenTrace G CP estimate) problem.path t
    (problem.static_base t ht) (problem.static_first t ht)
  have henergy := (energy7_initial_bounds_Conditional G C ε κ τ μ CP T hp
    estimate problem ht).2
  have hμ_pos : 0 < μ := hp.μ_pos
  have hκ_pos : 0 < κ := hp.κ_pos
  constructor
  · exact hcontrol.physical.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  · exact hcontrol.displacement.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  · exact hcontrol.auxiliary.trans (mul_le_mul_of_nonneg_left henergy (by norm_num))
  · exact hcontrol.primitivePolar.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  · exact hcontrol.electricMemory.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  · exact hcontrol.polarMemory.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  · exact hcontrol.magneticAuxiliary.trans (mul_le_mul_of_nonneg_left henergy (by positivity))

include hp in
/-- V7 定理 6.1 的条件性有限时间主结论汇总。
输出内部真实能量律与精确定量耗散下界、闭区间单调性和静态双边界、
能量/图平方/重构初值控制，以及真实积分平衡。
输入包只有原层演化、同源 HasDerivAt、空间接口及闭区间静态/连续条件；
额外的 second.R 连续用于 FTC。不是解存在、唯一性或严格衰减定理。 -/
theorem main_energy_estimate_Conditional
    (hsecondR : ContinuousOn (fun t => (problem.path.second t).R) (Set.Icc 0 T)) :
    AntitoneOn (energy7 ν C ε κ τ μ CP problem.path) (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (energy7 ν C ε κ τ μ CP problem.path)
        (-dissipation7 ν C ε κ τ μ CP problem.path t) t ∧
      (fieldSpatialDissipation ν C (problem.path.base t) +
        scaleK ε κ μ CP * fieldSpatialDissipation ν C (problem.path.first t))/2 +
        μ*τ/(4*κ) * (‖(problem.path.first t).R‖^2 +
          scaleK ε κ μ CP * ‖(problem.path.second t).R‖^2) ≤
        dissipation7 ν C ε κ τ μ CP problem.path t ∧
      0 ≤ dissipation7 ν C ε κ τ μ CP problem.path t) ∧
    (∀ t ∈ Set.Icc 0 T,
      (graphSquare7 ν C ε κ μ CP problem.path t / 4 ≤
        energy7 ν C ε κ τ μ CP problem.path t ∧
       energy7 ν C ε κ τ μ CP problem.path t ≤ graphSquare7 ν C ε κ μ CP problem.path t) ∧
      (0 ≤ energy7 ν C ε κ τ μ CP problem.path t ∧
       energy7 ν C ε κ τ μ CP problem.path t ≤ energy7 ν C ε κ τ μ CP problem.path 0) ∧
      graphSquare7 ν C ε κ μ CP problem.path t ≤ 4*energy7 ν C ε κ τ μ CP problem.path 0 ∧
      PhysicalInitialControlBounds ν C ε κ τ μ CP problem.path t) ∧
    (∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
      energy7 ν C ε κ τ μ CP problem.path t₂ +
        ∫ t in t₁..t₂, dissipation7 ν C ε κ τ μ CP problem.path t =
        energy7 ν C ε κ τ μ CP problem.path t₁) := by
  refine ⟨energy7_antitoneOn_Conditional G C ε κ τ μ CP T hp estimate problem, ?_, ?_, ?_⟩
  · intro t ht
    exact energy7_law_and_closure_Conditional G C ε κ τ μ CP T hp estimate problem ht
  · intro t ht
    exact ⟨energy7_bounds_on_Icc_Conditional G C ε κ τ μ CP T hp estimate problem ht,
      energy7_initial_bounds_Conditional G C ε κ τ μ CP T hp estimate problem ht,
      graphSquare7_initial_bound_Conditional G C ε κ τ μ CP T hp estimate problem ht,
      physicalControl_initial_Conditional G C ε κ τ μ CP T hp estimate problem ht⟩
  · intro t₁ t₂ ht₁ ht₁₂ ht₂
    exact energy7_integral_balance_Conditional G C ε κ τ μ CP T hp estimate problem
      hsecondR ht₁ ht₁₂ ht₂

end FiniteInterval

end LeanPML.PML
