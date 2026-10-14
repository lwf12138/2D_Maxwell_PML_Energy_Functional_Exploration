import LeanPML.PML.WeakCoefficientTransport

/-!
# V7 一般分离弱系数的最终原系统入口

原八式先在输入原弱系数的区域代表下成立；证明内部构造连续代表并搬运方程。
正长度分支采用 (6.6) 的真实图空间 Cᵏ 条件，T=0 分支保留独立初始 jet 兼容。
两者都使用原文精确矩形 Poincaré 常数，不加入 Green 或目标能量假设。
-/
noncomputable section
open MeasureTheory Set Filter
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML
namespace RawWeakRegionalAbsorption
variable {D : Rect} (A : RawWeakRegionalAbsorption D)

/-- x/y 权重在实际测度下相等；y 以 swap.wx 与既有历史接口一致。 -/
theorem raw_weights_ae :
    A.rawSpatial.wx =ᵐ[D.measure] A.represented.spatial.wx ∧
    A.rawSpatial.swap.wx =ᵐ[D.measure] A.represented.spatial.swap.wx := by
  constructor
  · filter_upwards [A.rawSpatial_ae.1,A.rawSpatial_ae.2] with z hp hr
    change energyWeightX A.c _ _ = energyWeightX A.c _ _
    rw [hp,hr]
  · filter_upwards [A.rawSpatial_ae.1,A.rawSpatial_ae.2] with z hp hr
    change energyWeightX A.c _ _ = energyWeightX A.c _ _
    simp only [SpatialAbsorption.swap]
    rw [hp,hr]

/-- 初始加权坐标的等距搬运，不预设全时段加权成员。 -/
def initialX (X : WeightedL2 D.measure A.rawSpatial.wx) :
    WeightedL2 D.measure A.represented.spatial.wx :=
  weightedChangeRepresentative D.measure _ _ A.raw_weights_ae.1 X

def initialY (Y : WeightedL2 D.measure A.rawSpatial.swap.wx) :
    WeightedL2 D.measure A.represented.spatial.swap.wx :=
  weightedChangeRepresentative D.measure _ _ A.raw_weights_ae.2 Y

/-- 原初值的物理场在换代表后不变。 -/
theorem initial_physical (X : WeightedL2 D.measure A.rawSpatial.wx)
    (Y : WeightedL2 D.measure A.rawSpatial.swap.wx) :
    physicalL2 D.measure A.represented.spatial.wx A.represented.spatial.wx_measurable
      A.represented.spatial.wx_gap (A.initialX X) =
        physicalL2 D.measure A.rawSpatial.wx A.rawSpatial.wx_measurable A.rawSpatial.wx_gap X ∧
    physicalL2 D.measure A.represented.spatial.swap.wx A.represented.spatial.swap.wx_measurable
      A.represented.spatial.swap.wx_gap (A.initialY Y) =
        physicalL2 D.measure A.rawSpatial.swap.wx A.rawSpatial.swap.wx_measurable A.rawSpatial.swap.wx_gap Y :=
  ⟨physical_changeRepresentative D.measure _ _ A.raw_weights_ae.1 _ _ _ _ X,
    physical_changeRepresentative D.measure _ _ A.raw_weights_ae.2 _ _ _ _ Y⟩
end RawWeakRegionalAbsorption

namespace Weak
namespace OriginalInterval
variable {D : Rect} {A : RawWeakRegionalAbsorption D} {ε κ τ μ T : ℝ}
variable (O : OriginalInterval D A.rawSpatial ε κ τ μ T)

/-- 八式与初始兼容由 a.e. 乘子相等迁移，原场和历史逐时刻不变。 -/
def representedInterval : OriginalInterval D A.represented.spatial ε κ τ μ T :=
  O.changeCoefficients A.rawSpatial_ae.1 A.rawSpatial_ae.2

/-- 真正 Cᵏ 正则性只依赖原场/历史路径，不依赖系数代表选择。 -/
def representedCk (R : V7ClosedCkCore O) : V7ClosedCkCore O.representedInterval :=
  ⟨R.u_graph,R.u_value,R.polar,R.flux⟩

/-- 时间 jet 逐字段保留真实导数证据；用于 T=0 分支及既有非零回归。 -/
def representedJet (J : OriginalJet O) : OriginalJet O.representedInterval :=
  { J with }

/-- 退化区间的初始兼容按同一个原系数乘子搬运，不由空内部条件推出。 -/
theorem representedDegenerate (J : OriginalJet O) (h : DegenerateJetCompatibility O J) :
    DegenerateJetCompatibility O.representedInterval (O.representedJet J) := by
  obtain ⟨hp,hr,_,_⟩ := spatial_operators_eq_ae A.rawSpatial A.represented.spatial
    A.rawSpatial_ae.1 A.rawSpatial_ae.2
  refine ⟨h.polar,?_,?_⟩
  · intro hT
    simpa only [representedJet,representedInterval,OriginalInterval.changeCoefficients,
      OriginalInterval.u,← hp,← hr] using h.spatialX hT
  · intro hT
    simpa only [representedJet,representedInterval,OriginalInterval.changeCoefficients,
      OriginalInterval.u,← hp,← hr] using h.spatialY hT

/-- 正长度一般 W¹,∞ 原系统主入口。
代表存在、八式迁移和初值加权识别全部在证明内兑现。
输出的 fields 仍是输入 O.fields；精确 (6.7)–(6.10) 及 (8.4)–(8.8) 沿用已证主链。 -/
theorem main_energy_GeneralWeakCk (R : V7ClosedCkCore O) (hT : 0 < T)
    (hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hμ : 0 < μ)
    (hsmall : A.c ≤ threshold ε κ τ μ (sharpPoincareConstant D))
    (X : WeightedL2 D.measure A.rawSpatial.wx) (Y : WeightedL2 D.measure A.rawSpatial.swap.wx)
    (hX : physicalL2 D.measure A.rawSpatial.wx A.rawSpatial.wx_measurable A.rawSpatial.wx_gap X = O.φx 0)
    (hY : physicalL2 D.measure A.rawSpatial.swap.wx A.rawSpatial.swap.wx_measurable A.rawSpatial.swap.wx_gap Y = O.φy 0) :
    let O' := V7ClosedCkCore.canonicalInterval (O := O.representedInterval) hT
    let J := (((O.representedCk R).regularity hT).toTimeRegularity hT).toOriginalJet
    SharpEnergyConclusions O' J (A.initialX X) (A.initialY Y) ∧
      ∀ t ∈ Icc 0 T, SharpOriginalAuxiliaryBounds O'
        (O'.sharpEnergy J (A.initialX X) (A.initialY Y) 0) t := by
  apply main_energy_RawRegionalSharpCk D A ε κ τ μ T hε hκ hτ hμ hT hsmall
    O.representedInterval (O.representedCk R) (A.initialX X) (A.initialY Y)
  · exact (A.initial_physical X Y).1.trans hX
  · exact (A.initial_physical X Y).2.trans hY

/-- 正长度 Cᵏ 主入口的配套当前能量控制；常数与 (8.4)–(8.8) 原式一致。
由同一规范化原解和已构造 jet 调用静态重构控制，未另加导数槽假设。 -/
theorem auxiliary_current_GeneralWeakCk (R : V7ClosedCkCore O) (hT : 0 < T)
    (hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hμ : 0 < μ)
    (hsmall : A.c ≤ threshold ε κ τ μ (sharpPoincareConstant D))
    (X : WeightedL2 D.measure A.rawSpatial.wx) (Y : WeightedL2 D.measure A.rawSpatial.swap.wx)
    (hX : physicalL2 D.measure A.rawSpatial.wx A.rawSpatial.wx_measurable A.rawSpatial.wx_gap X = O.φx 0)
    (hY : physicalL2 D.measure A.rawSpatial.swap.wx A.rawSpatial.swap.wx_measurable A.rawSpatial.swap.wx_gap Y = O.φy 0) :
    let O' := V7ClosedCkCore.canonicalInterval (O := O.representedInterval) hT
    let J := (((O.representedCk R).regularity hT).toTimeRegularity hT).toOriginalJet
    ∀ t ∈ Icc 0 T, SharpOriginalAuxiliaryBounds O'
      (O'.sharpEnergy J (A.initialX X) (A.initialY Y) t) t := by
  let O' := V7ClosedCkCore.canonicalInterval (O := O.representedInterval) hT
  let J := (((O.representedCk R).regularity hT).toTimeRegularity hT).toOriginalJet
  have hdeg : DegenerateJetCompatibility O' J :=
    ⟨fun hz => (hT.ne' hz).elim, fun hz => (hT.ne' hz).elim, fun hz => (hT.ne' hz).elim⟩
  change ∀ t ∈ Icc 0 T, SharpOriginalAuxiliaryBounds O'
    (O'.sharpEnergy J (A.initialX X) (A.initialY Y) t) t
  intro t ht
  exact O'.sharp_original_auxiliary_control J (A.initialX X) (A.initialY Y)
    ⟨hε,hκ,hτ,hμ,sharpPoincareConstant_pos D,hsmall⟩
    ((A.initial_physical X Y).1.trans hX) ((A.initial_physical X Y).2.trans hY) hdeg ht

/-- 任意 T≥0 的显式 jet 分支；主要用于实际解限制到单点。
要求初始导数层兼容而非在端点要求 PDE，正长度可用前一 Cᵏ 入口免去独立槽识别。 -/
theorem main_energy_GeneralWeakJet (J : OriginalJet O)
    (hdeg : DegenerateJetCompatibility O J)
    (hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hμ : 0 < μ)
    (hsmall : A.c ≤ threshold ε κ τ μ (sharpPoincareConstant D))
    (X : WeightedL2 D.measure A.rawSpatial.wx) (Y : WeightedL2 D.measure A.rawSpatial.swap.wx)
    (hX : physicalL2 D.measure A.rawSpatial.wx A.rawSpatial.wx_measurable A.rawSpatial.wx_gap X = O.φx 0)
    (hY : physicalL2 D.measure A.rawSpatial.swap.wx A.rawSpatial.swap.wx_measurable A.rawSpatial.swap.wx_gap Y = O.φy 0) :
    SharpEnergyConclusions O.representedInterval (O.representedJet J) (A.initialX X) (A.initialY Y) := by
  exact O.representedInterval.main_energy_estimate_SharpWeakOriginal (O.representedJet J)
    (A.initialX X) (A.initialY Y) ⟨hε,hκ,hτ,hμ,sharpPoincareConstant_pos D,hsmall⟩
    ((A.initial_physical X Y).1.trans hX) ((A.initial_physical X Y).2.trans hY)
    (O.representedDegenerate J hdeg)

/-- (8.4)–(8.8) 在当前时刻的能量控制，包含 T=0 的合法图状态。
与后面的初值界分开：此处右端是 E₇(t)，实际原 Z/Q 由兼容保持识别。 -/
theorem auxiliary_current_GeneralWeakJet (J : OriginalJet O)
    (hdeg : DegenerateJetCompatibility O J)
    (hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hμ : 0 < μ)
    (hsmall : A.c ≤ threshold ε κ τ μ (sharpPoincareConstant D))
    (X : WeightedL2 D.measure A.rawSpatial.wx) (Y : WeightedL2 D.measure A.rawSpatial.swap.wx)
    (hX : physicalL2 D.measure A.rawSpatial.wx A.rawSpatial.wx_measurable A.rawSpatial.wx_gap X = O.φx 0)
    (hY : physicalL2 D.measure A.rawSpatial.swap.wx A.rawSpatial.swap.wx_measurable A.rawSpatial.swap.wx_gap Y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    SharpOriginalAuxiliaryBounds O.representedInterval
      (O.representedInterval.sharpEnergy (O.representedJet J) (A.initialX X) (A.initialY Y) t) t :=
  O.representedInterval.sharp_original_auxiliary_control (O.representedJet J)
    (A.initialX X) (A.initialY Y) ⟨hε,hκ,hτ,hμ,sharpPoincareConstant_pos D,hsmall⟩
    ((A.initial_physical X Y).1.trans hX) ((A.initial_physical X Y).2.trans hY)
    (O.representedDegenerate J hdeg) ht

/-- 显式 jet 分支同样给出输入原 Z/Q 的初值控制，包含 T=0。
这条调用已证原变量重构估计，并没有只控制未识别的重构坐标。 -/
theorem auxiliary_initial_GeneralWeakJet (J : OriginalJet O)
    (hdeg : DegenerateJetCompatibility O J)
    (hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hμ : 0 < μ)
    (hsmall : A.c ≤ threshold ε κ τ μ (sharpPoincareConstant D))
    (X : WeightedL2 D.measure A.rawSpatial.wx) (Y : WeightedL2 D.measure A.rawSpatial.swap.wx)
    (hX : physicalL2 D.measure A.rawSpatial.wx A.rawSpatial.wx_measurable A.rawSpatial.wx_gap X = O.φx 0)
    (hY : physicalL2 D.measure A.rawSpatial.swap.wx A.rawSpatial.swap.wx_measurable A.rawSpatial.swap.wx_gap Y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    SharpOriginalAuxiliaryBounds O.representedInterval
      (O.representedInterval.sharpEnergy (O.representedJet J) (A.initialX X) (A.initialY Y) 0) t :=
  O.representedInterval.sharp_original_auxiliary_initial_control (O.representedJet J)
    (A.initialX X) (A.initialY Y) ⟨hε,hκ,hτ,hμ,sharpPoincareConstant_pos D,hsmall⟩
    ((A.initial_physical X Y).1.trans hX) ((A.initial_physical X Y).2.trans hY)
    (O.representedDegenerate J hdeg) ht

/-- §5.3 对一般弱系数不再独立输入连续性：由代表构造提供。
任意同原状态的合法提升与真实历史给出同一空间能量。 -/
theorem historical_energy_independent_GeneralWeak
    (X : WeightedL2 D.measure A.rawSpatial.wx) (Y : WeightedL2 D.measure A.rawSpatial.swap.wx)
    (hX : physicalL2 D.measure A.rawSpatial.wx A.rawSpatial.wx_measurable A.rawSpatial.wx_gap X = O.φx 0)
    (hY : physicalL2 D.measure A.rawSpatial.swap.wx A.rawSpatial.swap.wx_measurable A.rawSpatial.swap.wx_gap Y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (L : CompatibleLift D A.represented.spatial ε κ τ μ (O.fields t)) :
    fieldEnergy D.measure A.represented.spatial ε κ τ μ
      (O.representedInterval.baseState (A.initialX X) (A.initialY Y) t) =
    fieldEnergy D.measure A.represented.spatial ε κ τ μ L.state := by
  exact O.representedInterval.historical_energy_independent (A.initialX X) (A.initialY Y)
    ((A.initial_physical X Y).1.trans hX) ((A.initial_physical X Y).2.trans hY)
    A.represented.coefficients A.represented.p_match A.represented.r_match
    A.represented.p_continuous A.represented.r_continuous ht L

end OriginalInterval

/-- §5.3 与 (6.4)：一般弱系数下两层能量的提升选择无关。
两份原状态可取同源路径的原层和真实导数层；本结论不以两个任意状态冒充同源。
连续代表完全来自本轮弱导数构造，没有额外连续性或能量相等输入。 -/
theorem twoLayerEnergy_independent_GeneralWeak {D : Rect}
    (A : RawWeakRegionalAbsorption D) {ε κ τ μ K : ℝ} {F₀ F₁ : OriginalState D}
    (L₀ M₀ : CompatibleLift D A.represented.spatial ε κ τ μ F₀)
    (L₁ M₁ : CompatibleLift D A.represented.spatial ε κ τ μ F₁) :
    twoLayerEnergy D.measure A.represented.spatial ε κ τ μ K L₀.state L₁.state =
      twoLayerEnergy D.measure A.represented.spatial ε κ τ μ K M₀.state M₁.state :=
  CompatibleLift.twoLayerEnergy_independent A.represented.coefficients
    A.represented.p_match A.represented.r_match
    A.represented.p_continuous A.represented.r_continuous L₀ M₀ L₁ M₁
end Weak
end LeanPML.PML
