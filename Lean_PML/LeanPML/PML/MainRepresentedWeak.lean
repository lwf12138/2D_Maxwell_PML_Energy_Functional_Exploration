import LeanPML.PML.WeakAbsorptionRepresentative
import LeanPML.PML.WeakCanonicalTime

/-!
# 一般分离区域弱系数的原系统能量入口

V7 §1、(5.1)、(6.6)–(6.10)、(8.4)–(8.8)。代表构造从区域弱导数证明，
调用者不输入连续性。原方程用构造出的代表表达，但实际 L² 乘子与原系数相同；
下列积分对应把输出再写回原系数。正长度区间沿用真实闭区间 Cᵏ 入口。
零长度入口保留初始 jet 兼容，不从空内部方程获得导数层约束。
-/
noncomputable section
open MeasureTheory Set Filter
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

/-- a.e. 相等的权重给出完全相同的平方根坐标闭子空间。
零区条件也按原测度 a.e. 识别；不是让加权测度忽略零区。 -/
theorem weightedSubspace_eq_of_ae {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (w v : α → ℝ) (heq : w =ᵐ[ν] v) : weightedSubspace ν w = weightedSubspace ν v := by
  ext X
  constructor
  · intro hX
    filter_upwards [hX,heq] with x hx hweight
    exact fun hv => hx (hweight.trans hv)
  · intro hX
    filter_upwards [hX,heq] with x hx hweight
    exact fun hw => hx (hweight.symm.trans hw)

namespace RawWeakRegionalAbsorption
variable {D : Rect}

/-- 权重替换保留加权空间本身；不要求 w 有界，正区和零区同时处理。 -/
theorem weighted_spaces_eq (A : RawWeakRegionalAbsorption D) :
    weightedSubspace D.measure A.represented.spatial.wx =
      weightedSubspace D.measure (fun z => energyWeightX A.c
        (A.coefficients.p.value.value z) (A.coefficients.r.value.value z)) ∧
    weightedSubspace D.measure A.represented.spatial.wy =
      weightedSubspace D.measure (fun z => energyWeightY A.c
        (A.coefficients.p.value.value z) (A.coefficients.r.value.value z)) := by
  constructor
  · apply weightedSubspace_eq_of_ae
    filter_upwards [A.spatial_ae.1,A.spatial_ae.2] with z hp hr
    change energyWeightX A.c _ _ = _
    rw [hp,hr]
  · apply weightedSubspace_eq_of_ae
    filter_upwards [A.spatial_ae.1,A.spatial_ae.2] with z hp hr
    change energyWeightY A.c _ _ = _
    rw [hp,hr]

/-- (6.2) 的实际能量积分使用输入原弱系数，证明可积性后再改写积分。
μ、ε、κ 和零区分支直接复用既有密度，未建立第二套能量。 -/
theorem energy_integral_original (A : RawWeakRegionalAbsorption D) (ε κ τ μ : ℝ)
    (U : FieldState D.measure A.represented.spatial.wx A.represented.spatial.wy) :
    let f := fun z => Obstructions.singleLayerEnergy ε κ τ μ A.c
      (A.coefficients.p.value.value z) (A.coefficients.r.value.value z)
      (U.v z) (U.V z) (U.R z) (U.z z)
      (U.Λx z - physicalX D.measure A.represented.spatial U.ψx z)
      (U.Λy z - physicalY D.measure A.represented.spatial U.ψy z) (U.Λx z) (U.Λy z)
    Integrable f D.measure ∧ fieldEnergy D.measure A.represented.spatial ε κ τ μ U = ∫ z, f z ∂D.measure := by
  dsimp only
  let F := fun z p r => Obstructions.singleLayerEnergy ε κ τ μ A.c p r
    (U.v z) (U.V z) (U.R z) (U.z z)
    (U.Λx z - physicalX D.measure A.represented.spatial U.ψx z)
      (U.Λy z - physicalY D.measure A.represented.spatial U.ψy z) (U.Λx z) (U.Λy z)
  have hrepr := A.integral_and_integrable F
  have hknown := fieldEnergy_eq_integral D.measure A.represented.spatial ε κ τ μ U
  have hint := fieldEnergyDensity_integrable D.measure A.represented.spatial ε κ τ μ U
  exact ⟨hrepr.2.mp hint,hknown.trans hrepr.1⟩

end RawWeakRegionalAbsorption

namespace Weak

/-- 原弱系数 → 已证连续代表 → 精确矩形常数主定理。
输入结构只含原弱导数/幅度和原解的真实时间正则性，没有连续代表假设。
所有能量与原 Z/Q 初值控制由现有主证明推出；不是原方程输入字段。 -/
theorem main_energy_RawRegionalSharpCk
    (D : Rect) (A : RawWeakRegionalAbsorption D) (ε κ τ μ T : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hμ : 0 < μ) (hT : 0 < T)
    (hsmall : A.c ≤ threshold ε κ τ μ (sharpPoincareConstant D))
    (O : OriginalInterval D A.represented.spatial ε κ τ μ T) (R : V7ClosedCkCore O)
    (W₀x : WeightedL2 D.measure A.represented.spatial.wx)
    (W₀y : WeightedL2 D.measure A.represented.spatial.swap.wx)
    (hWx : physicalL2 D.measure A.represented.spatial.wx A.represented.spatial.wx_measurable
      A.represented.spatial.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure A.represented.spatial.swap.wx A.represented.spatial.swap.wx_measurable
      A.represented.spatial.swap.wx_gap W₀y = O.φy 0) :
    OriginalInterval.SharpEnergyConclusions (V7ClosedCkCore.canonicalInterval (O := O) hT)
      ((R.regularity hT).toTimeRegularity hT).toOriginalJet W₀x W₀y ∧
    ∀ t ∈ Icc 0 T, OriginalInterval.SharpOriginalAuxiliaryBounds
      (V7ClosedCkCore.canonicalInterval (O := O) hT)
      ((V7ClosedCkCore.canonicalInterval (O := O) hT).sharpEnergy
        ((R.regularity hT).toTimeRegularity hT).toOriginalJet W₀x W₀y 0) t := by
  exact main_energy_RegionalSharpCk D A.represented ε κ τ μ T hε hκ hτ hμ hT
    hsmall O R W₀x W₀y hWx hWy

end Weak
end LeanPML.PML
