import LeanPML.PML.MainWeakRectangle
import LeanPML.PML.WeakLiftCompatibility
import LeanPML.PML.WeakRegionalAbsorption

/-!
# 区域系数推荐入口与实际历史提升的规范独立性

V7 §5.3、(6.7)–(6.10)。原始吸收 profile 的幅度只在计算域坐标区间要求；
内部零延拓与原系数在整个 Ω 的 L²/积分意义一致。
历史提升属于合法提升是结论，由五不变量保持填入，不预设全时段兼容。
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.Weak
namespace OriginalInterval
variable {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
variable (O : OriginalInterval D C ε κ τ μ T)
variable (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
variable (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
variable (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)

/-- (2.3) 的实际历史在任意闭区间时刻是同一原八状态的合法提升。
所有兼容字段从 reconstruction 推出；辅助加权坐标由历史构造识别。 -/
def historicalLift {t : ℝ} (ht : t ∈ Icc 0 T) :
    CompatibleLift D C ε κ τ μ (O.fields t) where
  u := O.u t
  q := O.q t
  ψx := (O.baseState W₀x W₀y t).ψx
  ψy := (O.baseState W₀x W₀y t).ψy
  polar := (O.reconstruction ht).1
  flux_x := by
    rw [(O.base_physical W₀x W₀y hWx hWy ht).1]
    dsimp [φx, phiX]
    abel
  flux_y := by
    rw [(O.base_physical W₀x W₀y hWx hWy ht).2]
    dsimp [φy, phiY]
    abel
  memory1 := (O.reconstruction ht).2.1
  memory2 := (O.reconstruction ht).2.2.1
  auxiliaryX := by
    rw [(O.base_physical W₀x W₀y hWx hWy ht).2]
    exact (O.reconstruction ht).2.2.2.1
  auxiliaryY := by
    rw [(O.base_physical W₀x W₀y hWx hWy ht).1]
    exact (O.reconstruction ht).2.2.2.2

/-- 合法历史提升的状态就是最终能量使用的原层，包含实际磁通量缩放。 -/
theorem historicalLift_state {t : ℝ} (ht : t ∈ Icc 0 T) :
    (O.historicalLift W₀x W₀y hWx hWy ht).state = O.baseState W₀x W₀y t := by
  dsimp [historicalLift, CompatibleLift.state, baseState]
  rw [O.flux_x t ht, O.flux_y t ht]

include hWx hWy in
/-- §5.3 接入实际历史和实际单层能量：任何同一原状态的合法提升给出同一值。
结论在弱图/L² 商类意义成立，不主张任意逐点代表相等。 -/
theorem historical_energy_independent
    (m : SeparatedRegionalWeakCoefficients D)
    (hp_match : ∀ x ∈ D.openSet, m.p.value.value x = C.p x)
    (hr_match : ∀ x ∈ D.openSet, m.r.value.value x = C.r x)
    (hp_continuous : ContinuousOn m.p.value.value D.openSet)
    (hr_continuous : ContinuousOn m.r.value.value D.openSet)
    {t : ℝ} (ht : t ∈ Icc 0 T) (L : CompatibleLift D C ε κ τ μ (O.fields t)) :
    fieldEnergy D.measure C ε κ τ μ (O.baseState W₀x W₀y t) =
      fieldEnergy D.measure C ε κ τ μ L.state := by
  rw [← O.historicalLift_state W₀x W₀y hWx hWy ht]
  exact CompatibleLift.energy_independent m hp_match hr_match hp_continuous hr_continuous _ L

end OriginalInterval

/-- 推荐区域弱原系统入口。输入材料正性、区域 profile 条件及保守阈值；
具体有限区间问题在 main_energy_estimate_WeakOriginal 内部构造。
本条使用已证弱 Green/Poincaré，不要求调用者提供分析接口或能量目标。 -/
theorem main_energy_estimate_RegionalWeak
    (D : Rect) (A : WeakRegionalAbsorption D) (ε κ τ μ T : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hμ : 0 < μ)
    (hsmall : A.c ≤ threshold ε κ τ μ (poincareConstant D))
    (O : OriginalInterval D A.spatial ε κ τ μ T) (J : OriginalJet O)
    (W₀x : WeightedL2 D.measure A.spatial.wx)
    (W₀y : WeightedL2 D.measure A.spatial.swap.wx)
    (hWx : physicalL2 D.measure A.spatial.wx A.spatial.wx_measurable A.spatial.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure A.spatial.swap.wx A.spatial.swap.wx_measurable A.spatial.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O J) :
    OriginalInterval.EnergyConclusions O J W₀x W₀y := by
  have hp : CoercivityParameters A.spatial ε κ τ μ (poincareConstant D) :=
    ⟨hε, hκ, hτ, hμ, poincareConstant_pos D, hsmall⟩
  exact O.main_energy_estimate_WeakOriginal J W₀x W₀y hp hWx hWy hdeg

namespace RegionalIntegrals
variable (D : Rect) (A : WeakRegionalAbsorption D) (ε κ τ μ : ℝ)

/-- (6.2) 用输入原剖面 p(x)、r(y) 写出的实际密度；内部延拓只用于构造商类算子。 -/
def energyDensity (U : FieldState D.measure A.spatial.wx A.spatial.wy) (x : ℝ × ℝ) : ℝ :=
  Obstructions.singleLayerEnergy ε κ τ μ A.c
    (A.coefficients.profileX x.1) (A.coefficients.profileY x.2)
    (U.v x) (U.V x) (U.R x) (U.z x)
    (U.Λx x - physicalX D.measure A.spatial U.ψx x)
    (U.Λy x - physicalY D.measure A.spatial U.ψy x) (U.Λx x) (U.Λy x)

/-- (7.7) 同样换回原区域剖面，保留空间耗散的独立零吸收分支。 -/
def dissipationDensity (U : FieldState D.measure A.spatial.wx A.spatial.wy)
    (Rdot : ScalarL2 D.measure) (x : ℝ × ℝ) : ℝ :=
  Obstructions.singleLayerDissipation ε κ τ μ A.c
    (A.coefficients.profileX x.1) (A.coefficients.profileY x.2)
    (U.v x) (U.V x) (U.R x) (U.z x) (Rdot x)
    (spatialComponentX U x) (spatialComponentY U x) (U.Λx x) (U.Λy x)

/-- 由 (6.2) 推出：原剖面密度可积，且积分正是主定理的实际内积能量。
先调用旧可积性，再用域内 a.e. 一致换代表；不利用不可积积分的总定义。 -/
theorem energy_integrable_and_eq
    (U : FieldState D.measure A.spatial.wx A.spatial.wy) :
    Integrable (energyDensity D A ε κ τ μ U) D.measure ∧
      fieldEnergy D.measure A.spatial ε κ τ μ U =
        ∫ x, energyDensity D A ε κ τ μ U x ∂D.measure := by
  let F := fun x p r => Obstructions.singleLayerEnergy ε κ τ μ A.c p r
    (U.v x) (U.V x) (U.R x) (U.z x)
    (U.Λx x - physicalX D.measure A.spatial U.ψx x)
    (U.Λy x - physicalY D.measure A.spatial U.ψy x) (U.Λx x) (U.Λy x)
  have hintegrable := fieldEnergyDensity_integrable D.measure A.spatial ε κ τ μ U
  constructor
  · exact (A.integrable_profiles_iff F).mp hintegrable
  · calc
      fieldEnergy D.measure A.spatial ε κ τ μ U =
          ∫ x, fieldEnergyDensity D.measure A.spatial ε κ τ μ U x ∂D.measure :=
        fieldEnergy_eq_integral D.measure A.spatial ε κ τ μ U
      _ = _ := A.integral_profiles F

/-- 由 (7.7) 推出：耗散密度的同一可积性与积分连接，不附加耗散符号假设。 -/
theorem dissipation_integrable_and_eq
    (U : FieldState D.measure A.spatial.wx A.spatial.wy) (Rdot : ScalarL2 D.measure) :
    Integrable (dissipationDensity D A ε κ τ μ U Rdot) D.measure ∧
      fieldDissipation D.measure A.spatial ε κ τ μ U Rdot =
        ∫ x, dissipationDensity D A ε κ τ μ U Rdot x ∂D.measure := by
  let F := fun x p r => Obstructions.singleLayerDissipation ε κ τ μ A.c p r
    (U.v x) (U.V x) (U.R x) (U.z x) (Rdot x)
    (spatialComponentX U x) (spatialComponentY U x) (U.Λx x) (U.Λy x)
  have hintegrable := fieldDissipationDensity_integrable D.measure A.spatial ε κ τ μ U Rdot
  constructor
  · exact (A.integrable_profiles_iff F).mp hintegrable
  · calc
      fieldDissipation D.measure A.spatial ε κ τ μ U Rdot =
          ∫ x, fieldDissipationDensity D.measure A.spatial ε κ τ μ U Rdot x ∂D.measure :=
        fieldDissipation_eq_integral D.measure A.spatial ε κ τ μ U Rdot
      _ = _ := A.integral_profiles F
end RegionalIntegrals

end LeanPML.PML.Weak
