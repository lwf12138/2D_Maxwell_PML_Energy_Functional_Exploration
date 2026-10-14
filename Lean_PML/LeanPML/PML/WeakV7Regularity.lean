import LeanPML.PML.WeakPhysicalControl

/-!
# V7 (6.6) 的时间正则性连接：消去独立 λ_tt 输入

u 由原电场的 H₀¹ 历史构造。u 的 C²(H₀¹)/C³(L²)、P 的 C²(L²)、
λ 的 C¹(H(div)) 所需导数和闭区间连续性逐项列明，未把 OriginalJet 包装成字段。
从已证兼容保持、空间关系和原辅助方程推出 λ_tt；φ 的加权求导沿用真实历史。
有限区间采用内部 HasDerivAt，端点不要求 PDE；T=0 的初始图兼容仍需单列。
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.Weak

/-- (6.6) 的可调用导数证据表示。E_t 是 H₀¹ 图导数，E_tt、P_tt 是真实 L² 导数，
λ_t 是 H(div) 图导数。与旧 OriginalJet 相比，不输入 λ_tt 或其导数公式。
这些时间正则性是输入，不宣称由空间成员自动传播。 -/
structure V7TimeRegularity {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (O : OriginalInterval D C ε κ τ μ T) where
  electricDot : ℝ → zeroBoundaryGraph D
  fluxDot : ℝ → weakHDivGraph D
  electricDDot : ℝ → ScalarL2 D.measure
  polarDDot : ℝ → ScalarL2 D.measure
  electric_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt O.electric (electricDot t) t
  flux_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt O.flux (fluxDot t) t
  electricDot_value : ∀ t ∈ Icc 0 T, (electricDot t).val.val 0 = (O.derivatives t).E
  electric_second : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => (O.derivatives s).E) (electricDDot t) t
  polar_second : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => (O.derivatives s).P) (polarDDot t) t
  continuous_electricDot : ContinuousOn electricDot (Icc 0 T)
  continuous_fluxDot : ContinuousOn fluxDot (Icc 0 T)
  continuous_polarDot : ContinuousOn (fun t => (O.derivatives t).P) (Icc 0 T)
  continuous_polarDDot : ContinuousOn polarDDot (Icc 0 T)

namespace V7TimeRegularity
variable {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
variable {O : OriginalInterval D C ε κ τ μ T} (R : V7TimeRegularity O)

/-- 由 λ=∇u+φ 与真实辅助演化推出 λ_t 两分量。
空间等式在邻域成立后才求导；不对单点恒等式求导。 -/
theorem fluxDot_eq {t : ℝ} (ht : t ∈ Ioo 0 T) :
    (R.fluxDot t).val 0 = (O.electric t).val.val 1 +
      (C.rCoeff.operator D.measure ((O.u t).val.val 1) - C.pCoeff.operator D.measure ((O.flux t).val 0)) ∧
    (R.fluxDot t).val 1 = (O.electric t).val.val 2 +
      (C.swap.rCoeff.operator D.measure ((O.u t).val.val 2) - C.swap.pCoeff.operator D.measure ((O.flux t).val 1)) := by
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 T := isOpen_Ioo.mem_nhds ht
  have hu := historyU_hasDerivAt D O.electric O.u₀ O.continuous_electric ht
  have hphi := O.auxiliary_hasDerivAt ht
  constructor
  · have hright := (zeroCoordinate_hasDerivAt D 1 hu).add hphi.1
    have hleft := hasDerivAt_weakHDiv_coordinate D 0 (R.flux_deriv t ht)
    exact hleft.unique (hright.congr_of_eventuallyEq
      (hnear.mono fun s hs => (O.spatial (Ioo_subset_Icc_self hs)).1))
  · have hright := (zeroCoordinate_hasDerivAt D 2 hu).add hphi.2
    have hleft := hasDerivAt_weakHDiv_coordinate D 1 (R.flux_deriv t ht)
    exact hleft.unique (hright.congr_of_eventuallyEq
      (hnear.mono fun s hs => (O.spatial (Ioo_subset_Icc_self hs)).2))

/-- λ_tt 的实际值由原式确定，x方向 r∂xE−pλx,t，y方向交换 p/r。 -/
def fluxDDotX (t : ℝ) : ScalarL2 D.measure :=
  (R.electricDot t).val.val 1 +
    (C.rCoeff.operator D.measure ((O.electric t).val.val 1) -
      C.pCoeff.operator D.measure ((R.fluxDot t).val 0))

def fluxDDotY (t : ℝ) : ScalarL2 D.measure :=
  (R.electricDot t).val.val 2 +
    (C.swap.rCoeff.operator D.measure ((O.electric t).val.val 2) -
      C.swap.pCoeff.operator D.measure ((R.fluxDot t).val 1))

/-- (6.6) 与原辅助演化实际给出旧入口需要的 λ_tt 证据。
梯度投影、固定有界乘子分别用连续线性求导规则；最后使用邻域等式。
不对无界能量权重作空间或时间乘子求导。 -/
theorem flux_second {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => (R.fluxDot s).val 0) (R.fluxDDotX t) t ∧
    HasDerivAt (fun s => (R.fluxDot s).val 1) (R.fluxDDotY t) t := by
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 T := isOpen_Ioo.mem_nhds ht
  have hu := historyU_hasDerivAt D O.electric O.u₀ O.continuous_electric ht
  constructor
  · have hgrad := zeroCoordinate_hasDerivAt D 1 (R.electric_deriv t ht)
    have hforcing := (Analysis.hasDerivAt_operator (C.rCoeff.operator D.measure)
      (zeroCoordinate_hasDerivAt D 1 hu)).sub
      (Analysis.hasDerivAt_operator (C.pCoeff.operator D.measure)
        (hasDerivAt_weakHDiv_coordinate D 0 (R.flux_deriv t ht)))
    exact (hgrad.add hforcing).congr_of_eventuallyEq (hnear.mono fun s hs => (R.fluxDot_eq hs).1)
  · have hgrad := zeroCoordinate_hasDerivAt D 2 (R.electric_deriv t ht)
    have hforcing := (Analysis.hasDerivAt_operator (C.swap.rCoeff.operator D.measure)
      (zeroCoordinate_hasDerivAt D 2 hu)).sub
      (Analysis.hasDerivAt_operator (C.swap.pCoeff.operator D.measure)
        (hasDerivAt_weakHDiv_coordinate D 1 (R.flux_deriv t ht)))
    exact (hgrad.add hforcing).congr_of_eventuallyEq (hnear.mono fun s hs => (R.fluxDot_eq hs).2)

/-- 构造旧实际 jet。λ_tt 两字段由上条证明填入，调用者不再提供。
其余字段正是 (6.6) 所用的真实图/L² 时间正则性。 -/
def toOriginalJet : OriginalJet O where
  electricDot := R.electricDot
  fluxDot := R.fluxDot
  electricDDot := R.electricDDot
  polarDDot := R.polarDDot
  fluxDDotX := R.fluxDDotX
  fluxDDotY := R.fluxDDotY
  electric_deriv := R.electric_deriv
  flux_deriv := R.flux_deriv
  electricDot_value := R.electricDot_value
  electric_second := R.electric_second
  polar_second := R.polar_second
  flux_second_x t ht := (R.flux_second ht).1
  flux_second_y t ht := (R.flux_second ht).2
  continuous_electricDot := R.continuous_electricDot
  continuous_fluxDot := R.continuous_fluxDot
  continuous_polarDot := R.continuous_polarDot
  continuous_polarDDot := R.continuous_polarDDot

/-- 新最终调用入口：从较少的真实时间正则性出发，内部补齐 λ_tt，
再调用已经验证的弱原系统能量与原辅助变量控制。 -/
theorem main_energy_and_auxiliary
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hp : CoercivityParameters C ε κ τ μ (poincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O R.toOriginalJet) :
    OriginalInterval.EnergyConclusions O R.toOriginalJet W₀x W₀y ∧
      ∀ t ∈ Icc 0 T, OriginalInterval.OriginalAuxiliaryBounds O
        (O.energy R.toOriginalJet W₀x W₀y 0) t := by
  refine ⟨O.main_energy_estimate_WeakOriginal R.toOriginalJet W₀x W₀y hp hWx hWy hdeg, ?_⟩
  intro t ht
  exact O.original_auxiliary_initial_control R.toOriginalJet W₀x W₀y hp hWx hWy hdeg ht
end V7TimeRegularity
end LeanPML.PML.Weak
