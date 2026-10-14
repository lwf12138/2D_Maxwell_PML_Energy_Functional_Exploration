import LeanPML.PML.WeakPathAssembly

/-!
# 弱原系统到有限区间能量问题的具体总装

对应 V7 (6.6)–(6.9)。弱 Green、Poincaré 和时间—空间交换均由已证结果填入。
正长度区间的导数层静态约束由内部演化及闭区间连续性延伸；T=0 单独要求
初始导数数据相容，不从空内部方程推出该事实。此文件不假设目标能量律。
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.Weak

/-- 闭区间连续函数的内部相等可延至端点；退化单点须另给该点相等。
这是拓扑辅助结论，不输入端点 PDE 或端点双侧导数。 -/
theorem eqOn_Icc_of_Ioo {H : Type*} [TopologicalSpace H] [T2Space H]
    {f g : ℝ → H} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hinterior : EqOn f g (Ioo 0 T)) (hzero : T = 0 → f 0 = g 0) :
    EqOn f g (Icc 0 T) := by
  rcases hT.eq_or_lt with hzeroT | hpos
  · have hTzero : T = 0 := hzeroT.symm
    subst T
    intro t ht
    have htzero : t = 0 := le_antisymm ht.2 ht.1
    subst t
    exact hzero rfl
  · apply hinterior.of_subset_closure hf hg Ioo_subset_Icc_self
    rw [closure_Ioo hpos.ne]

/-- 只在 T=0 使用的初始导数层相容：是实际数据关系，不是能量或全时段结论。
正长度区间这些关系由原式与连续性推出，故不额外限制其初值。 -/
structure DegenerateJetCompatibility {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)}
    {ε κ τ μ T : ℝ} (O : OriginalInterval D C ε κ τ μ T) (J : OriginalJet O) : Prop where
  polar : T = 0 → (O.fields 0).P + τ • (O.derivatives 0).P = κ • (O.fields 0).E
  spatialX : T = 0 → (J.fluxDot 0).val 0 = (O.electric 0).val.val 1 +
    C.rCoeff.operator D.measure ((O.u 0).val.val 1) - C.pCoeff.operator D.measure ((O.flux 0).val 0)
  spatialY : T = 0 → (J.fluxDot 0).val 1 = (O.electric 0).val.val 2 +
    C.pCoeff.operator D.measure ((O.u 0).val.val 2) - C.rCoeff.operator D.measure ((O.flux 0).val 1)

/-- 真实 H₀¹ 图及极化/空间等式给出旧框架的静态约束。
Poincaré 本身由弱闭包证明提供，零迹来自 H₀¹ 而非新的 estimate 输入。 -/
theorem stateConstraints_of_graph (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (κ τ : ℝ)
    (U : FieldState D.measure C.wx C.wy) (v : zeroBoundaryGraph D)
    (hvalue : v.val.val 0 = U.v) (hpolar : PolarConstraint κ τ U)
    (hx : U.Λx = v.val.val 1 + physicalX D.measure C U.ψx)
    (hy : U.Λy = v.val.val 2 + physicalY D.measure C U.ψy) :
    StateCoercivityConstraints D.measure C (weakGreenDomain D).spatial
      (weakPoincareDomain D) κ τ U := by
  have hmem : U.v ∈ (weakGreenDomain D).spatial.domain := by
    rw [← hvalue]
    exact (zeroDomain D v).property
  have heq : (⟨U.v, hmem⟩ : (weakGreenDomain D).spatial.domain) = zeroDomain D v :=
    Subtype.ext hvalue.symm
  refine ⟨⟨hmem, ?_, ?_⟩, ?_, hpolar⟩
  · rw [heq, (zeroDomain_gradient D v).1]
    exact hx
  · rw [heq, (zeroDomain_gradient D v).2]
    exact hy
  · rfl

namespace OriginalInterval
variable {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
variable (O : OriginalInterval D C ε κ τ μ T) (J : OriginalJet O)
variable (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
variable (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
variable (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
include W₀x W₀y hWx hWy

/-- 第一导数层满足同一 primitive 演化，调用已证的真实邻域求导链。
基方程来自原八式，不把第一导数层 PDE 放入输入。 -/
theorem first_evolution {t : ℝ} (ht : t ∈ Ioo 0 T) :
    PrimitiveAtConditional (weakGreenDomain D) C ε κ τ μ
      (O.firstState J t) (O.secondState J t)
      (zeroDomain D (O.electric t)) (fluxDomain D (J.fluxDot t)) := by
  exact primitive_first_Conditional ε κ τ μ (O.sameSource J W₀x W₀y)
    (O.spatialPath J W₀x W₀y)
    (fun s hs => O.base_evolution J W₀x W₀y hWx hWy hs)
    (by simpa only [isOpen_Ioo.interior_eq] using ht)

/-- 原层的闭区间静态约束来自初始兼容保持及加权历史识别。 -/
theorem base_constraints {t : ℝ} (ht : t ∈ Icc 0 T) :
    StateCoercivityConstraints D.measure C (weakGreenDomain D).spatial
      (weakPoincareDomain D) κ τ (O.baseState W₀x W₀y t) := by
  have hp := O.base_physical W₀x W₀y hWx hWy ht
  apply stateConstraints_of_graph D C κ τ (O.baseState W₀x W₀y t) (O.u t) rfl (O.reconstruction ht).1
  · rw [hp.1]
    exact (O.spatial ht).1
  · rw [hp.2]
    exact (O.spatial ht).2

/-- 导数层静态约束延伸到两个端点。连续的是实际图/L²/加权坐标，
内部约束由已求导的 primitive 系统得到；T=0 仅用明确初始数据相容。 -/
theorem first_constraints (hdeg : DegenerateJetCompatibility O J)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    StateCoercivityConstraints D.measure C (weakGreenDomain D).spatial
      (weakPoincareDomain D) κ τ (O.firstState J t) := by
  have hcont := (O.states_continuous J W₀x W₀y).2
  have hpolar : PolarConstraint κ τ (O.firstState J t) := by
    apply eqOn_Icc_of_Ioo O.nonneg_time (hcont.z.add (hcont.R.const_smul τ))
      (hcont.v.const_smul κ) _ hdeg.polar ht
    intro s hs
    exact (O.first_evolution J W₀x W₀y hWx hWy hs).polar
  have hgradx : ContinuousOn (fun s => (O.electric s).val.val 1) (Icc 0 T) :=
    (zeroCoordinate D 1).continuous.comp_continuousOn O.continuous_electric
  have hgrady : ContinuousOn (fun s => (O.electric s).val.val 2) (Icc 0 T) :=
    (zeroCoordinate D 2).continuous.comp_continuousOn O.continuous_electric
  have hx : (O.firstState J t).Λx = (O.electric t).val.val 1 +
      physicalX D.measure C (O.firstState J t).ψx := by
    apply eqOn_Icc_of_Ioo O.nonneg_time hcont.Λx
      (hgradx.add ((physicalX D.measure C).continuous.comp_continuousOn hcont.ψx)) _ _ ht
    · intro s hs
      simpa only [(zeroDomain_gradient D _).1, Pi.add_apply, Function.comp_apply] using
        (O.first_evolution J W₀x W₀y hWx hWy hs).spatialX
    · intro hT
      change (J.fluxDot 0).val 0 = _ + physicalX _ _ (C.auxiliaryRateX _ _ _)
      rw [physicalX, C.physical_auxiliaryRateX]
      simpa only [add_sub_assoc] using hdeg.spatialX hT
  have hy : (O.firstState J t).Λy = (O.electric t).val.val 2 +
      physicalY D.measure C (O.firstState J t).ψy := by
    apply eqOn_Icc_of_Ioo O.nonneg_time hcont.Λy
      (hgrady.add ((physicalY D.measure C).continuous.comp_continuousOn hcont.ψy)) _ _ ht
    · intro s hs
      simpa only [(zeroDomain_gradient D _).2, Pi.add_apply, Function.comp_apply] using
        (O.first_evolution J W₀x W₀y hWx hWy hs).spatialY
    · intro hT
      change (J.fluxDot 0).val 1 = _ + physicalL2 _ _ _ _ (weightedCongr _ _ _)
      rw [physical_weightedCongr D.measure C.swap_wx_eq_wy C.swap.wx_measurable C.wy_measurable C.swap.wx_gap C.wy_gap, C.swap.physical_auxiliaryRateX]
      change (J.fluxDot 0).val 1 = (O.electric 0).val.val 2 +
        (C.pCoeff.operator D.measure ((O.u 0).val.val 2) - C.rCoeff.operator D.measure ((O.flux 0).val 1))
      exact (hdeg.spatialY hT).trans (add_sub_assoc _ _ _)
  exact stateConstraints_of_graph D C κ τ _ (O.electric t) (O.electric_value t ht) hpolar hx hy

/-- 真实弱原系统的有限区间问题构造。Green、Poincaré、交换、原层演化、
同源两层及闭区间静态约束全部在证明体内填入，不由调用者传入已完成问题。
仍保留显式时间正则性 OriginalJet 与仅 T=0 的初始导数相容。 -/
def finiteProblem (hdeg : DegenerateJetCompatibility O J) :
    FiniteIntervalProblemConditional (weakGreenDomain D) C ε κ τ μ (poincareConstant D) T
      (fun v _ => weak_poincare_domain D v) where
  T_nonneg := O.nonneg_time
  path := O.sameSource J W₀x W₀y
  regular := O.spatialPath J W₀x W₀y
  base_evolution t ht := O.base_evolution J W₀x W₀y hWx hWy ht
  continuous_base := (O.states_continuous J W₀x W₀y).1
  continuous_first := (O.states_continuous J W₀x W₀y).2
  static_base t ht := O.base_constraints W₀x W₀y hWx hWy ht
  static_first t ht := O.first_constraints J W₀x W₀y hWx hWy hdeg ht

end OriginalInterval
end LeanPML.PML.Weak
