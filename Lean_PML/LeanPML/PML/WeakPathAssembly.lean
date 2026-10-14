import LeanPML.PML.WeakPrimitiveSystem
import LeanPML.PML.MainAbstract

/-!
# 弱原场历史到两层真实路径

由 V7 (6.3)、(6.6) 推出，原文未单列这些桥接。梯度和散度的时间交换
来自图空间路径的真实导数，经连续坐标投影得到；不假设交换公式。
加权原层由已证明历史构造，第一、第二层用同一强迫算子作用于真实导数。
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Time
namespace LeanPML.PML.Weak

/-- 相等权重之间的实际连续线性识别，只更换类型索引，不改变 L² 商类。 -/
def weightedCongr {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {w₁ w₂ : α → ℝ} (h : w₁ = w₂) : WeightedL2 ν w₁ →L[ℝ] WeightedL2 ν w₂ := by
  subst w₂
  exact ContinuousLinearMap.id ℝ _

/-- 权重识别不改变物理恢复，避免把交换方向当成独立加权坐标。 -/
theorem physical_weightedCongr {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {w₁ w₂ : α → ℝ} (h : w₁ = w₂) (hm₁ : Measurable w₁) (hm₂ : Measurable w₂)
    (hg₁ : ∀ x, w₁ x = 0 ∨ 1 ≤ w₁ x) (hg₂ : ∀ x, w₂ x = 0 ∨ 1 ≤ w₂ x)
    (W : WeightedL2 ν w₁) :
    physicalL2 ν w₂ hm₂ hg₂ (weightedCongr ν h W) = physicalL2 ν w₁ hm₁ hg₁ W := by
  subst w₂
  rfl

/-- H₀¹ 图转入已证明弱 Green 的受限定义域，没有读取边界点值。 -/
def zeroDomain (D : Rect) (u : zeroBoundaryGraph D) : (weakGreenDomain D).spatial.domain :=
  ⟨u.val.val 0, ⟨u, rfl⟩⟩

/-- 通量图转入弱散度定义域；不额外限制法向迹。 -/
def fluxDomain (D : Rect) (L : weakHDivGraph D) : (weakGreenDomain D).fluxDomain :=
  ⟨(L.val 0, L.val 1), ⟨L, rfl⟩⟩

/-- 上述 L² 像恢复出的图就是原图，理由是实际弱偏导唯一。 -/
theorem zeroDomain_lift (D : Rect) (u : zeroBoundaryGraph D) :
    weakZeroLift D (zeroDomain D u) = u := by
  apply Subtype.ext
  apply weakValue_injective D
  exact weakZeroLift_value D (zeroDomain D u)

/-- 弱梯度接口的两个坐标与原 H₀¹ 图一致。 -/
theorem zeroDomain_gradient (D : Rect) (u : zeroBoundaryGraph D) :
    (weakGreenDomain D).spatial.componentX (zeroDomain D u) = u.val.val 1 ∧
    (weakGreenDomain D).spatial.componentY (zeroDomain D u) = u.val.val 2 := by
  change (weakZeroLift D (zeroDomain D u)).val.val 1 = _ ∧
    (weakZeroLift D (zeroDomain D u)).val.val 2 = _
  rw [zeroDomain_lift]
  exact ⟨rfl, rfl⟩

/-- 散度接口恢复出的坐标就是给定真实弱散度。 -/
theorem fluxDomain_divergence (D : Rect) (L : weakHDivGraph D) :
    (weakGreenDomain D).divergence (fluxDomain D L) = L.val 2 := by
  exact HasWeakDivergence.unique (weakDivergence_spec D (fluxDomain D L)) L.property

/-- 为同源导数层采用的实际正则性。图导数提供 E_t 的零迹和 λ_t 的散度。
E_tt、P_tt、λ_tt 是真实 L² 导数数据；不输入导数层 PDE 或能量结论。
这里 λ 的第二时间导数以分量 L² 表示，不机械要求 H¹ 磁场。
闭区间连续性供端点静态约束及时间积分平衡使用。 -/
structure OriginalJet {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (O : OriginalInterval D C ε κ τ μ T) where
  electricDot : ℝ → zeroBoundaryGraph D
  fluxDot : ℝ → weakHDivGraph D
  electricDDot : ℝ → ScalarL2 D.measure
  polarDDot : ℝ → ScalarL2 D.measure
  fluxDDotX : ℝ → ScalarL2 D.measure
  fluxDDotY : ℝ → ScalarL2 D.measure
  electric_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt O.electric (electricDot t) t
  flux_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt O.flux (fluxDot t) t
  electricDot_value : ∀ t ∈ Icc 0 T, (electricDot t).val.val 0 = (O.derivatives t).E
  electric_second : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => (O.derivatives s).E) (electricDDot t) t
  polar_second : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => (O.derivatives s).P) (polarDDot t) t
  flux_second_x : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => (fluxDot s).val 0) (fluxDDotX t) t
  flux_second_y : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => (fluxDot s).val 1) (fluxDDotY t) t
  continuous_electricDot : ContinuousOn electricDot (Icc 0 T)
  continuous_fluxDot : ContinuousOn fluxDot (Icc 0 T)
  continuous_polarDot : ContinuousOn (fun t => (O.derivatives t).P) (Icc 0 T)
  continuous_polarDDot : ContinuousOn polarDDot (Icc 0 T)

namespace OriginalInterval
variable {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
variable (O : OriginalInterval D C ε κ τ μ T)

/-- 加权原层来自实际历史；y 方向先交换系数，再用已证明权重等式转回 wy。 -/
def weightedX (W₀ : WeightedL2 D.measure C.wx) (t : ℝ) :=
  C.auxiliaryWeightedHistory D.measure W₀ (fun s => (O.u s).val.val 1)
    (fun s => (O.flux s).val 0) t

def weightedY (W₀ : WeightedL2 D.measure C.swap.wx) (t : ℝ) :=
  weightedCongr D.measure C.swap_wx_eq_wy
    (C.swap.auxiliaryWeightedHistory D.measure W₀ (fun s => (O.u s).val.val 2)
      (fun s => (O.flux s).val 1) t)

/-- 两层状态的原层：每一坐标来自同一个原场及真实历史。 -/
def baseState (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (t : ℝ) : FieldState D.measure C.wx C.wy where
  v := (O.u t).val.val 0
  V := (O.fields t).E
  R := (O.fields t).P
  z := O.q t
  ψx := O.weightedX W₀x t
  ψy := O.weightedY W₀y t
  Λx := (O.flux t).val 0
  Λy := (O.flux t).val 1

/-- 第一层加权槽是已构造右端，其物理恢复恰为 r∂xu−pλx 等。
该值是否真是导数在下方逐项证明，未凭命名认定。 -/
def firstState (J : OriginalJet O) (t : ℝ) : FieldState D.measure C.wx C.wy where
  v := (O.fields t).E
  V := (O.derivatives t).E
  R := (O.derivatives t).P
  z := (O.fields t).P
  ψx := C.auxiliaryRateX D.measure ((O.u t).val.val 1) ((O.flux t).val 0)
  ψy := weightedCongr D.measure C.swap_wx_eq_wy
    (C.swap.auxiliaryRateX D.measure ((O.u t).val.val 2) ((O.flux t).val 1))
  Λx := (J.fluxDot t).val 0
  Λy := (J.fluxDot t).val 1

/-- 第二层是第一层的实际导数数据；P_tt 对应 J.polarDDot。 -/
def secondState (J : OriginalJet O) (t : ℝ) : FieldState D.measure C.wx C.wy where
  v := (O.derivatives t).E
  V := J.electricDDot t
  R := J.polarDDot t
  z := (O.derivatives t).P
  ψx := C.auxiliaryRateX D.measure ((O.electric t).val.val 1) ((J.fluxDot t).val 0)
  ψy := weightedCongr D.measure C.swap_wx_eq_wy
    (C.swap.auxiliaryRateX D.measure ((O.electric t).val.val 2) ((J.fluxDot t).val 1))
  Λx := J.fluxDDotX t
  Λy := J.fluxDDotY t

/-- 原层全部八个坐标的真实空间值求导，逐项使用 FTC、原场导数和图坐标投影。
加权槽在实际加权范数中求导，不从普通 L² 导数冒充加权导数。 -/
theorem baseState_hasDerivAt (J : OriginalJet O)
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    StateHasDerivAt (O.baseState W₀x W₀y) (O.firstState J t) t := by
  have hu := historyU_hasDerivAt D O.electric O.u₀ O.continuous_electric ht
  have hux := (zeroCoordinate D 1).continuous.comp_continuousOn O.continuous_history.1
  have huy := (zeroCoordinate D 2).continuous.comp_continuousOn O.continuous_history.1
  have hLx := (weakHDivCoordinate D 0).continuous.comp_continuousOn O.continuous_flux
  have hLy := (weakHDivCoordinate D 1).continuous.comp_continuousOn O.continuous_flux
  refine ⟨?_, (O.equations t ht).E, (O.equations t ht).P, ?_, ?_, ?_, ?_, ?_⟩
  · exact (zeroCoordinate_hasDerivAt D 0 hu).congr_deriv (O.electric_value t (Ioo_subset_Icc_self ht))
  · exact hasDerivAt_banachHistory (fun s => (O.fields s).P) O.q₀ O.continuous_fields.P ht
  · exact C.hasDerivAt_auxiliaryWeightedHistory D.measure W₀x _ _ T t hux hLx ht
  · exact (weightedCongr D.measure C.swap_wx_eq_wy).hasFDerivAt.comp_hasDerivAt t
      (C.swap.hasDerivAt_auxiliaryWeightedHistory D.measure W₀y _ _ T t huy hLy ht)
  · exact hasDerivAt_weakHDiv_coordinate D 0 (J.flux_deriv t ht)
  · exact hasDerivAt_weakHDiv_coordinate D 1 (J.flux_deriv t ht)

/-- 第一层的实际导数由同一个原系统的二阶时间正则性推出。
辅助槽用同一有界强迫算子作用于 ∇E、λ_t；没有独立导数层演化输入。 -/
theorem firstState_hasDerivAt (J : OriginalJet O) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    StateHasDerivAt (O.firstState J) (O.secondState J t) t := by
  have hu := historyU_hasDerivAt D O.electric O.u₀ O.continuous_electric ht
  have hdx := zeroCoordinate_hasDerivAt D 1 hu
  have hdy := zeroCoordinate_hasDerivAt D 2 hu
  have hLx := hasDerivAt_weakHDiv_coordinate D 0 (J.flux_deriv t ht)
  have hLy := hasDerivAt_weakHDiv_coordinate D 1 (J.flux_deriv t ht)
  refine ⟨(O.equations t ht).E, J.electric_second t ht, J.polar_second t ht,
    (O.equations t ht).P, ?_, ?_, J.flux_second_x t ht, J.flux_second_y t ht⟩
  · exact (C.hasDerivAt_auxiliaryRateX D.measure _ _ _ _ t hdx hLx).1
  · exact (weightedCongr D.measure C.swap_wx_eq_wy).hasFDerivAt.comp_hasDerivAt t
      (C.swap.hasDerivAt_auxiliaryRateX D.measure _ _ _ _ t hdy hLy).1

/-- (6.3) 的同源对象由历史构造及两次真实求导填入；不是两个独立状态。
原层 q_t=P、u_t=E 与八坐标求导使用同一证明。 -/
def sameSource (J : OriginalJet O)
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx) :
    SameSourcePath D.measure C.wx C.wy (Ioo 0 T) where
  base := O.baseState W₀x W₀y
  first := O.firstState J
  second := O.secondState J
  deriv_base t ht := O.baseState_hasDerivAt J W₀x W₀y ht
  deriv_first t ht := O.firstState_hasDerivAt J ht
  velocity t ht := (O.baseState_hasDerivAt J W₀x W₀y ht).v
  primitivePolar t ht := (O.baseState_hasDerivAt J W₀x W₀y ht).z



/-- 两层所需梯度/散度交换及四个零迹由实际图路径填入。
原层 u、E 与导数层 E、E_t 都属于 H₀¹；零迹来自同一闭包，非额外边界假设。 -/
def spatialPath (J : OriginalJet O)
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx) :
    ConditionalSpatialPath (weakGreenDomain D) C (O.sameSource J W₀x W₀y) where
  base_v t := zeroDomain D (O.u t)
  base_V t := zeroDomain D (O.electric t)
  first_v t := zeroDomain D (O.electric t)
  first_V t := zeroDomain D (J.electricDot t)
  base_flux t := fluxDomain D (O.flux t)
  first_flux t := fluxDomain D (J.fluxDot t)
  base_v_eq _ _ := rfl
  base_V_eq t ht := O.electric_value t (Ioo_subset_Icc_self ht)
  first_v_eq t ht := O.electric_value t (Ioo_subset_Icc_self ht)
  first_V_eq t ht := J.electricDot_value t (Ioo_subset_Icc_self ht)
  base_flux_eq _ _ := rfl
  first_flux_eq _ _ := rfl
  grad_baseX t ht := by
    simp_rw [(zeroDomain_gradient D _).1]
    exact zeroCoordinate_hasDerivAt D 1
      (historyU_hasDerivAt D O.electric O.u₀ O.continuous_electric (interior_subset ht))
  grad_baseY t ht := by
    simp_rw [(zeroDomain_gradient D _).2]
    exact zeroCoordinate_hasDerivAt D 2
      (historyU_hasDerivAt D O.electric O.u₀ O.continuous_electric (interior_subset ht))
  grad_firstX t ht := by
    simp_rw [(zeroDomain_gradient D _).1]
    exact zeroCoordinate_hasDerivAt D 1 (J.electric_deriv t (interior_subset ht))
  grad_firstY t ht := by
    simp_rw [(zeroDomain_gradient D _).2]
    exact zeroCoordinate_hasDerivAt D 2 (J.electric_deriv t (interior_subset ht))
  div_base t ht := by
    simp_rw [fluxDomain_divergence]
    exact hasDerivAt_weakHDiv_coordinate D 2 (J.flux_deriv t (interior_subset ht))
  trace_base_v _ _ := rfl
  trace_base_V _ _ := rfl
  trace_first_v _ _ := rfl
  trace_first_V _ _ := rfl

/-- 已构造加权历史的物理恢复等于由原磁场/提升定义的 φ。
零区和代表元处理由旧 physical_auxiliaryWeightedHistory 完成。 -/
theorem base_physical
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    physicalX D.measure C (O.baseState W₀x W₀y t).ψx = O.φx t ∧
    physicalY D.measure C (O.baseState W₀x W₀y t).ψy = O.φy t := by
  have hux := (zeroCoordinate D 1).continuous.comp_continuousOn O.continuous_history.1
  have huy := (zeroCoordinate D 2).continuous.comp_continuousOn O.continuous_history.1
  have hLx := (weakHDivCoordinate D 0).continuous.comp_continuousOn O.continuous_flux
  have hLy := (weakHDivCoordinate D 1).continuous.comp_continuousOn O.continuous_flux
  constructor
  · exact C.physical_auxiliaryWeightedHistory D.measure W₀x O.φx _ _ T
      O.continuous_history.2.1 hux hLx hWx (fun s hs => (O.auxiliary_hasDerivAt hs).1) ht
  · change physicalL2 _ _ _ _ (weightedCongr _ _ _) = _
    rw [physical_weightedCongr]
    exact C.swap.physical_auxiliaryWeightedHistory D.measure W₀y O.φy _ _ T
      O.continuous_history.2.2 huy hLy hWy (fun s hs => (O.auxiliary_hasDerivAt hs).2) ht

/-- (2.6) 在旧分析接口中的实际入口：主式来自原电式和兼容消元，
极化/空间关系来自历史保持，辅助式来自已经识别的加权强迫。
所有六个字段在证明体内建立；调用者不提供 primitive 演化。 -/
theorem base_evolution (J : OriginalJet O)
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    PrimitiveAtConditional (weakGreenDomain D) C ε κ τ μ
      (O.baseState W₀x W₀y t) (O.firstState J t)
      (zeroDomain D (O.u t)) (fluxDomain D (O.flux t)) := by
  have hphysical := O.base_physical W₀x W₀y hWx hWy (Ioo_subset_Icc_self ht)
  refine ⟨?_, (O.reconstruction (Ioo_subset_Icc_self ht)).1, ?_, ?_, ?_, ?_⟩
  · rw [fluxDomain_divergence]
    exact O.primitive_main ht
  · rw [(zeroDomain_gradient D _).1, hphysical.1]
    exact (O.spatial (Ioo_subset_Icc_self ht)).1
  · rw [(zeroDomain_gradient D _).2, hphysical.2]
    exact (O.spatial (Ioo_subset_Icc_self ht)).2
  · rw [(zeroDomain_gradient D _).1]
    exact C.physical_auxiliaryRateX D.measure _ _
  · rw [(zeroDomain_gradient D _).2]
    change physicalL2 _ _ _ _ (weightedCongr _ _ _) = _
    rw [physical_weightedCongr]
    exact C.swap.physical_auxiliaryRateX D.measure _ _

/-- 两层普通/加权坐标在闭区间连续。加权原层由积分连续性、第一层由有界
强迫算子连续性推出；没有要求无界 w 是普通 L² 乘子。 -/
theorem states_continuous (J : OriginalJet O)
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx) :
    StateContinuousOn (O.baseState W₀x W₀y) (Icc 0 T) ∧
    StateContinuousOn (O.firstState J) (Icc 0 T) := by
  have hcoord (i : Fin 3) := (zeroCoordinate D i).continuous.comp_continuousOn O.continuous_history.1
  have hflux (i : Fin 3) := (weakHDivCoordinate D i).continuous.comp_continuousOn O.continuous_flux
  have hfluxdot (i : Fin 3) := (weakHDivCoordinate D i).continuous.comp_continuousOn J.continuous_fluxDot
  have hEderiv : ContinuousOn (fun t => (O.derivatives t).E) (Icc 0 T) :=
    ((zeroCoordinate D 0).continuous.comp_continuousOn J.continuous_electricDot).congr
      (fun t ht => (J.electricDot_value t ht).symm)
  constructor
  · refine ⟨hcoord 0, O.continuous_fields.E, O.continuous_fields.P, ?_, ?_, ?_, hflux 0, hflux 1⟩
    · exact continuousOn_banachHistory _ O.q₀ O.nonneg_time O.continuous_fields.P
    · exact C.continuousOn_auxiliaryWeightedHistory D.measure W₀x _ _ T O.nonneg_time (hcoord 1) (hflux 0)
    · exact (weightedCongr D.measure C.swap_wx_eq_wy).continuous.comp_continuousOn
        (C.swap.continuousOn_auxiliaryWeightedHistory D.measure W₀y _ _ T O.nonneg_time (hcoord 2) (hflux 1))
  · refine ⟨O.continuous_fields.E, hEderiv, J.continuous_polarDot, O.continuous_fields.P,
      ?_, ?_, hfluxdot 0, hfluxdot 1⟩
    · exact C.continuousOn_auxiliaryRateX D.measure _ _ _ (hcoord 1) (hflux 0)
    · exact (weightedCongr D.measure C.swap_wx_eq_wy).continuous.comp_continuousOn
        (C.swap.continuousOn_auxiliaryRateX D.measure _ _ _ (hcoord 2) (hflux 1))

end OriginalInterval
end LeanPML.PML.Weak
