import LeanPML.PML.WeakV7Regularity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# (6.6) 的 Cᵏ 充分性桥接：正长度闭区间

使用 mathlib 的 ContDiffOn 与区间导数 derivWithin，构造已有 V7TimeRegularity。
连续的真实内部导数可唯一延到两个端点；不输入端点 PDE。
T=0 不能使用此稠密性论证，仍由旧 DegenerateJetCompatibility 单独处理。
本文件不改原解的演化、空间或加权条件。
-/
noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.Weak

/-- 连续内部导数与 C¹ 区间导数在闭区间一致。
(6.6) 的端点识别辅助结论，原文未单列；T>0 保证内部稠密。 -/
theorem derivWithin_eq_on_closed_interval {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f g : ℝ → H} {T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ 1 f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt f (g t) t) :
    EqOn (derivWithin f (Icc 0 T)) g (Icc 0 T) := by
  have hunique : UniqueDiffOn ℝ (Icc 0 T) := uniqueDiffOn_Icc hT
  have hcontinuous := hf.continuousOn_derivWithin hunique le_rfl
  have hinterior : EqOn (derivWithin f (Icc 0 T)) g (Ioo 0 T) := by
    intro t ht
    exact (hderiv t ht).hasDerivWithinAt.derivWithin (hunique t (Ioo_subset_Icc_self ht))
  apply hinterior.of_subset_closure hcontinuous hg Ioo_subset_Icc_self
  rw [closure_Ioo hT.ne]

/-- (6.6) 中 Cⁿ⁺¹ 函数的已识别导数具有 Cⁿ 正则性。
该桥接使用实际 HasDerivAt 和闭区间稠密性，不对单点等式求导。 -/
theorem contDiffOn_derivative_of_evidence {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f g : ℝ → H} {T : ℝ} {n : ℕ∞ω} (hT : 0 < T)
    (hf : ContDiffOn ℝ (n+1) f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt f (g t) t) :
    ContDiffOn ℝ n g (Icc 0 T) := by
  have hfirst : ContDiffOn ℝ 1 f (Icc 0 T) := hf.of_le (by exact le_add_self)
  have heq := derivWithin_eq_on_closed_interval hT hfirst hg hderiv
  exact (hf.derivWithin (uniqueDiffOn_Icc hT) le_rfl).congr (fun t ht => (heq ht).symm)

/-- C¹ 闭区间路径在内部具有真实普通导数，其值是区间导数。
端点只使用 ContDiffOn 的相对正则性，不额外声明普通双侧导数。 -/
theorem hasDerivAt_within_of_contDiffOn {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : ℝ → H} {T t : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T)) (ht : t ∈ Ioo 0 T) :
    HasDerivAt f (derivWithin f (Icc 0 T) t) t :=
  ((hf.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- (6.6) 中主定理实际需要的 Cᵏ 空间路径条件。
u 是真实 H₀¹ 历史；L² 的 u 另有 C³，P 有 C²，λ 有 C¹(H(div))。
原结构的 derivatives 在端点不受内部 PDE 约束，故另将其 E/P 两槽识别为
区间导数；这属于导数数据的端点识别，不是端点 PDE 或目标能量条件。
本构造只用于 T>0；未声称任意单点 jet 由 Cᵏ 自动确定。 -/
structure ClosedCkRegularity {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (O : OriginalInterval D C ε κ τ μ T) : Prop where
  u_graph : ContDiffOn ℝ 2 O.u (Icc 0 T)
  u_value : ContDiffOn ℝ 3 (fun t => (O.u t).val.val 0) (Icc 0 T)
  polar : ContDiffOn ℝ 2 (fun t => (O.fields t).P) (Icc 0 T)
  flux : ContDiffOn ℝ 1 O.flux (Icc 0 T)
  electric_endpoint : ∀ t, t = 0 ∨ t = T →
    derivWithin (fun s => (O.fields s).E) (Icc 0 T) t = (O.derivatives t).E
  polar_endpoint : ∀ t, t = 0 ∨ t = T →
    derivWithin (fun s => (O.fields s).P) (Icc 0 T) t = (O.derivatives t).P

namespace ClosedCkRegularity
variable {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
variable {O : OriginalInterval D C ε κ τ μ T} (R : ClosedCkRegularity O) (hT : 0 < T)
include R hT

/-- 历史 u 的 C²(H₀¹) 与真实 u_t=E 推出 E 的 C¹(H₀¹)。
三坐标同时受图范数控制，因此后续梯度求导是有证据的线性投影。 -/
theorem electric_graph : ContDiffOn ℝ 1 O.electric (Icc 0 T) := by
  apply contDiffOn_derivative_of_evidence hT R.u_graph O.continuous_electric
  intro t ht
  exact historyU_hasDerivAt D O.electric O.u₀ O.continuous_electric ht

/-- u 的 L² C³ 通过真实历史导数推出输入原电场的 L² C²。 -/
theorem electric_value : ContDiffOn ℝ 2 (fun t => (O.fields t).E) (Icc 0 T) := by
  apply contDiffOn_derivative_of_evidence hT R.u_value O.continuous_fields.E
  intro t ht
  have hhistory := zeroCoordinate_hasDerivAt D 0
    (historyU_hasDerivAt D O.electric O.u₀ O.continuous_electric ht)
  rw [O.electric_value t (Ioo_subset_Icc_self ht)] at hhistory
  exact hhistory

/-- 内部原八式绑定 E_t/P_t；端点仅用上述数据识别。
因而区间导数与原导数槽在整个闭区间一致。 -/
theorem derivative_slots :
    EqOn (derivWithin (fun t => (O.fields t).E) (Icc 0 T))
      (fun t => (O.derivatives t).E) (Icc 0 T) ∧
    EqOn (derivWithin (fun t => (O.fields t).P) (Icc 0 T))
      (fun t => (O.derivatives t).P) (Icc 0 T) := by
  have hunique := uniqueDiffOn_Icc hT
  constructor
  · intro t ht
    by_cases hendpoint : t = 0 ∨ t = T
    · exact R.electric_endpoint t hendpoint
    · have hinterior : t ∈ Ioo 0 T := ⟨lt_of_le_of_ne ht.1 (Ne.symm (not_or.mp hendpoint).1),
        lt_of_le_of_ne ht.2 (not_or.mp hendpoint).2⟩
      exact (O.equations t hinterior).toOriginalHasDerivAt.E.hasDerivWithinAt.derivWithin (hunique t ht)
  · intro t ht
    by_cases hendpoint : t = 0 ∨ t = T
    · exact R.polar_endpoint t hendpoint
    · have hinterior : t ∈ Ioo 0 T := ⟨lt_of_le_of_ne ht.1 (Ne.symm (not_or.mp hendpoint).1),
        lt_of_le_of_ne ht.2 (not_or.mp hendpoint).2⟩
      exact (O.equations t hinterior).toOriginalHasDerivAt.P.hasDerivWithinAt.derivWithin (hunique t ht)

/-- 原导数槽的 C¹ 不是新输入：由 C² 原场与刚证明的闭区间识别得到。 -/
theorem derivatives_c1 :
    ContDiffOn ℝ 1 (fun t => (O.derivatives t).E) (Icc 0 T) ∧
    ContDiffOn ℝ 1 (fun t => (O.derivatives t).P) (Icc 0 T) := by
  have hslots := R.derivative_slots hT
  exact ⟨((R.electric_value hT).derivWithin (uniqueDiffOn_Icc hT) (by norm_num)).congr
      (fun t ht => (hslots.1 ht).symm),
    (R.polar.derivWithin (uniqueDiffOn_Icc hT) (by norm_num)).congr
      (fun t ht => (hslots.2 ht).symm)⟩

/-- 从真正 Cᵏ 假设构造旧正则性证据；未输入 OriginalJet、λ_tt 或能量目标。
λ_tt 仍由 V7TimeRegularity 的已证原演化推导取得。 -/
def toTimeRegularity : V7TimeRegularity O where
  electricDot := derivWithin O.electric (Icc 0 T)
  fluxDot := derivWithin O.flux (Icc 0 T)
  electricDDot := derivWithin (fun t => (O.derivatives t).E) (Icc 0 T)
  polarDDot := derivWithin (fun t => (O.derivatives t).P) (Icc 0 T)
  electric_deriv t ht := hasDerivAt_within_of_contDiffOn (R.electric_graph hT) ht
  flux_deriv t ht := hasDerivAt_within_of_contDiffOn R.flux ht
  electricDot_value := by
    have hgraphContinuous := (R.electric_graph hT).continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl
    apply eqOn_Icc_of_Ioo hT.le
      ((zeroCoordinate D 0).continuous.comp_continuousOn hgraphContinuous)
      (R.derivatives_c1 hT).1.continuousOn
    · intro t ht
      have hgraph := zeroCoordinate_hasDerivAt D 0
        (hasDerivAt_within_of_contDiffOn (R.electric_graph hT) ht)
      have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 T := isOpen_Ioo.mem_nhds ht
      have hsame : HasDerivAt (fun s => (O.fields s).E)
          ((derivWithin O.electric (Icc 0 T) t).val.val 0) t :=
        hgraph.congr_of_eventuallyEq (hnear.mono fun s hs =>
          (O.electric_value s (Ioo_subset_Icc_self hs)).symm)
      exact hsame.unique (O.equations t ht).toOriginalHasDerivAt.E
    · intro hzero
      exact (hT.ne' hzero).elim
  electric_second t ht := hasDerivAt_within_of_contDiffOn (R.derivatives_c1 hT).1 ht
  polar_second t ht := hasDerivAt_within_of_contDiffOn (R.derivatives_c1 hT).2 ht
  continuous_electricDot := (R.electric_graph hT).continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl
  continuous_fluxDot := R.flux.continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl
  continuous_polarDot := (R.derivatives_c1 hT).2.continuousOn
  continuous_polarDDot := (R.derivatives_c1 hT).2.continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl

/-- 正长度区间的新调用入口：Cᵏ → 真实 jet → 原系统能量及输入原辅助变量界。
当前空间常数仍为 2Lx，连续代表仍由旧系数入口给出，未宣称原 π 常数已接通。 -/
theorem main_energy_from_closedCk
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hp : CoercivityParameters C ε κ τ μ (poincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0) :
    OriginalInterval.EnergyConclusions O (R.toTimeRegularity hT).toOriginalJet W₀x W₀y ∧
      ∀ t ∈ Icc 0 T, OriginalInterval.OriginalAuxiliaryBounds O
        (O.energy (R.toTimeRegularity hT).toOriginalJet W₀x W₀y 0) t := by
  apply (R.toTimeRegularity hT).main_energy_and_auxiliary W₀x W₀y hp hWx hWy
  exact ⟨fun hz => (hT.ne' hz).elim, fun hz => (hT.ne' hz).elim,
    fun hz => (hT.ne' hz).elim⟩
end ClosedCkRegularity
end LeanPML.PML.Weak
