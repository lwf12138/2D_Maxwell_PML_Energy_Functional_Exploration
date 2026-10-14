import LeanPML.PML.WeakOriginalSystem

/-!
# V7 (2.5)–(2.6)：弱原八式的历史提升与 primitive 消元

先从原方程证明五个不变量保持，再只用初始兼容得到本文件的全时段重构。
空间导数来自 H₀¹/H(div) 图；无全轴光滑条件、无吸收正下界。
本文件还把消元后的真实辅助演化交给已有加权历史定理，
使加权成员保持及 (5.8) 的输入来自原八式，而非另行假设辅助 ODE。
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Time
namespace LeanPML.PML.Weak

/-- 有限区间弱原系统的输入。空间识别覆盖端点，PDE 仅在内部。
初始五兼容是单个时刻的条件；historyU/Q、全时段兼容及加权成员均是后续结论。
这里 E 的 H₀¹ 图连续、旋转磁通量的 H(div) 图连续是明确的正则性输入。 -/
structure OriginalInterval (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ε κ τ μ T : ℝ) where
  nonneg_time : 0 ≤ T
  fields : ℝ → OriginalState D
  derivatives : ℝ → OriginalState D
  electric : ℝ → zeroBoundaryGraph D
  flux : ℝ → weakHDivGraph D
  u₀ : zeroBoundaryGraph D
  q₀ : ScalarL2 D.measure
  continuous_fields : OriginalContinuousOn fields (Icc 0 T)
  continuous_electric : ContinuousOn electric (Icc 0 T)
  continuous_flux : ContinuousOn flux (Icc 0 T)
  electric_value : ∀ t ∈ Icc 0 T, (electric t).val.val 0 = (fields t).E
  flux_x : ∀ t ∈ Icc 0 T, (flux t).val 0 = μ • (fields t).Hy
  flux_y : ∀ t ∈ Icc 0 T, (flux t).val 1 = -μ • (fields t).Hx
  equations : ∀ t ∈ Ioo 0 T,
    OriginalAt D C ε κ τ μ fields (derivatives t) t (electric t) (flux t)
  initial_compatible : ∀ i,
    invariants D C ε κ τ μ fields (historyU D electric u₀) (historyQ D fields q₀) 0 i = 0

namespace OriginalInterval
variable {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
variable (O : OriginalInterval D C ε κ τ μ T)

/-- (2.3) 的 H₀¹ 与 L² 历史，初值可非零。 -/
def u := historyU D O.electric O.u₀
def q := historyQ D O.fields O.q₀
def φx := phiX D μ O.u O.fields
def φy := phiY D μ O.u O.fields

/-- 全时段重构只由初始兼容与真实原演化推出，等式在 L² 商类意义成立。
这是弱原系统到 primitive 的消元入口；T=0 直接使用初始兼容。 -/
theorem reconstruction {t : ℝ} (ht : t ∈ Icc 0 T) :
    O.q t + τ • (O.fields t).P = κ • (O.u t).val.val 0 ∧
    (O.fields t).Z1 = -ε • C.bCoeff.operator D.measure ((O.u t).val.val 0) ∧
    (O.fields t).Z2 = -C.bCoeff.operator D.measure (O.q t) ∧
    (O.fields t).Qx = C.pCoeff.operator D.measure (O.φy t) ∧
    (O.fields t).Qy = -C.rCoeff.operator D.measure (O.φx t) := by
  have hz := all_invariants_zero_of_initial D C ε κ τ μ O.fields O.derivatives
    O.electric O.flux O.u₀ O.q₀ O.continuous_electric O.continuous_fields
    O.equations O.initial_compatible ht
  have hD := hz 0
  have hZ1 := hz 1
  have hZ2 := hz 2
  have hX := hz 3
  have hY := hz 4
  change O.q t + τ • (O.fields t).P - κ • (O.u t).val.val 0 = 0 at hD
  change (O.fields t).Z1 + ε • C.bCoeff.operator D.measure ((O.u t).val.val 0) = 0 at hZ1
  change (O.fields t).Z2 + C.bCoeff.operator D.measure (O.q t) = 0 at hZ2
  change (O.fields t).Qx - C.pCoeff.operator D.measure (O.φy t) = 0 at hX
  change (O.fields t).Qy + C.rCoeff.operator D.measure (O.φx t) = 0 at hY
  exact ⟨sub_eq_zero.mp hD, by simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hZ1,
    eq_neg_of_add_eq_zero_left hZ2, sub_eq_zero.mp hX, eq_neg_of_add_eq_zero_left hY⟩

/-- 真实历史空间关系 Λ=∇u+φ。梯度是 H₀¹ 图坐标，不是任意命名函数。 -/
theorem spatial {t : ℝ} (ht : t ∈ Icc 0 T) :
    (O.flux t).val 0 = (O.u t).val.val 1 + O.φx t ∧
    (O.flux t).val 1 = (O.u t).val.val 2 + O.φy t := by
  dsimp [φx, φy, phiX, phiY]
  rw [O.flux_x t ht, O.flux_y t ht]
  constructor <;> abel

/-- (2.6) 主方程：代入已证明的 Z₁、Z₂ 重构消去记忆变量。
E_t 由 OriginalAt.E 的真实 L² 导数绑定；u_t=E 来自 H₀¹ 历史 FTC。
不使用教学子系统 εE'=-P'，也不输入目标能量律。 -/
theorem primitive_main {t : ℝ} (ht : t ∈ Ioo 0 T) :
    μ • (ε • ((O.derivatives t).E + C.aCoeff.operator D.measure ((O.fields t).E) +
      C.bCoeff.operator D.measure ((O.u t).val.val 0)) +
      (O.derivatives t).P + C.aCoeff.operator D.measure ((O.fields t).P) +
      C.bCoeff.operator D.measure (O.q t)) = (O.flux t).val 2 := by
  have hODE := O.equations t ht
  have hrec := O.reconstruction (Ioo_subset_Icc_self ht)
  have hmain := hODE.electric
  rw [hrec.2.1, hrec.2.2.1] at hmain
  simp only [smul_add, smul_sub, neg_smul, sub_neg_eq_add] at hmain ⊢
  rw [hmain]
  abel

/-- (2.6) 的两条辅助演化，由原磁方程与两个磁不变量消元推出。
方向次序为 x: r∂xu−pΛx，y: p∂yu−rΛy；不除以 p、r 或 a。 -/
theorem auxiliary_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt O.φx (C.rCoeff.operator D.measure ((O.u t).val.val 1) -
      C.pCoeff.operator D.measure ((O.flux t).val 0)) t ∧
    HasDerivAt O.φy (C.swap.rCoeff.operator D.measure ((O.u t).val.val 2) -
      C.swap.pCoeff.operator D.measure ((O.flux t).val 1)) t := by
  have hraw := phi_hasDerivAt D C ε κ τ μ O.fields (O.derivatives t) O.electric O.u₀
    (O.flux t) O.continuous_electric ht (O.equations t ht)
  have hrec := O.reconstruction (Ioo_subset_Icc_self ht)
  constructor
  · apply hraw.1.congr_deriv
    rw [hrec.2.2.2.2, O.flux_x t (Ioo_subset_Icc_self ht)]
    dsimp [φx, phiX]
    simp only [map_sub, map_smul, map_neg, smul_sub, neg_smul, neg_neg]
    abel
  · apply hraw.2.congr_deriv
    rw [hrec.2.2.2.1, O.flux_y t (Ioo_subset_Icc_self ht)]
    change μ • (C.rCoeff.operator D.measure (O.fields t).Hx - C.pCoeff.operator D.measure (O.fields t).Hx) -
      C.pCoeff.operator D.measure (O.φy t) =
      C.pCoeff.operator D.measure ((O.u t).val.val 2) - C.rCoeff.operator D.measure (-μ • (O.fields t).Hx)
    dsimp [φy, phiY]
    simp only [map_sub, map_smul, map_neg, smul_sub, neg_smul, neg_neg]
    abel

/-- 历史在 H₀¹ 图范数中连续，并给出实际 φ 的普通 L² 连续性。
这些是加权成员传播的输入，由原场正则性推出而非再次假设。 -/
theorem continuous_history : ContinuousOn O.u (Icc 0 T) ∧
    ContinuousOn O.φx (Icc 0 T) ∧ ContinuousOn O.φy (Icc 0 T) := by
  have hu : ContinuousOn O.u (Icc 0 T) :=
    continuousOn_banachHistory O.electric O.u₀ O.nonneg_time O.continuous_electric
  have hx := (zeroCoordinate D 1).continuous.comp_continuousOn hu
  have hy := (zeroCoordinate D 2).continuous.comp_continuousOn hu
  exact ⟨hu, (O.continuous_fields.Hy.const_smul μ).sub hx,
    (O.continuous_fields.Hx.const_smul (-μ)).sub hy⟩

/-- 原八式 → 实际加权成员及零吸收区保持。
输入只给初始加权元素；全时段成员不在 OriginalInterval 字段中。
由重构、辅助演化和历史连续性调用旧的实际加权 Bochner 构造。 -/
theorem weighted_membership
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hinitial_x : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hinitial_y : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (MemLp (fun x => Real.sqrt (C.wx x) * O.φx t x) 2 D.measure ∧
      (∀ᵐ x ∂D.measure, C.a x = 0 → O.φx t x = 0)) ∧
    (MemLp (fun x => Real.sqrt (C.swap.wx x) * O.φy t x) 2 D.measure ∧
      (∀ᵐ x ∂D.measure, C.a x = 0 → O.φy t x = 0)) := by
  have hu : ContinuousOn (fun s => (O.u s).val) (Icc 0 T) :=
    (zeroBoundaryGraph D).subtypeL.continuous.comp_continuousOn O.continuous_history.1
  constructor
  · exact C.auxiliary_weak_field_membership D W₀x O.φx (fun s => (O.u s).val)
      O.flux T O.continuous_history.2.1 hu O.continuous_flux hinitial_x
      (fun s hs => (O.auxiliary_hasDerivAt hs).1) ht
  · have h := C.swap.auxiliary_weighted_membership D.measure W₀y O.φy
      (fun s => (O.u s).val.val 2) (fun s => (O.flux s).val 1) T O.continuous_history.2.2
      ((zeroCoordinate D 2).continuous.comp_continuousOn O.continuous_history.1)
      ((weakHDivCoordinate D 1).continuous.comp_continuousOn O.continuous_flux)
      hinitial_y (fun s hs => (O.auxiliary_hasDerivAt hs).2) ht
    refine ⟨h.1, h.2.mono ?_⟩
    intro x hx ha
    apply hx
    exact (C.swap.wx_eq_zero_iff x).mpr (by simpa [SpatialAbsorption.a, SpatialAbsorption.swap, absorptionSum, add_comm] using ha)

/-- V7 (5.8) 接入真实原八变量：h、Λ 和辅助演化不再是独立输入。
准确常数 2、4cSt 保持；输出是已构造加权历史的范数，物理值由成员定理识别。
本结论仅是传播估计，不替代后续两层能量律或 C² 正则性。 -/
theorem memory_bound
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hinitial_x : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hinitial_y : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖C.auxiliaryWeightedHistory D.measure W₀x (fun s => (O.u s).val.val 1)
      (fun s => (O.flux s).val 0) t‖ ^ 2 +
    ‖C.swap.auxiliaryWeightedHistory D.measure W₀y (fun s => (O.u s).val.val 2)
      (fun s => (O.flux s).val 1) t‖ ^ 2 ≤
    2 * (‖W₀x‖ ^ 2 + ‖W₀y‖ ^ 2) + 4 * C.c * C.S * t *
      ∫ s in 0..t, (‖(O.u s).val.val 1‖ ^ 2 + ‖(O.u s).val.val 2‖ ^ 2) := by
  have hu : ContinuousOn (fun s => (O.u s).val) (Icc 0 T) :=
    (zeroBoundaryGraph D).subtypeL.continuous.comp_continuousOn O.continuous_history.1
  exact C.auxiliary_weak_memory_bound D W₀x W₀y O.φx O.φy (fun s => (O.u s).val)
    O.flux T O.continuous_history.2.1 O.continuous_history.2.2 hu O.continuous_flux
    hinitial_x hinitial_y (fun s hs => (O.auxiliary_hasDerivAt hs).1)
    (fun s hs => (O.auxiliary_hasDerivAt hs).2)
    (fun s hs => (O.spatial (Ioo_subset_Icc_self hs)).1)
    (fun s hs => (O.spatial (Ioo_subset_Icc_self hs)).2) ht

end OriginalInterval
end LeanPML.PML.Weak
