import LeanPML.PML.AuxiliaryWeightedEvolution
import LeanPML.Analysis.DissipativeMemoryEstimate

/-!
# V7 (5.8)：实际加权场的精确有限时间估计

初始加权成员 + 普通 L² 原演化 → 构造并识别加权历史 → 阻尼形式 → (5.8)。
这里接通已证空间算子与真实 Hilbert 时间估计，不重新假设全时段加权成员。
最后把 h 接到真实弱 H¹ 图的梯度，并按两个方向求和。
本估计不是最终能量单调性，也不自动给完整原八变量解的存在或 C² 正则性。
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.SpatialAbsorption
variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/-- V7 (5.8) 的单方向版本，范数取已识别的实际加权历史。
h、l 是普通 L² 路径，φ 满足真实辅助演化；l=h+φ 是空间兼容。
由已证非负阻尼和强迫界 2cS 得到精确 2 与 4cSt，未预设目标估计。 -/
theorem auxiliary_weighted_memory_bound (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (φ h l : ℝ → ScalarL2 ν) (T : ℝ)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (hinitial : physicalL2 ν C.wx C.wx_measurable C.wx_gap W₀ = φ 0)
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt φ (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (l s)) s)
    (hspace : ∀ s ∈ Ioo 0 T, l s = h s + φ s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖C.auxiliaryWeightedHistory ν W₀ h l t‖ ^ 2 ≤
      2 * ‖W₀‖ ^ 2 + 4 * C.c * C.S * t * ∫ s in 0..t, ‖h s‖ ^ 2 := by
  let B := weightedMul ν C.wx C.pCoeff.value C.pCoeff.measurable
    C.pCoeff.bound C.pCoeff.abs_le
  let W := C.auxiliaryWeightedHistory ν W₀ h l
  let F : ℝ → WeightedL2 ν C.wx := fun s => C.differenceLift ν (h s)
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hW : ContinuousOn W (Icc 0 T) :=
    C.continuousOn_auxiliaryWeightedHistory ν W₀ h l T hT hh hl
  have hF : ContinuousOn F (Icc 0 T) :=
    (C.differenceLift ν).continuous.comp_continuousOn hh
  have hweightedODE : ∀ s ∈ Ioo 0 T, HasDerivAt W (-B (W s) + F s) s := by
    intro s hs
    exact C.hasDerivAt_auxiliaryWeightedHistory_damped ν W₀ φ h l T s
      hφ hh hl hinitial hODE (hspace s hs) hs
  have hmemory := dissipative_memory_square_bound B (C.weighted_absorption_inner_nonneg ν)
    W F hW hF hweightedODE ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hFint : IntervalIntegrable (fun s => ‖F s‖ ^ 2) volume 0 t :=
    ((hF.norm.pow 2).mono hsub).intervalIntegrable_of_Icc ht.1
  have hhint : IntervalIntegrable (fun s => ‖h s‖ ^ 2) volume 0 t :=
    ((hh.norm.pow 2).mono hsub).intervalIntegrable_of_Icc ht.1
  have hint_bound : (∫ s in 0..t, ‖F s‖ ^ 2) ≤
      (2 * C.c * C.S) * ∫ s in 0..t, ‖h s‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ht.1 hFint (hhint.const_mul _)
    intro s hs
    exact C.differenceLift_norm_sq ν (h s)
  have hscaled := mul_le_mul_of_nonneg_left hint_bound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht.1)
  have hWzero : W 0 = W₀ := C.auxiliaryWeightedHistory_initial ν W₀ h l
  rw [hWzero] at hmemory
  change ‖W t‖ ^ 2 ≤ _
  nlinarith

/-- (5.8) 的实际空间积分版本，直接涉及输入的普通 L² 辅助场 φ(t)。
先用物理恢复识别构造的加权历史，再调用旧空间的范数—积分定理；
同时交付密度可积性，避免借不可积积分的总定义得到形式上的数值。 -/
theorem auxiliary_weighted_integral_bound (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (φ h l : ℝ → ScalarL2 ν) (T : ℝ)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (hinitial : physicalL2 ν C.wx C.wx_measurable C.wx_gap W₀ = φ 0)
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt φ (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (l s)) s)
    (hspace : ∀ s ∈ Ioo 0 T, l s = h s + φ s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (fun x => C.wx x * (φ t x) ^ 2) ν ∧
    (∫ x, C.wx x * (φ t x) ^ 2 ∂ν) ≤
      2 * ‖W₀‖ ^ 2 + 4 * C.c * C.S * t * ∫ s in 0..t, ‖h s‖ ^ 2 := by
  let W := C.auxiliaryWeightedHistory ν W₀ h l t
  have hphysical : physicalL2 ν C.wx C.wx_measurable C.wx_gap W = φ t :=
    C.physical_auxiliaryWeightedHistory ν W₀ φ h l T hφ hh hl hinitial hODE ht
  have hintegrable := integrable_weighted_square ν C.wx C.wx_measurable C.wx_gap W
  have hnorm := weighted_norm_sq_eq_integral ν C.wx C.wx_measurable C.wx_gap W
  rw [hphysical] at hintegrable hnorm
  have hbound := C.auxiliary_weighted_memory_bound ν W₀ φ h l T
    hφ hh hl hinitial hODE hspace ht
  exact ⟨hintegrable, hnorm.symm.trans_le hbound⟩

/-- V7 (5.8) 的二维实际弱场版本。
u 的两个空间导数是 weakH1Graph 的真实弱偏导；L 是 H(div) 图通量。
y 方向显式交换 p、r；其加权空间 C.swap.wx=C.wy 已由 swap_wx_eq_wy 证明。
两个初始加权元素是输入，整个时间段的成员与连续/可导表示由前面构造推出。 -/
theorem auxiliary_weak_memory_bound (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (φx φy : ℝ → ScalarL2 D.measure)
    (u : ℝ → weakH1Graph D) (L : ℝ → weakHDivGraph D) (T : ℝ)
    (hφx : ContinuousOn φx (Icc 0 T)) (hφy : ContinuousOn φy (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T)) (hL : ContinuousOn L (Icc 0 T))
    (hinitial_x : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = φx 0)
    (hinitial_y : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = φy 0)
    (hODE_x : ∀ s ∈ Ioo 0 T, HasDerivAt φx
      (C.rCoeff.operator D.measure ((u s).val 1) - C.pCoeff.operator D.measure ((L s).val 0)) s)
    (hODE_y : ∀ s ∈ Ioo 0 T, HasDerivAt φy
      (C.swap.rCoeff.operator D.measure ((u s).val 2) - C.swap.pCoeff.operator D.measure ((L s).val 1)) s)
    (hspace_x : ∀ s ∈ Ioo 0 T, (L s).val 0 = (u s).val 1 + φx s)
    (hspace_y : ∀ s ∈ Ioo 0 T, (L s).val 1 = (u s).val 2 + φy s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖C.auxiliaryWeightedHistory D.measure W₀x (fun s => (u s).val 1)
      (fun s => (L s).val 0) t‖ ^ 2 +
    ‖C.swap.auxiliaryWeightedHistory D.measure W₀y (fun s => (u s).val 2)
      (fun s => (L s).val 1) t‖ ^ 2 ≤
    2 * (‖W₀x‖ ^ 2 + ‖W₀y‖ ^ 2) + 4 * C.c * C.S * t *
      ∫ s in 0..t, (‖(u s).val 1‖ ^ 2 + ‖(u s).val 2‖ ^ 2) := by
  have hgx : ContinuousOn (fun s => (u s).val 1) (Icc 0 T) := (weakH1Coordinate D 1).continuous.comp_continuousOn hu
  have hgy : ContinuousOn (fun s => (u s).val 2) (Icc 0 T) := (weakH1Coordinate D 2).continuous.comp_continuousOn hu
  have hLx : ContinuousOn (fun s => (L s).val 0) (Icc 0 T) := (weakHDivCoordinate D 0).continuous.comp_continuousOn hL
  have hLy : ContinuousOn (fun s => (L s).val 1) (Icc 0 T) := (weakHDivCoordinate D 1).continuous.comp_continuousOn hL
  have hx := C.auxiliary_weighted_memory_bound D.measure W₀x φx
    (fun s => (u s).val 1) (fun s => (L s).val 0) T hφx hgx hLx hinitial_x hODE_x hspace_x ht
  have hy := C.swap.auxiliary_weighted_memory_bound D.measure W₀y φy
    (fun s => (u s).val 2) (fun s => (L s).val 1) T hφy hgy hLy hinitial_y hODE_y hspace_y ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hix := ((hgx.norm.pow 2).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
  have hiy := ((hgy.norm.pow 2).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
  rw [intervalIntegral.integral_add hix hiy]
  change _ ≤ 2 * ‖W₀y‖ ^ 2 + 4 * C.c * C.S * t * _ at hy
  linarith

end LeanPML.PML.SpatialAbsorption
