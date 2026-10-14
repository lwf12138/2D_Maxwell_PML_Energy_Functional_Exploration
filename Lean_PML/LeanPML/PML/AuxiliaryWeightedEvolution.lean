import LeanPML.PML.WeightedForcing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# 辅助演化的加权成员与真实路径构造

由 V7 §5.2 (5.7)–(5.8) 所讨论的辅助演化推出，原文未单列本构造。
采用等价右端 φᵢ,t=σⱼ h−σᵢ l，其中 h=∂ᵢu、l=Λᵢ。
先把普通 L² 的右端提升到加权空间，再积分；通过普通 L² 的 FTC
识别给定原路径。输入只要求初始加权成员，没有要求全时段加权成员。

本文件证明成员保持、闭区间加权连续及内部真实加权求导。
它使用 h、l 的普通 L² 连续性；不由一个有限范数估计推断 C²。
(5.8) 的仅含 ∇u 的定量记忆估计仍需进一步使用阻尼及 l=h+φ。
-/
noncomputable section
open MeasureTheory Set
open LeanPML.Analysis
namespace LeanPML.PML.SpatialAbsorption
variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/-- 连续线性强迫算子把普通 L² 连续路径变成加权连续右端。
没有使用点值代表或未经证明的“逐点可导⇒L² 可导”。 -/
theorem continuousOn_auxiliaryRateX (ν : Measure α) (C : SpatialAbsorption α)
    (h l : ℝ → ScalarL2 ν) (I : Set ℝ)
    (hh : ContinuousOn h I) (hl : ContinuousOn l I) :
    ContinuousOn (fun s => C.auxiliaryRateX ν (h s) (l s)) I :=
  ((C.xAbsorptionLift ν true).continuous.comp_continuousOn hh).sub
    ((C.xAbsorptionLift ν false).continuous.comp_continuousOn hl)

/-- 实际加权 Bochner 历史：初值加上已构造加权右端的时间积分。
后续定理证明积分可积，并与原普通 L² 解识别，故不是任意命名的 φ。 -/
def auxiliaryWeightedHistory (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (h l : ℝ → ScalarL2 ν) (t : ℝ) :
    WeightedL2 ν C.wx := W₀ + ∫ s in (0 : ℝ)..t, C.auxiliaryRateX ν (h s) (l s)

/-- 历史在零时刻等于给定加权初值；也处理 T=0 的单点情形。 -/
theorem auxiliaryWeightedHistory_initial (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (h l : ℝ → ScalarL2 ν) :
    C.auxiliaryWeightedHistory ν W₀ h l 0 = W₀ := by
  simp [auxiliaryWeightedHistory]

/-- 从闭区间普通 L² 连续推出加权历史的闭区间连续。
可积性由连续右端与有限时间区间获得，不依靠积分的总定义。 -/
theorem continuousOn_auxiliaryWeightedHistory (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (h l : ℝ → ScalarL2 ν) (T : ℝ) (hT : 0 ≤ T)
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T)) :
    ContinuousOn (C.auxiliaryWeightedHistory ν W₀ h l) (Icc 0 T) := by
  letI : CompleteSpace (WeightedL2 ν C.wx) := weighted_completeSpace ν C.wx C.wx_measurable
  have hrate := C.continuousOn_auxiliaryRateX ν h l (Icc 0 T) hh hl
  have hint := hrate.intervalIntegrable_of_Icc (μ := volume) hT
  have hprimitive := intervalIntegral.continuousOn_primitive_interval' hint (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
  rw [uIcc_of_le hT] at hprimitive
  exact continuousOn_const.add hprimitive

/-- 内部求导在实际加权范数中成立，导数是上一模块构造的加权右端。
只使用内部点的连续性邻域；没有要求端点普通双侧导数或端点方程。 -/
theorem hasDerivAt_auxiliaryWeightedHistory (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (h l : ℝ → ScalarL2 ν) (T t : ℝ)
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (ht : t ∈ Ioo 0 T) :
    HasDerivAt (C.auxiliaryWeightedHistory ν W₀ h l)
      (C.auxiliaryRateX ν (h t) (l t)) t := by
  letI : CompleteSpace (WeightedL2 ν C.wx) := weighted_completeSpace ν C.wx C.wx_measurable
  have hrate := C.continuousOn_auxiliaryRateX ν h l (Icc 0 T) hh hl
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2.le⟩
  have hint := (hrate.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1.le
  have hmeas := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo
    (hrate.mono Ioo_subset_Icc_self) t ht
  have hcontinuous := (hrate t ⟨ht.1.le, ht.2.le⟩).continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint hmeas hcontinuous
  exact ((hasDerivAt_const t W₀).add hderiv).congr_deriv (zero_add _)

/-- 成员传播的识别步骤：从普通 L² 原演化和初值推出物理恢复等于原 φ。
PDE/ODE 只在 (0,T) 输入；闭区间连续允许比较两个端点。
全时段加权成员是本条及下条的结论，不在输入中。 -/
theorem physical_auxiliaryWeightedHistory (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (φ h l : ℝ → ScalarL2 ν) (T : ℝ)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (hinitial : physicalL2 ν C.wx C.wx_measurable C.wx_gap W₀ = φ 0)
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt φ (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (l s)) s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    physicalL2 ν C.wx C.wx_measurable C.wx_gap
      (C.auxiliaryWeightedHistory ν W₀ h l t) = φ t := by
  letI : CompleteSpace (WeightedL2 ν C.wx) := weighted_completeSpace ν C.wx C.wx_measurable
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hrate := C.continuousOn_auxiliaryRateX ν h l (Icc 0 T) hh hl
  have hint := (hrate.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
  have hordinary_cont : ContinuousOn
      (fun s => C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (l s)) (Icc 0 T) :=
    (C.rCoeff.operator ν).continuous.comp_continuousOn hh |>.sub
      ((C.pCoeff.operator ν).continuous.comp_continuousOn hl)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hφ.mono hsub)
    (fun s hs => hODE s ⟨hs.1, hs.2.trans_le ht.2⟩)
    ((hordinary_cont.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1)
  calc
    physicalL2 ν C.wx C.wx_measurable C.wx_gap
        (C.auxiliaryWeightedHistory ν W₀ h l t) =
        φ 0 + ∫ s in (0 : ℝ)..t,
          physicalL2 ν C.wx C.wx_measurable C.wx_gap (C.auxiliaryRateX ν (h s) (l s)) := by
      rw [auxiliaryWeightedHistory, map_add, hinitial,
        ← (physicalL2 ν C.wx C.wx_measurable C.wx_gap).intervalIntegral_comp_comm hint]
    _ = φ 0 + (φ t - φ 0) := by simp_rw [C.physical_auxiliaryRateX]; rw [hFTC]
    _ = φ t := by abel

/-- 全时段加权成员与零区保持，由真实普通 L² 演化推出。
右端给出 √w φ∈L² 以及 w=0 区 φ=0（均 a.e.）；并不读取代表元的指定点。
输入只含初始加权代表和普通场连续/导数，允许权重无界。 -/
theorem auxiliary_weighted_membership (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (φ h l : ℝ → ScalarL2 ν) (T : ℝ)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (hinitial : physicalL2 ν C.wx C.wx_measurable C.wx_gap W₀ = φ 0)
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt φ (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (l s)) s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    MemLp (fun x => Real.sqrt (C.wx x) * φ t x) 2 ν ∧
      (∀ᵐ x ∂ν, C.wx x = 0 → φ t x = 0) := by
  apply (physicalL2_range_iff ν C.wx C.wx_measurable C.wx_gap (φ t)).mp
  exact ⟨C.auxiliaryWeightedHistory ν W₀ h l t,
    C.physical_auxiliaryWeightedHistory ν W₀ φ h l T hφ hh hl hinitial hODE ht⟩

/-- 在空间兼容 l=h+φ 下，已构造历史确实满足 (5.7) 对应的加权阻尼 ODE。
原 φ 仍只有普通 L² 演化输入；先由 FTC 识别，再把空间关系传给加权导数。
本条不是变常数积分公式，也不代替 (5.8) 的精确时间估计。 -/
theorem hasDerivAt_auxiliaryWeightedHistory_damped
    (ν : Measure α) (C : SpatialAbsorption α) (W₀ : WeightedL2 ν C.wx)
    (φ h l : ℝ → ScalarL2 ν) (T t : ℝ)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (hinitial : physicalL2 ν C.wx C.wx_measurable C.wx_gap W₀ = φ 0)
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt φ (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (l s)) s)
    (hspace : l t = h t + φ t) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (C.auxiliaryWeightedHistory ν W₀ h l)
      (-(weightedMul ν C.wx C.pCoeff.value C.pCoeff.measurable
          C.pCoeff.bound C.pCoeff.abs_le (C.auxiliaryWeightedHistory ν W₀ h l t)) +
        C.differenceLift ν (h t)) t := by
  have hidentified := C.physical_auxiliaryWeightedHistory ν W₀ φ h l T
    hφ hh hl hinitial hODE ⟨ht.1.le, ht.2.le⟩
  have hspace_weighted : l t = h t + physicalL2 ν C.wx C.wx_measurable C.wx_gap
      (C.auxiliaryWeightedHistory ν W₀ h l t) := by rw [hidentified]; exact hspace
  have hderiv := C.hasDerivAt_auxiliaryWeightedHistory ν W₀ h l T t hh hl ht
  exact hderiv.congr_deriv (C.auxiliaryRateX_eq_damped ν _ _ _ hspace_weighted)

/-- 时间微分层：若普通 h、l 在该时刻真实可导，则加权右端路径真实可导。
导数是同一个有界算子作用于 dh、dl，并满足相同 2cS 界。
这是实际时间导数，不把 dh/dl 的变量名称当证据；不由此无条件宣称 C²。 -/
theorem hasDerivAt_auxiliaryRateX (ν : Measure α) (C : SpatialAbsorption α)
    (h l : ℝ → ScalarL2 ν) (dh dl : ScalarL2 ν) (t : ℝ)
    (hh : HasDerivAt h dh t) (hl : HasDerivAt l dl t) :
    HasDerivAt (fun s => C.auxiliaryRateX ν (h s) (l s))
      (C.auxiliaryRateX ν dh dl) t ∧
    ‖C.auxiliaryRateX ν dh dl‖ ^ 2 ≤ 2 * C.c * C.S * (‖dh‖ ^ 2 + ‖dl‖ ^ 2) := by
  have hgradient := (C.xAbsorptionLift ν true).hasFDerivAt.comp_hasDerivAt t hh
  have hflux := (C.xAbsorptionLift ν false).hasFDerivAt.comp_hasDerivAt t hl
  exact ⟨hgradient.sub hflux, C.auxiliaryRateX_norm_sq ν dh dl⟩

/-- 把成员传播接到实际弱梯度与 H(div) 通量路径。
连续性在图范数中输入，再由已证连续坐标投影传到普通 L²。
这是真实弱场接口调用；尚未要求其满足全部原八变量方程。 -/
theorem auxiliary_weak_field_membership (D : LeanPML.Rectangle.Rect)
    (C : SpatialAbsorption (ℝ × ℝ))
    (W₀ : WeightedL2 D.measure C.wx) (φ : ℝ → ScalarL2 D.measure)
    (u : ℝ → LeanPML.Rectangle.weakH1Graph D)
    (L : ℝ → LeanPML.Rectangle.weakHDivGraph D) (T : ℝ)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T)) (hL : ContinuousOn L (Icc 0 T))
    (hinitial : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀ = φ 0)
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt φ (C.rCoeff.operator D.measure ((u s).val 1) -
        C.pCoeff.operator D.measure ((L s).val 0)) s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    MemLp (fun x => Real.sqrt (C.wx x) * φ t x) 2 D.measure ∧
      (∀ᵐ x ∂D.measure, C.a x = 0 → φ t x = 0) := by
  have hgradient : ContinuousOn (fun s => (u s).val 1) (Icc 0 T) :=
    (LeanPML.Rectangle.weakH1Coordinate D 1).continuous.comp_continuousOn hu
  have hflux : ContinuousOn (fun s => (L s).val 0) (Icc 0 T) :=
    (LeanPML.Rectangle.weakHDivCoordinate D 0).continuous.comp_continuousOn hL
  have hmember := C.auxiliary_weighted_membership D.measure W₀ φ
    (fun s => (u s).val 1) (fun s => (L s).val 0) T hφ hgradient hflux hinitial hODE ht
  simpa only [C.wx_eq_zero_iff] using hmember

end LeanPML.PML.SpatialAbsorption

