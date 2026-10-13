import LeanPML.Analysis.WeightedL2
import LeanPML.Rectangle.Fields

/-!
# v0.4.3：加权正则性与原物理场的真实连接

为兑现 V7 (5.6)、(6.6) 所需接口，以下在明确加权正则性与光滑表示条件下
证明导数识别；这些技术条件并非自动由 (6.6) 的弱空间表述推出。原文未单列。
权重可无界，因此普通 L² 可导不能代替加权可导。本文件明确输入加权
路径的 `DifferentiableAt`，再由连续线性恢复、实际普通 L² 导数及唯一性
识别加权导数。这样没有把任意加权导数坐标叫作 φ_t。
零区物理场为零的证据必须来自初始兼容保持；此文件不证明 (5.7)/(5.8)
的自动传播，也不从光滑性推断无界权重下可积。
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
open LeanPML.Analysis

namespace LeanPML.PML

variable {α : Type*} [MeasurableSpace α]

/-- 服务于 (6.6) 的加权导数识别引理。X 在真实加权范数内可微是正则性输入；
Y 是同一物理场的普通 L² 路径，邻域相等保证不能只靠单点取值求导。
先恢复未知加权导数，再用普通导数唯一性与恢复单射识别为 Xdot。
后续两层路径用本定理把 φ_t、φ_tt 接回加权坐标。 -/
theorem hasDerivAt_weighted_of_physical
    (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    {X : ℝ → WeightedL2 ν w} {Y : ℝ → ScalarL2 ν}
    {Xdot : WeightedL2 ν w} {t : ℝ}
    (hweighted : DifferentiableAt ℝ X t)
    (hphysical : (fun s => physicalL2 ν w hw hgap (X s)) =ᶠ[𝓝 t] Y)
    (hY : HasDerivAt Y (physicalL2 ν w hw hgap Xdot) t) :
    HasDerivAt X Xdot t := by
  have hunknown : HasDerivAt X (deriv X t) t := hweighted.hasDerivAt
  have hrecovered : HasDerivAt (fun s => physicalL2 ν w hw hgap (X s))
      (physicalL2 ν w hw hgap (deriv X t)) t :=
    hasDerivAt_physicalL2 ν w hw hgap hunknown
  have hsame_derivative : physicalL2 ν w hw hgap (deriv X t) =
      physicalL2 ν w hw hgap Xdot :=
    (hrecovered.congr_of_eventuallyEq hphysical.symm).unique hY
  have hidentified : deriv X t = Xdot :=
    physicalL2_injective ν w hw hgap hsame_derivative
  rw [hidentified] at hunknown
  exact hunknown

end LeanPML.PML

namespace LeanPML.Rectangle

/-- 光滑物理函数在零区消失且有实际加权成员证据时，其平方根坐标恢复为
原来的 SmoothField.toL2；不是仅在某个点读取 L² 商类。来源：(5.6)。 -/
theorem weighted_smooth_recovery (D : Rect) (w : (ℝ × ℝ) → ℝ)
    (hw : Measurable w) (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    (f : SmoothField)
    (hweighted : MemLp (fun x => Real.sqrt (w x) * f x) 2 D.measure)
    (hzero : ∀ᵐ x ∂D.measure, w x = 0 → f x = 0) :
    physicalL2 D.measure w hw hgap (weightedOfFunction D.measure w f hweighted) =
      SmoothField.toL2 D f := by
  apply Lp.ext
  exact (physicalL2_weightedOfFunction D.measure w f hw hgap hweighted hzero).trans
    (SmoothField.coe_toL2 D f).symm

/-- 为实现 (6.6) 接口采用的光滑场版本：加权路径由物理函数乘 √w 构造。
加权可微性仅断言导数存在；导数值由已证普通 L² 时间导数识别。
零区条件在邻域内明确使用，导数场也需其实际加权成员和零区证据。
这允许无界 w，不假设乘 w 是普通 L² 有界算子。 -/
theorem hasDerivAt_weighted_smooth (D : Rect) (w : (ℝ × ℝ) → ℝ)
    (hw : Measurable w) (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    (F : ℝ → SmoothField) (Fdot : SmoothField) (t : ℝ)
    (hmem : ∀ s, MemLp (fun x => Real.sqrt (w x) * F s x) 2 D.measure)
    (hmem_dot : MemLp (fun x => Real.sqrt (w x) * Fdot x) 2 D.measure)
    (hzero : ∀ᶠ s in 𝓝 t, ∀ᵐ x ∂D.measure, w x = 0 → F s x = 0)
    (hzero_dot : ∀ᵐ x ∂D.measure, w x = 0 → Fdot x = 0)
    (hweighted : DifferentiableAt ℝ
      (fun s => weightedOfFunction D.measure w (F s) (hmem s)) t)
    (hordinary : HasDerivAt (fun s => SmoothField.toL2 D (F s))
      (SmoothField.toL2 D Fdot) t) :
    HasDerivAt (fun s => weightedOfFunction D.measure w (F s) (hmem s))
      (weightedOfFunction D.measure w Fdot hmem_dot) t := by
  apply LeanPML.PML.hasDerivAt_weighted_of_physical D.measure w hw hgap hweighted
  · filter_upwards [hzero] with s hs
    exact weighted_smooth_recovery D w hw hgap (F s) (hmem s) hs
  · rw [weighted_smooth_recovery D w hw hgap Fdot hmem_dot hzero_dot]
    exact hordinary

end LeanPML.Rectangle
