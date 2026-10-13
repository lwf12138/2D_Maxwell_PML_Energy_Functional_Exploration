import LeanPML.Rectangle.SmoothPaths
import LeanPML.PML.MainAbstract

/-!
# v0.4.3：实际光滑场与加权坐标组成同源状态路径

为兑现 V7 (6.3)、(6.6) 所需接口，采用更强的光滑与一致范数技术条件；
本构造由这些明确输入推出，不能反称技术条件由 (6.6) 保证。原文未单列。
普通坐标来自实际 SmoothField.toL2，加权坐标来自 √wφ 的真实 L² 类。
正则性结构只含成员资格、连续性与可微性；零区保持单独作为下游须证明的
兼容结论传入低层构造，绝不作为原系统解定义的一部分。
最终 OriginalSystem 入口须从初值和真实演化提供这些兼容结论。
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
open LeanPML.Analysis LeanPML.PML
namespace LeanPML.Rectangle

/-- 实际时空函数的八组时间层。V 是独立坐标，只有后面的速度证据才能
将其认作 v_t；加权 φ 的物理函数也保留，不能只给任意抽象加权坐标。 -/
structure SmoothStateData where
  v : SmoothTimeJet
  V : SmoothTimeJet
  R : SmoothTimeJet
  z : SmoothTimeJet
  Λx : SmoothTimeJet
  Λy : SmoothTimeJet
  φx : SmoothTimeJet
  φy : SmoothTimeJet

/-- (6.6) 的明确加权正则性输入。成员资格是实际 √wφ∈L²；可微性在
加权范数中要求，但不指定导数值。导数由恢复映射与普通导数唯一性识别。
这没有证明 (5.7)/(5.8) 的自动传播。 -/
structure WeightedJetRegular (D : Rect) (w : (ℝ × ℝ) → ℝ) (J : SmoothTimeJet) where
  mem_value : ∀ t, MemLp (fun x => Real.sqrt (w x) * J.value t x) 2 D.measure
  mem_first : ∀ t, MemLp (fun x => Real.sqrt (w x) * J.first t x) 2 D.measure
  mem_second : ∀ t, MemLp (fun x => Real.sqrt (w x) * J.second t x) 2 D.measure
  continuous_value : Continuous (fun t => weightedOfFunction D.measure w (J.value t) (mem_value t))
  continuous_first : Continuous (fun t => weightedOfFunction D.measure w (J.first t) (mem_first t))
  differentiable_value : Differentiable ℝ (fun t => weightedOfFunction D.measure w (J.value t) (mem_value t))
  differentiable_first : Differentiable ℝ (fun t => weightedOfFunction D.measure w (J.first t) (mem_first t))

/-- 原始正则性，逐坐标列出以便审查；没有方程、兼容保持或能量结论字段。 -/
structure SmoothStateRegular (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (B : SmoothStateData) where
  v : UniformTimeJet D B.v
  V : UniformTimeJet D B.V
  R : UniformTimeJet D B.R
  z : UniformTimeJet D B.z
  Λx : UniformTimeJet D B.Λx
  Λy : UniformTimeJet D B.Λy
  φx : UniformTimeJet D B.φx
  φy : UniformTimeJet D B.φy
  weightedX : WeightedJetRegular D C.wx B.φx
  weightedY : WeightedJetRegular D C.wy B.φy

/-- (6.3) 的Base层：每个坐标来自同一实际函数的 value 时间层。
这只是状态定义；真实导数关系在下方 分别 证明。 -/
def smoothStateBase (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B) (t : ℝ) :
    FieldState D.measure C.wx C.wy where
  v := SmoothField.toL2 D (B.v.value t)
  V := SmoothField.toL2 D (B.V.value t)
  R := SmoothField.toL2 D (B.R.value t)
  z := SmoothField.toL2 D (B.z.value t)
  Λx := SmoothField.toL2 D (B.Λx.value t)
  Λy := SmoothField.toL2 D (B.Λy.value t)
  ψx := weightedOfFunction D.measure C.wx (B.φx.value t) (reg.weightedX.mem_value t)
  ψy := weightedOfFunction D.measure C.wy (B.φy.value t) (reg.weightedY.mem_value t)

/-- (6.3) 的First层：每个坐标来自同一实际函数的 first 时间层。
这只是状态定义；真实导数关系在下方 分别 证明。 -/
def smoothStateFirst (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B) (t : ℝ) :
    FieldState D.measure C.wx C.wy where
  v := SmoothField.toL2 D (B.v.first t)
  V := SmoothField.toL2 D (B.V.first t)
  R := SmoothField.toL2 D (B.R.first t)
  z := SmoothField.toL2 D (B.z.first t)
  Λx := SmoothField.toL2 D (B.Λx.first t)
  Λy := SmoothField.toL2 D (B.Λy.first t)
  ψx := weightedOfFunction D.measure C.wx (B.φx.first t) (reg.weightedX.mem_first t)
  ψy := weightedOfFunction D.measure C.wy (B.φy.first t) (reg.weightedY.mem_first t)

/-- (6.3) 的Second层：每个坐标来自同一实际函数的 second 时间层。
这只是状态定义；真实导数关系在下方 分别 证明。 -/
def smoothStateSecond (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B) (t : ℝ) :
    FieldState D.measure C.wx C.wy where
  v := SmoothField.toL2 D (B.v.second t)
  V := SmoothField.toL2 D (B.V.second t)
  R := SmoothField.toL2 D (B.R.second t)
  z := SmoothField.toL2 D (B.z.second t)
  Λx := SmoothField.toL2 D (B.Λx.second t)
  Λy := SmoothField.toL2 D (B.Λy.second t)
  ψx := weightedOfFunction D.measure C.wx (B.φx.second t) (reg.weightedX.mem_second t)
  ψy := weightedOfFunction D.measure C.wy (B.φy.second t) (reg.weightedY.mem_second t)

/-- 零区兼容的中间命题，供下方构造使用。它是保持定理的输出接口，
不能作为最终原系统解的正则性假设。此处仅记录当前内时段所需的三层零值。 -/
structure SmoothZeroOn (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (I : Set ℝ) : Prop where
  φx_value : ∀ t ∈ I, ∀ᵐ x ∂D.measure, C.wx x = 0 → B.φx.value t x = 0
  φx_first : ∀ t ∈ I, ∀ᵐ x ∂D.measure, C.wx x = 0 → B.φx.first t x = 0
  φx_second : ∀ t ∈ I, ∀ᵐ x ∂D.measure, C.wx x = 0 → B.φx.second t x = 0
  φy_value : ∀ t ∈ I, ∀ᵐ x ∂D.measure, C.wy x = 0 → B.φy.value t x = 0
  φy_first : ∀ t ∈ I, ∀ᵐ x ∂D.measure, C.wy x = 0 → B.φy.first t x = 0
  φy_second : ∀ t ∈ I, ∀ᵐ x ∂D.measure, C.wy x = 0 → B.φy.second t x = 0

/-- (6.3) 的实际 Base→First 求导。普通分量调用 C(K)→L² 桥接，
加权分量使用已证明恢复单射识别导数；不从逐点可导直接跳入加权范数。 -/
theorem hasDerivAt_smoothStateBase (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    {I : Set ℝ} (hI : IsOpen I) (hzero : SmoothZeroOn D C B I)
    {t : ℝ} (ht : t ∈ I) :
    StateHasDerivAt (smoothStateBase D C B reg) (smoothStateFirst D C B reg t) t := by
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ I := hI.mem_nhds ht
  constructor
  · exact hasDerivAt_jet_value_L2 D B.v reg.v t
  · exact hasDerivAt_jet_value_L2 D B.V reg.V t
  · exact hasDerivAt_jet_value_L2 D B.R reg.R t
  · exact hasDerivAt_jet_value_L2 D B.z reg.z t
  · apply hasDerivAt_weighted_smooth D C.wx C.wx_measurable C.wx_gap
      B.φx.value (B.φx.first t) t reg.weightedX.mem_value
      (reg.weightedX.mem_first t)
    · exact hnear.mono (fun s hs => hzero.φx_value s hs)
    · exact hzero.φx_first t ht
    · exact reg.weightedX.differentiable_value t
    · exact hasDerivAt_jet_value_L2 D B.φx reg.φx t
  · apply hasDerivAt_weighted_smooth D C.wy C.wy_measurable C.wy_gap
      B.φy.value (B.φy.first t) t reg.weightedY.mem_value
      (reg.weightedY.mem_first t)
    · exact hnear.mono (fun s hs => hzero.φy_value s hs)
    · exact hzero.φy_first t ht
    · exact reg.weightedY.differentiable_value t
    · exact hasDerivAt_jet_value_L2 D B.φy reg.φy t
  · exact hasDerivAt_jet_value_L2 D B.Λx reg.Λx t
  · exact hasDerivAt_jet_value_L2 D B.Λy reg.Λy t

/-- (6.3) 的实际 First→Second 求导。普通分量调用 C(K)→L² 桥接，
加权分量使用已证明恢复单射识别导数；不从逐点可导直接跳入加权范数。 -/
theorem hasDerivAt_smoothStateFirst (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    {I : Set ℝ} (hI : IsOpen I) (hzero : SmoothZeroOn D C B I)
    {t : ℝ} (ht : t ∈ I) :
    StateHasDerivAt (smoothStateFirst D C B reg) (smoothStateSecond D C B reg t) t := by
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ I := hI.mem_nhds ht
  constructor
  · exact hasDerivAt_jet_first_L2 D B.v reg.v t
  · exact hasDerivAt_jet_first_L2 D B.V reg.V t
  · exact hasDerivAt_jet_first_L2 D B.R reg.R t
  · exact hasDerivAt_jet_first_L2 D B.z reg.z t
  · apply hasDerivAt_weighted_smooth D C.wx C.wx_measurable C.wx_gap
      B.φx.first (B.φx.second t) t reg.weightedX.mem_first
      (reg.weightedX.mem_second t)
    · exact hnear.mono (fun s hs => hzero.φx_first s hs)
    · exact hzero.φx_second t ht
    · exact reg.weightedX.differentiable_first t
    · exact hasDerivAt_jet_first_L2 D B.φx reg.φx t
  · apply hasDerivAt_weighted_smooth D C.wy C.wy_measurable C.wy_gap
      B.φy.first (B.φy.second t) t reg.weightedY.mem_first
      (reg.weightedY.mem_second t)
    · exact hnear.mono (fun s hs => hzero.φy_first s hs)
    · exact hzero.φy_second t ht
    · exact reg.weightedY.differentiable_first t
    · exact hasDerivAt_jet_first_L2 D B.φy reg.φy t
  · exact hasDerivAt_jet_first_L2 D B.Λx reg.Λx t
  · exact hasDerivAt_jet_first_L2 D B.Λy reg.Λy t

/-- 从普通/加权场的正则性推出实际状态闭区间连续，不输入能量连续性。 -/
theorem continuous_smoothStateBase (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B) (I : Set ℝ) :
    StateContinuousOn (smoothStateBase D C B reg) I := by
  constructor
  · exact (continuous_jet_L2 D B.v reg.v).1.continuousOn
  · exact (continuous_jet_L2 D B.V reg.V).1.continuousOn
  · exact (continuous_jet_L2 D B.R reg.R).1.continuousOn
  · exact (continuous_jet_L2 D B.z reg.z).1.continuousOn
  · exact reg.weightedX.continuous_value.continuousOn
  · exact reg.weightedY.continuous_value.continuousOn
  · exact (continuous_jet_L2 D B.Λx reg.Λx).1.continuousOn
  · exact (continuous_jet_L2 D B.Λy reg.Λy).1.continuousOn

/-- 从普通/加权场的正则性推出实际状态闭区间连续，不输入能量连续性。 -/
theorem continuous_smoothStateFirst (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B) (I : Set ℝ) :
    StateContinuousOn (smoothStateFirst D C B reg) I := by
  constructor
  · exact (continuous_jet_L2 D B.v reg.v).2.1.continuousOn
  · exact (continuous_jet_L2 D B.V reg.V).2.1.continuousOn
  · exact (continuous_jet_L2 D B.R reg.R).2.1.continuousOn
  · exact (continuous_jet_L2 D B.z reg.z).2.1.continuousOn
  · exact reg.weightedX.continuous_first.continuousOn
  · exact reg.weightedY.continuous_first.continuousOn
  · exact (continuous_jet_L2 D B.Λx reg.Λx).2.1.continuousOn
  · exact (continuous_jet_L2 D B.Λy reg.Λy).2.1.continuousOn

/-- 同源路径的具体构造。hv/hq 是下游历史 FTC 已证明的坐标识别，
不是未绑定真实函数的速度命名；所有槽的 HasDerivAt 已由上面定理产生。
本低层构造不输入 primitive PDE 或任何能量结论。 -/
def smoothSameSourcePath (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (I : Set ℝ) (hI : IsOpen I) (hzero : SmoothZeroOn D C B I)
    (hv : ∀ t ∈ I, SmoothField.toL2 D (B.v.first t) = SmoothField.toL2 D (B.V.value t))
    (hq : ∀ t ∈ I, SmoothField.toL2 D (B.z.first t) = SmoothField.toL2 D (B.R.value t)) :
    SameSourcePath D.measure C.wx C.wy I where
  base := smoothStateBase D C B reg
  first := smoothStateFirst D C B reg
  second := smoothStateSecond D C B reg
  deriv_base := fun _ ht => hasDerivAt_smoothStateBase D C B reg hI hzero ht
  deriv_first := fun _ ht => hasDerivAt_smoothStateFirst D C B reg hI hzero ht
  velocity := fun t ht => (hasDerivAt_jet_value_L2 D B.v reg.v t).congr_deriv (hv t ht)
  primitivePolar := fun t ht => (hasDerivAt_jet_value_L2 D B.z reg.z t).congr_deriv (hq t ht)

end LeanPML.Rectangle
