import LeanPML.Rectangle.Boundary

/-!
# v0.4.3：一致范数路径到真实矩形 L² 路径

本文件把闭矩形上的连续函数空间 C(K) 连续线性地送入既有 ScalarL2。
借助显式矩形截断延拓及 mathlib 的 bounded continuous → Lp 映射，
保证连续性、可导性都是空间范数中的结论，不由逐点求导直接跳步。
所选更强正则性可输入 C(K) 路径可导；导数值再由每个点的真实导数唯一性识别。
这不假设目标 L² 导数，不假设 PDE，也不自动证明加权可积性。
-/
noncomputable section
open MeasureTheory Set BoundedContinuousFunction
open scoped Topology
open LeanPML.Analysis
namespace LeanPML.Rectangle

instance (D : Rect) : CompactSpace D.closedSet := isCompact_iff_compactSpace.mp D.closedSet_compact

/-- 闭矩形上的一致范数连续函数空间。 -/
abbrev ContinuousField (D : Rect) := C(D.closedSet, ℝ)

/-- 连续截断到闭矩形，仅用于构造空间范数映射；域内取值保持原样。 -/
def clampPoint (D : Rect) : C(ℝ × ℝ, D.closedSet) where
  toFun z := ⟨(max D.xlo (min D.xhi z.1), max D.ylo (min D.yhi z.2)),
    ⟨⟨le_max_left _ _, max_le D.x_lt.le (min_le_left _ _)⟩,
     ⟨le_max_left _ _, max_le D.y_lt.le (min_le_left _ _)⟩⟩⟩
  continuous_toFun := by fun_prop

/-- 域内截断是恒等；因此外部技术延拓不会更改整个矩形积分。 -/
theorem clampPoint_eq (D : Rect) (z : ℝ × ℝ) (hz : z ∈ D.closedSet) :
    (clampPoint D z : ℝ × ℝ) = z := by
  simp only [clampPoint, ContinuousMap.coe_mk, min_eq_right hz.1.2,
    min_eq_right hz.2.2, max_eq_right hz.1.1, max_eq_right hz.2.1]

/-- C(K) 的连续截断延拓是有界连续函数；sup 范数不增加。 -/
def extendContinuous (D : Rect) : ContinuousField D →L[ℝ] ((ℝ × ℝ) →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => (BoundedContinuousFunction.mkOfCompact f).compContinuous (clampPoint D)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by
      simpa using (BoundedContinuousFunction.norm_compContinuous_le
        (BoundedContinuousFunction.mkOfCompact f) (clampPoint D)))

/-- 实际矩形 C(K)→L² 连续线性映射；measure 是原来的整个矩形测度。 -/
def continuousToL2 (D : Rect) : ContinuousField D →L[ℝ] ScalarL2 D.measure :=
  (BoundedContinuousFunction.toLp 2 D.measure ℝ).comp (extendContinuous D)

/-- 光滑场在闭矩形的实际连续限制。 -/
def restrictContinuous (D : Rect) : SmoothField →ₗ[ℝ] ContinuousField D where
  toFun f := ⟨fun z => f z, f.continuous.comp continuous_subtype_val⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 两种 L² 构造一致：新 C(K) 映射接回 v0.4.1 的光滑 toL2。
证明只用域内截断恒等和 a.e. 代表等式，不逐点读取 L² 商类。 -/
theorem continuousToL2_restrict (D : Rect) (f : SmoothField) :
    continuousToL2 D (restrictContinuous D f) = SmoothField.toL2 D f := by
  apply Lp.ext
  have hext := BoundedContinuousFunction.coeFn_toLp 2 D.measure ℝ
    (extendContinuous D (restrictContinuous D f))
  have hmem : ∀ᵐ z ∂D.measure, z ∈ D.closedSet := by
    rw [D.measure_eq_closed]
    exact ae_restrict_mem D.closedSet_compact.measurableSet
  filter_upwards [hext, SmoothField.coe_toL2 D f, hmem] with z hzext hzf hz
  change (continuousToL2 D (restrictContinuous D f)) z = _ at hzext
  rw [hzext, hzf]
  change f (clampPoint D z) = f z
  rw [clampPoint_eq D z hz]

/-- 一致范数中的真实导数经连续线性映射成为真实 L² 导数。
该结论比逐点可导强，是后续 SameSourcePath 的构造工具。 -/
theorem hasDerivAt_continuousToL2 (D : Rect) {X : ℝ → ContinuousField D}
    {Xdot : ContinuousField D} {t : ℝ} (hX : HasDerivAt X Xdot t) :
    HasDerivAt (fun s => continuousToL2 D (X s)) (continuousToL2 D Xdot) t :=
  (continuousToL2 D).hasFDerivAt.comp_hasDerivAt t hX

/-- 一致范数路径导数值由各点的实际导数唯一决定。
hregular 只假设空间范数可导，不把期望的 L² 导数作为输入。 -/
theorem hasDerivAt_of_pointwise (D : Rect) (X : ℝ → ContinuousField D)
    (Xdot : ContinuousField D) (t : ℝ) (hregular : DifferentiableAt ℝ X t)
    (hpointwise : ∀ z : D.closedSet,
      HasDerivAt (fun s => X s z) (Xdot z) t) : HasDerivAt X Xdot t := by
  have hderivative : deriv X t = Xdot := by
    apply ContinuousMap.ext
    intro z
    have heval : HasDerivAt (fun s => X s z) ((deriv X t) z) t :=
      ((ContinuousMap.evalCLM ℝ z : ContinuousField D →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt t hregular.hasDerivAt
    exact heval.unique (hpointwise z)
  rw [← hderivative]
  exact hregular.hasDerivAt

/-- 逐点导数 + 一致范数可导正则性 ⇒ 真正 L² 导数。
这是总装时使用的入口；没有交换求导与空间积分的无证跳步。 -/
theorem hasDerivAt_L2_of_pointwise (D : Rect) (X : ℝ → ContinuousField D)
    (Xdot : ContinuousField D) (t : ℝ) (hregular : DifferentiableAt ℝ X t)
    (hpointwise : ∀ z : D.closedSet,
      HasDerivAt (fun s => X s z) (Xdot z) t) :
    HasDerivAt (fun s => continuousToL2 D (X s)) (continuousToL2 D Xdot) t :=
  hasDerivAt_continuousToL2 D (hasDerivAt_of_pointwise D X Xdot t hregular hpointwise)

/-- 闭区间 C(K) 路径连续性推出闭区间实际 L² 连续性，包含两个端点。 -/
theorem continuousOn_L2 (D : Rect) {I : Set ℝ} {X : ℝ → ContinuousField D}
    (hX : ContinuousOn X I) : ContinuousOn (fun s => continuousToL2 D (X s)) I :=
  (continuousToL2 D).continuous.comp_continuousOn hX

/-- 面向原场的直接入口：光滑时空切片的 toL2 路径拥有真实导数。
输入是闭矩形一致范数可导正则性及实际逐点导数，输出接入 StateHasDerivAt。 -/
theorem hasDerivAt_toL2_of_pointwise (D : Rect) (F : ℝ → SmoothField)
    (Fdot : SmoothField) (t : ℝ)
    (hregular : DifferentiableAt ℝ (fun s => restrictContinuous D (F s)) t)
    (hpointwise : ∀ z : D.closedSet, HasDerivAt (fun s => F s z) (Fdot z) t) :
    HasDerivAt (fun s => SmoothField.toL2 D (F s)) (SmoothField.toL2 D Fdot) t := by
  have hresult := hasDerivAt_L2_of_pointwise D
    (fun s => restrictContinuous D (F s)) (restrictContinuous D Fdot) t hregular hpointwise
  simpa only [continuousToL2_restrict] using hresult

/-- 原光滑场一致范数路径的闭区间连续性，接回旧 toL2 状态坐标。 -/
theorem continuousOn_toL2 (D : Rect) {I : Set ℝ} {F : ℝ → SmoothField}
    (hF : ContinuousOn (fun s => restrictContinuous D (F s)) I) :
    ContinuousOn (fun s => SmoothField.toL2 D (F s)) I := by
  simpa only [continuousToL2_restrict] using continuousOn_L2 D hF

/-- 非平凡调用：时间线性变化的零边界泡函数场，真正调用上述 L² 导数桥接。
空间泡函数已证明 L² 非零；这是接口测试，不是 PML 解存在性证明。 -/
theorem bubblePath_hasDerivAt (D : Rect) (t : ℝ) :
    HasDerivAt (fun s => SmoothField.toL2 D (s • rectangleBubble D))
      (SmoothField.toL2 D (rectangleBubble D)) t := by
  apply hasDerivAt_toL2_of_pointwise D (fun s => s • rectangleBubble D)
    (rectangleBubble D) t
  · have hlinear := (hasDerivAt_id t).smul_const
      (restrictContinuous D (rectangleBubble D))
    simpa only [map_smul, one_smul, id_eq] using! hlinear.differentiableAt
  · intro z
    change HasDerivAt (fun s => s * rectangleBubble D z) (rectangleBubble D z) t
    simpa only [one_mul, id_eq] using! (hasDerivAt_id t).mul_const (rectangleBubble D z)

end LeanPML.Rectangle
