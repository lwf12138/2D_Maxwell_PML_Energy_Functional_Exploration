import LeanPML.Rectangle.Fields

/-!
# v0.4.1：四条外边上的真实迹与 PEC

对应 V7 (2.2)、(7.5)。边界数据是四条紧区间上的连续函数，顺序为右、左、上、下。
迹来自光滑代表在闭矩形边上的实际值；Fields 已证明相同 L² 类的光滑代表在
闭矩形上相等，所以这里的迹不依赖选择，且不从任意 L² 代表直接读边界。
这里只建 PEC（E 的四边零值）；不增加任何磁场法向或内部区域边界条件。
Green 的四边配对与外法向符号在下一文件中证明。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
namespace LeanPML.Rectangle

/-- 四边数据空间：右、左边参数为 y；上、下边参数为 x。
连续数据保证后续与光滑通量相乘的每条边界密度可积。 -/
abbrev BoundaryData (D : Rect) :=
  C(Icc D.ylo D.yhi, ℝ) × C(Icc D.ylo D.yhi, ℝ) ×
  C(Icc D.xlo D.xhi, ℝ) × C(Icc D.xlo D.xhi, ℝ)

/-- 光滑代表的四边实际取值，按 right/left/top/bottom 顺序。 -/
def smoothTrace (D : Rect) : SmoothField →ₗ[ℝ] BoundaryData D where
  toFun f :=
    (⟨fun y => f (D.xhi,y), f.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩,
     ⟨fun y => f (D.xlo,y), f.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩,
     ⟨fun x => f (x,D.yhi), f.continuous.comp (continuous_subtype_val.prodMk continuous_const)⟩,
     ⟨fun x => f (x,D.ylo), f.continuous.comp (continuous_subtype_val.prodMk continuous_const)⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 由 Fields 的闭矩形唯一性推出四边迹代表无关。
不是把任意等价类的边界值相同作为新假设。 -/
theorem smoothTrace_independent (D : Rect) (f g : SmoothField)
    (hclass : SmoothField.toL2 D f = SmoothField.toL2 D g) :
    smoothTrace D f = smoothTrace D g := by
  have hclosed := SmoothField.eqOn_closed_of_toL2_eq D f g hclass
  apply Prod.ext
  · apply ContinuousMap.ext
    intro y
    exact hclosed ⟨⟨D.x_lt.le,le_rfl⟩,y.property⟩
  · apply Prod.ext
    · apply ContinuousMap.ext
      intro y
      exact hclosed ⟨⟨le_rfl,D.x_lt.le⟩,y.property⟩
    · apply Prod.ext
      · apply ContinuousMap.ext
        intro x
        exact hclosed ⟨x.property,⟨D.y_lt.le,le_rfl⟩⟩
      · apply ContinuousMap.ext
        intro x
        exact hclosed ⟨x.property,⟨le_rfl,D.y_lt.le⟩⟩

/-- 具体迹作为受限 L² 域上的线性映射；核就是本光滑类的零迹域。 -/
def trace (D : Rect) : fieldDomain D →ₗ[ℝ] BoundaryData D :=
  descend D (smoothTrace D) (smoothTrace_independent D)

/-- 具体迹在任何原光滑代表上等于直接四边取值。 -/
theorem trace_toL2 (D : Rect) (f : SmoothField) :
    trace D ⟨SmoothField.toL2 D f, ⟨f,rfl⟩⟩ = smoothTrace D f :=
  descend_toL2 D (smoothTrace D) (smoothTrace_independent D) f

/-- 实际函数的全外边界零值条件；仅 E 被要求满足它才称 PEC。
一般提升 u 的零迹还需要其初值和历史积分，不能由这个定义自动获得。 -/
def ZeroBoundary (D : Rect) (f : ℝ × ℝ → ℝ) : Prop :=
  (∀ y ∈ Icc D.ylo D.yhi, f (D.xhi,y) = 0) ∧
  (∀ y ∈ Icc D.ylo D.yhi, f (D.xlo,y) = 0) ∧
  (∀ x ∈ Icc D.xlo D.xhi, f (x,D.yhi) = 0) ∧
  (∀ x ∈ Icc D.xlo D.xhi, f (x,D.ylo) = 0)

/-- 迹为零恰好是四条外边逐条为零，供 Green 零边界消去使用。 -/
theorem smoothTrace_eq_zero_iff (D : Rect) (f : SmoothField) :
    smoothTrace D f = 0 ↔ ZeroBoundary D f := by
  constructor
  · intro hzero
    have hr := congrArg Prod.fst hzero
    have hl := congrArg (fun B : BoundaryData D => B.2.1) hzero
    have ht := congrArg (fun B : BoundaryData D => B.2.2.1) hzero
    have hb := congrArg (fun B : BoundaryData D => B.2.2.2) hzero
    exact ⟨fun y hy => congrArg (fun g => g ⟨y,hy⟩) hr,
      fun y hy => congrArg (fun g => g ⟨y,hy⟩) hl,
      fun x hx => congrArg (fun g => g ⟨x,hx⟩) ht,
      fun x hx => congrArg (fun g => g ⟨x,hx⟩) hb⟩
  · intro hboundary
    apply Prod.ext
    · exact ContinuousMap.ext (fun y => hboundary.1 y y.property)
    · apply Prod.ext
      · exact ContinuousMap.ext (fun y => hboundary.2.1 y y.property)
      · apply Prod.ext
        · exact ContinuousMap.ext (fun x => hboundary.2.2.1 x x.property)
        · exact ContinuousMap.ext (fun x => hboundary.2.2.2 x x.property)

/-- 受限 L² 域中迹为零，与所选光滑代表的整个外边界为零等价。 -/
theorem trace_zero_iff (D : Rect) (U : fieldDomain D) :
    trace D U = 0 ↔ ZeroBoundary D (representative D U) :=
  smoothTrace_eq_zero_iff D (representative D U)

/-- 零迹在乘子 V+cv 下保持；两层分别需要 u/E 和 E/E_t 的零迹。
这是四边逐项线性结论，没有额外磁约束。 -/
theorem ZeroBoundary.add_smul (D : Rect) {f g : ℝ × ℝ → ℝ}
    (hf : ZeroBoundary D f) (hg : ZeroBoundary D g) (c : ℝ) :
    ZeroBoundary D (fun z => f z + c * g z) := by
  exact ⟨fun y hy => by simp [hf.1 y hy, hg.1 y hy],
    fun y hy => by simp [hf.2.1 y hy, hg.2.1 y hy],
    fun x hx => by simp [hf.2.2.1 x hx, hg.2.2.1 x hx],
    fun x hx => by simp [hf.2.2.2 x hx, hg.2.2.2 x hx]⟩

/-- 非零调用：矩形多项式泡函数，在整个外边界为零，内部严格正。
这验证具体迹/L²域非平凡，不声称它是 PML 解。 -/
def rectangleBubble (D : Rect) : SmoothField :=
  ⟨fun z => (z.1-D.xlo)*(D.xhi-z.1)*(z.2-D.ylo)*(D.yhi-z.2), by
    change ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (z.1-D.xlo)*(D.xhi-z.1)*(z.2-D.ylo)*(D.yhi-z.2))
    fun_prop⟩

/-- 泡函数的四边值逐项消去；供实际 Green/Poincaré 调用。 -/
theorem rectangleBubble_zeroBoundary (D : Rect) : ZeroBoundary D (rectangleBubble D) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro z hz <;> simp [rectangleBubble]

/-- 泡函数在矩形中心为正，证明几何及零迹空间不是空实现。 -/
theorem rectangleBubble_midpoint_pos (D : Rect) :
    0 < rectangleBubble D ((D.xlo+D.xhi)/2, (D.ylo+D.yhi)/2) := by
  change 0 < ((D.xlo+D.xhi)/2-D.xlo)*(D.xhi-(D.xlo+D.xhi)/2)*
    ((D.ylo+D.yhi)/2-D.ylo)*(D.yhi-(D.ylo+D.yhi)/2)
  apply mul_pos
  · apply mul_pos
    · apply mul_pos <;> linarith [D.x_lt]
    · linarith [D.y_lt]
  · linarith [D.y_lt]

/-- 非零光滑泡函数确实给出非零 L² 类；不能只用单点值来判断任意 L²。
这里借助已证“连续代表 a.e. 相等 ⇒ 开矩形相等”。 -/
theorem rectangleBubble_toL2_ne_zero (D : Rect) :
    SmoothField.toL2 D (rectangleBubble D) ≠ 0 := by
  intro hzero
  have hclass : SmoothField.toL2 D (rectangleBubble D) = SmoothField.toL2 D 0 := by
    simpa using hzero
  have hmid : ((D.xlo+D.xhi)/2, (D.ylo+D.yhi)/2) ∈ D.openSet := by
    change (D.xlo < (D.xlo+D.xhi)/2 ∧ (D.xlo+D.xhi)/2 < D.xhi) ∧
      (D.ylo < (D.ylo+D.yhi)/2 ∧ (D.ylo+D.yhi)/2 < D.yhi)
    exact ⟨⟨by linarith [D.x_lt], by linarith [D.x_lt]⟩,
      ⟨by linarith [D.y_lt], by linarith [D.y_lt]⟩⟩
  have hvalue := SmoothField.eqOn_open_of_toL2_eq D (rectangleBubble D) 0 hclass hmid
  have hpos := rectangleBubble_midpoint_pos D
  change rectangleBubble D _ = 0 at hvalue
  linarith

end LeanPML.Rectangle
