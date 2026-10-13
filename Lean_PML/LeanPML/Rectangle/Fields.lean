import LeanPML.Rectangle.Domain
import LeanPML.PML.State
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# v0.4.1：光滑代表、真实坐标导数及受限 L² 梯度域

本轮取全空间 C∞ 延拓作为闭矩形邻域光滑场的技术表示；PDE 并不在域外成立。
这比 V7 (6.6) 的弱空间范围强，不宣称两种正则性等价。
`dx/dy` 是 Fréchet 导数作用于坐标单位向量，随后与一元真实导数连接。
`toL2` 将代表送入原来的实际 L²；a.e. 相等先提升为内部连续函数相等，
再用局部导数唯一性、闭包连续性证明导数与边界的代表元无关性。
最后才在像子空间上定义梯度；绝不对任意 L² 代表直接求导。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
open LeanPML.Analysis LeanPML.PML
namespace LeanPML.Rectangle

/-- 坐标偏导是真实 Fréchet 导数的 x 分量；未给出可微性时只是 mathlib 总定义。 -/
def dx (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := fderiv ℝ f z (1,0)
/-- 真实 y 偏导；其可微性证据来自下方 SmoothField。 -/
def dy (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := fderiv ℝ f z (0,1)

/-- 光滑延拓形成线性子空间。字段只有正则性，不含 Green、Poincaré 或能量结论。 -/
def smoothFields : Submodule ℝ (ℝ × ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by change ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (0:ℝ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ f at hf
    exact hf.const_smul c

abbrev SmoothField := ↥smoothFields

instance : CoeFun SmoothField (fun _ => ℝ × ℝ → ℝ) := ⟨fun f => f.val⟩

namespace SmoothField
/-- 代表携带的 C∞ 正则性。 -/
theorem contDiff (f : SmoothField) : ContDiff ℝ ∞ (⇑f) := f.property
/-- 光滑代表的连续性，供紧致性和 a.e. 唯一性使用。 -/
theorem continuous (f : SmoothField) : Continuous (f : ℝ × ℝ → ℝ) := f.contDiff.continuous
/-- 光滑代表真实可微；不由名称推断导数。 -/
theorem differentiable (f : SmoothField) : Differentiable ℝ (f : ℝ × ℝ → ℝ) :=
  f.contDiff.differentiable (by simp)

/-- C∞ 的实际 x 导数仍为 C∞；后续导数层需要这一封闭性。 -/
def derivativeX (f : SmoothField) : SmoothField :=
  ⟨dx f, ((contDiff_infty_iff_fderiv.mp f.contDiff).2).clm_apply contDiff_const⟩
/-- C∞ 的实际 y 导数仍为 C∞。 -/
def derivativeY (f : SmoothField) : SmoothField :=
  ⟨dy f, ((contDiff_infty_iff_fderiv.mp f.contDiff).2).clm_apply contDiff_const⟩

@[simp] theorem derivativeX_apply (f : SmoothField) (z : ℝ × ℝ) :
    derivativeX f z = dx f z := rfl
@[simp] theorem derivativeY_apply (f : SmoothField) (z : ℝ × ℝ) :
    derivativeY f z = dy f z := rfl

/-- 将方向 Fréchet 导数绑定到切片 x↦f(x,y) 的真实 HasDerivAt。 -/
theorem hasDerivAt_sliceX (f : SmoothField) (z : ℝ × ℝ) :
    HasDerivAt (fun x => f (x,z.2)) (dx f z) z.1 := by
  have hline : HasDerivAt (fun x : ℝ => (x,z.2)) (1,0) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  exact (f.differentiable z).hasFDerivAt.comp_hasDerivAt z.1 hline

/-- y 切片的真实导数证据。 -/
theorem hasDerivAt_sliceY (f : SmoothField) (z : ℝ × ℝ) :
    HasDerivAt (fun y => f (z.1,y)) (dy f z) z.2 := by
  have hline : HasDerivAt (fun y : ℝ => (z.1,y)) (0,1) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  exact (f.differentiable z).hasFDerivAt.comp_hasDerivAt z.2 hline

/-- 与逐坐标 `deriv` 定义接通，供原八变量方程使用。 -/
theorem dx_eq_deriv (f : SmoothField) (z : ℝ × ℝ) :
    dx f z = deriv (fun x => f (x,z.2)) z.1 := (f.hasDerivAt_sliceX z).deriv.symm
/-- y 坐标的相同连接。 -/
theorem dy_eq_deriv (f : SmoothField) (z : ℝ × ℝ) :
    dy f z = deriv (fun y => f (z.1,y)) z.2 := (f.hasDerivAt_sliceY z).deriv.symm

/-- 实际 L² 成员由闭矩形紧致及连续性证明，未假设函数平方可积。 -/
theorem memLp (D : Rect) (f : SmoothField) : MemLp (f : ℝ × ℝ → ℝ) 2 D.measure :=
  D.memLp_of_continuous f.continuous 2

/-- 原工程 ScalarL2 的具体光滑场表示；整个矩形上的 a.e. 商类。 -/
def toL2 (D : Rect) : SmoothField →ₗ[ℝ] ScalarL2 D.measure where
  toFun f := (f.memLp D).toLp f
  map_add' f g := by
    exact MemLp.toLp_add (f.memLp D) (g.memLp D)
  map_smul' c f := by
    exact MemLp.toLp_const_smul c (f.memLp D)

/-- toL2 选出的代表只在 a.e. 意义等于原光滑函数。 -/
theorem coe_toL2 (D : Rect) (f : SmoothField) :
    (toL2 D f : ℝ × ℝ → ℝ) =ᵐ[D.measure] (f : ℝ × ℝ → ℝ) :=
  (f.memLp D).coeFn_toLp

/-- 同一 L² 类的光滑代表在整个开矩形相等。
关键使用 Lebesgue 测度在非空开集上正，以及代表连续性。 -/
theorem eqOn_open_of_toL2_eq (D : Rect) (f g : SmoothField)
    (hclass : toL2 D f = toL2 D g) : EqOn (⇑f) (⇑g) D.openSet := by
  have hae : (⇑f) =ᵐ[D.measure] (⇑g) :=
    (coe_toL2 D f).symm.trans (hclass ▸ coe_toL2 D g)
  exact Measure.eqOn_open_of_ae_eq hae D.openSet_open
    f.continuous.continuousOn g.continuous.continuousOn

/-- 同一 L² 类的光滑代表在闭矩形相等，因此四边取值可良定义。
这一结论不能推广到任意 L² 代表；连续性与闭包关系均不可省。 -/
theorem eqOn_closed_of_toL2_eq (D : Rect) (f g : SmoothField)
    (hclass : toL2 D f = toL2 D g) : EqOn (⇑f) (⇑g) D.closedSet := by
  rw [← D.closure_openSet]
  exact (eqOn_open_of_toL2_eq D f g hclass).closure f.continuous g.continuous

/-- 开集上的函数相等给出邻域相等，故真实 Fréchet 导数相等。
这一步保证所构造梯度不依赖光滑延拓代表。 -/
theorem fderiv_eq_of_toL2_eq (D : Rect) (f g : SmoothField)
    (hclass : toL2 D f = toL2 D g) (z : ℝ × ℝ) (hz : z ∈ D.openSet) :
    fderiv ℝ (⇑f) z = fderiv ℝ (⇑g) z := by
  have hnear : (⇑f) =ᶠ[𝓝 z] (⇑g) :=
    Filter.mem_of_superset (D.openSet_open.mem_nhds hz)
      (fun z hz => eqOn_open_of_toL2_eq D f g hclass hz)
  exact hnear.fderiv_eq

/-- x 导数的实际 L² 类与代表选择无关。 -/
theorem derivativeX_toL2_eq (D : Rect) (f g : SmoothField)
    (hclass : toL2 D f = toL2 D g) :
    toL2 D (derivativeX f) = toL2 D (derivativeX g) := by
  apply Lp.ext
  filter_upwards [coe_toL2 D (derivativeX f), coe_toL2 D (derivativeX g),
    ae_restrict_mem D.openSet_open.measurableSet] with z hf hg hz
  rw [hf, hg]
  exact congrArg (fun F : (ℝ × ℝ) →L[ℝ] ℝ => F (1,0))
    (fderiv_eq_of_toL2_eq D f g hclass z hz)

/-- y 导数的实际 L² 类与代表选择无关。 -/
theorem derivativeY_toL2_eq (D : Rect) (f g : SmoothField)
    (hclass : toL2 D f = toL2 D g) :
    toL2 D (derivativeY f) = toL2 D (derivativeY g) := by
  apply Lp.ext
  filter_upwards [coe_toL2 D (derivativeY f), coe_toL2 D (derivativeY g),
    ae_restrict_mem D.openSet_open.measurableSet] with z hf hg hz
  rw [hf, hg]
  exact congrArg (fun F : (ℝ × ℝ) →L[ℝ] ℝ => F (0,1))
    (fderiv_eq_of_toL2_eq D f g hclass z hz)

/-- 真实 x 导数在光滑场上是线性算子。不是全部 L² 上的有界梯度。 -/
def derivativeXLinear : SmoothField →ₗ[ℝ] SmoothField where
  toFun := derivativeX
  map_add' f g := by
    apply Subtype.ext
    funext z
    change fderiv ℝ (fun z => f z + g z) z (1,0) = _
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0))
      (fderiv_add (f.differentiable z) (g.differentiable z))
  map_smul' c f := by
    apply Subtype.ext
    funext z
    change fderiv ℝ (fun z => c • f z) z (1,0) = _
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0))
      (fderiv_const_smul (f.differentiable z) c)

/-- y 导数的线性性。 -/
def derivativeYLinear : SmoothField →ₗ[ℝ] SmoothField where
  toFun := derivativeY
  map_add' f g := by
    apply Subtype.ext
    funext z
    change fderiv ℝ (fun z => f z + g z) z (0,1) = _
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1))
      (fderiv_add (f.differentiable z) (g.differentiable z))
  map_smul' c f := by
    apply Subtype.ext
    funext z
    change fderiv ℝ (fun z => c • f z) z (0,1) = _
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1))
      (fderiv_const_smul (f.differentiable z) c)
end SmoothField

/-- 梯度定义域是光滑代表在实际 L² 中的像，不是整个 L²。 -/
def fieldDomain (D : Rect) : Submodule ℝ (ScalarL2 D.measure) :=
  (SmoothField.toL2 D).range

/-- 为域中元素选择光滑延拓；后续所有输出均须另证代表无关。 -/
def representative (D : Rect) (U : fieldDomain D) : SmoothField :=
  Classical.choose U.property

/-- 所选代表确实表示原 L² 类。 -/
theorem representative_toL2 (D : Rect) (U : fieldDomain D) :
    SmoothField.toL2 D (representative D U) = U := Classical.choose_spec U.property

/-- 把已证明代表无关的光滑线性运算降到受限 L² 域。
`hindependent` 是具体使用处必须证明的商兼容，不是空间分析目标的占位。 -/
def descend {W : Type*} [AddCommGroup W] [Module ℝ W]
    (D : Rect) (L : SmoothField →ₗ[ℝ] W)
    (hindependent : ∀ f g, SmoothField.toL2 D f = SmoothField.toL2 D g → L f = L g) :
    fieldDomain D →ₗ[ℝ] W where
  toFun U := L (representative D U)
  map_add' U V := by
    have hclass : SmoothField.toL2 D (representative D (U + V)) =
        SmoothField.toL2 D (representative D U + representative D V) := by
      rw [map_add, representative_toL2, representative_toL2, representative_toL2]
      rfl
    calc
      L (representative D (U + V)) = L (representative D U + representative D V) :=
        hindependent _ _ hclass
      _ = L (representative D U) + L (representative D V) := L.map_add _ _
  map_smul' c U := by
    have hclass : SmoothField.toL2 D (representative D (c • U)) =
        SmoothField.toL2 D (c • representative D U) := by
      rw [map_smul, representative_toL2, representative_toL2]
      rfl
    calc
      L (representative D (c • U)) = L (c • representative D U) :=
        hindependent _ _ hclass
      _ = c • L (representative D U) := L.map_smul c _

/-- 降到商类的运算，对任何原光滑代表均返回同一结果。 -/
theorem descend_toL2 {W : Type*} [AddCommGroup W] [Module ℝ W]
    (D : Rect) (L : SmoothField →ₗ[ℝ] W) (hindependent) (f : SmoothField) :
    descend D L hindependent ⟨SmoothField.toL2 D f, ⟨f,rfl⟩⟩ = L f := by
  apply hindependent
  exact representative_toL2 D _

/-- 具体光滑矩形梯度域填入旧工程接口。
每个分量由真实偏导和已证代表独立性构成，不含任意梯度字段。 -/
def spatialDomain (D : Rect) : ConditionalSpatialDomain D.measure where
  domain := fieldDomain D
  componentX := descend D ((SmoothField.toL2 D).comp SmoothField.derivativeXLinear)
    (SmoothField.derivativeX_toL2_eq D)
  componentY := descend D ((SmoothField.toL2 D).comp SmoothField.derivativeYLinear)
    (SmoothField.derivativeY_toL2_eq D)

/-- 具体 x 梯度与实际光滑偏导的 L² 类一致。 -/
theorem componentX_toL2 (D : Rect) (f : SmoothField) :
    (spatialDomain D).componentX ⟨SmoothField.toL2 D f, ⟨f,rfl⟩⟩ =
      SmoothField.toL2 D f.derivativeX :=
  descend_toL2 D _ (SmoothField.derivativeX_toL2_eq D) f

/-- 具体 y 梯度的相同识别。 -/
theorem componentY_toL2 (D : Rect) (f : SmoothField) :
    (spatialDomain D).componentY ⟨SmoothField.toL2 D f, ⟨f,rfl⟩⟩ =
      SmoothField.toL2 D f.derivativeY :=
  descend_toL2 D _ (SmoothField.derivativeY_toL2_eq D) f

/-- V7 (1.1) 分离吸收的光滑实现入口：p=p(x)、r=r(y)，时间不变。
C∞ 是本轮比 W¹,∞ 更强的正则性；幅度仍仅为非负上界，可在任意区域为零。
输入在全空间给出有界光滑延拓，PDE 本身仍只在矩形内部使用。
零区、单向边层与角层未被排除，也没有吸收梯度小量假设。 -/
def separated_of_smooth (c S : ℝ) (hc_pos : 0 < c) (p r : ℝ → ℝ)
    (hp_smooth : ContDiff ℝ ∞ p) (hr_smooth : ContDiff ℝ ∞ r)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hr_nonneg : ∀ y, 0 ≤ r y)
    (hp_le_S : ∀ x, p x ≤ S) (hr_le_S : ∀ y, r y ≤ S)
    (hS_le : S ≤ c / 4) : SpatialAbsorption (ℝ × ℝ) :=
  SpatialAbsorption.separated c S hc_pos p r hp_smooth.continuous.measurable
    hr_smooth.continuous.measurable hp_nonneg hr_nonneg hp_le_S hr_le_S hS_le

end LeanPML.Rectangle
