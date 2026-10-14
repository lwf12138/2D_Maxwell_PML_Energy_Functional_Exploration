import LeanPML.Rectangle.WeakPoincare
import LeanPML.Rectangle.WeakPaths

/-!
# 区域 W¹,∞ 系数与 H₀¹ 的弱乘积法则

服务于 V7 §1 的 W¹,∞ 系数及 §5.3 的提升约束（原文未单列本乘积引理）。
系数及其两个弱导数只在实际矩形上有界；域外置零仅用于 L² 乘子，
不声称零延拓跨边界仍有同一个弱导数。弱导数由内部测试配对定义。
本文件不假设 Green、提升唯一性或能量结论，也不对无界权重求空间导数。
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace Topology ContDiff
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

/-- 区域有界可测函数。幅度限制仅在 Ω；域外取值不参与任何物理假设。 -/
structure RegionalBounded (D : Rect) where
  value : ℝ × ℝ → ℝ
  measurable : Measurable value
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bound_on : ∀ x ∈ D.openSet, |value x| ≤ bound

namespace RegionalBounded
variable {D : Rect}

/-- 内部实现所用的零延拓；只有普通 L² 乘法用途，不宣称全轴弱正则性。 -/
def extended (m : RegionalBounded D) : ℝ × ℝ → ℝ := D.openSet.indicator m.value

theorem extended_measurable (m : RegionalBounded D) : Measurable m.extended :=
  m.measurable.indicator D.openSet_open.measurableSet

theorem extended_bound (m : RegionalBounded D) (x : ℝ × ℝ) :
    |m.extended x| ≤ m.bound := by
  by_cases hx : x ∈ D.openSet
  · simpa [extended, hx] using m.bound_on x hx
  · simpa [extended, hx] using m.bound_nonneg

/-- 整个矩形测度下零延拓与原函数 a.e. 相等；没有缩小积分域。 -/
theorem extended_ae (m : RegionalBounded D) : m.extended =ᵐ[D.measure] m.value := by
  filter_upwards [ae_restrict_mem D.openSet_open.measurableSet] with x hx
  exact indicator_of_mem hx _

/-- 实际有界 L² 乘子；不能把该构造用于可能无界的能量权重。 -/
def operator (m : RegionalBounded D) : ScalarL2 D.measure →L[ℝ] ScalarL2 D.measure :=
  boundedMul D.measure m.extended m.extended_measurable m.bound m.extended_bound

theorem operator_ae (m : RegionalBounded D) (f : ScalarL2 D.measure) :
    ⇑(m.operator f) =ᵐ[D.measure] fun x => m.value x * f x := by
  filter_upwards [coeFn_boundedMul D.measure m.extended m.extended_measurable
    m.bound m.extended_bound f, m.extended_ae] with x hx hm
  simpa [operator, hm] using hx

/-- 区域有界函数本身属于真实 L²；有限矩形测度用于常数函数的成员资格。 -/
def toL2 (m : RegionalBounded D) : ScalarL2 D.measure :=
  m.operator (SmoothField.toL2 D ⟨fun _ => 1, by change ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℝ)); exact contDiff_const⟩)

theorem coe_toL2 (m : RegionalBounded D) : ⇑m.toL2 =ᵐ[D.measure] m.value := by
  filter_upwards [m.operator_ae (SmoothField.toL2 D ⟨fun _ => 1, by change ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℝ)); exact contDiff_const⟩),
    SmoothField.coe_toL2 D ⟨fun _ => 1, by change ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℝ)); exact contDiff_const⟩] with x hx hone
  simpa only [toL2, hone, mul_one] using hx
end RegionalBounded

/-- 实际区域 W¹,∞ 的具体表示：函数及两弱偏导均区域本质有界。
这里选取逐点有界的可测代表；弱导数等式仍在 L² 商类意义成立。
没有 C∞、经典导数、Green 或待证乘积法则字段。 -/
structure RegionalWeakCoefficient (D : Rect) where
  value : RegionalBounded D
  derivative : Fin 2 → RegionalBounded D
  weak_partial : ∀ i, HasWeakPartial D i value.toL2 (derivative i).toL2

/-- 两个实际光滑函数的乘积，用于构造弱导数定义允许的测试函数。 -/
def smoothProduct (f g : SmoothField) : SmoothField :=
  ⟨fun x => f x * g x, f.contDiff.mul g.contDiff⟩

/-- 内部紧支光滑函数乘另一个光滑函数，仍是合法测试函数。 -/
def testProduct {D : Rect} (f g : TestFunction D) : TestFunction D where
  field := smoothProduct f.field g.field
  compact := f.compact.mul_right
  support_inside := tsupport_mul_subset_left.trans f.support_inside

/-- 乘积的真实偏导；HasDerivAt 的乘法规则用于坐标切片，未将偏导当代数槽。 -/
theorem smoothPartial_product (i : Fin 2) (f g : SmoothField) (x : ℝ × ℝ) :
    smoothPartial i (smoothProduct f g) x =
      smoothPartial i f x * g x + f x * smoothPartial i g x := by
  fin_cases i
  · have hproduct := (f.hasDerivAt_sliceX x).mul (g.hasDerivAt_sliceX x)
    have hactual := (smoothProduct f g).hasDerivAt_sliceX x
    exact hactual.unique hproduct
  · have hproduct := (f.hasDerivAt_sliceY x).mul (g.hasDerivAt_sliceY x)
    have hactual := (smoothProduct f g).hasDerivAt_sliceY x
    exact hactual.unique hproduct

/-- 把区域系数乘子的配对移到系数本身；a.e. 改写保证代表选择无关。 -/
theorem inner_regional_smooth (D : Rect) (m : RegionalBounded D) (f g : SmoothField) :
    ⟪m.operator (SmoothField.toL2 D f), SmoothField.toL2 D g⟫_ℝ =
      ⟪m.toL2, SmoothField.toL2 D (smoothProduct f g)⟫_ℝ := by
  rw [inner_eq_integral, inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [m.operator_ae (SmoothField.toL2 D f), m.coe_toL2,
    SmoothField.coe_toL2 D f, SmoothField.coe_toL2 D g,
    SmoothField.coe_toL2 D (smoothProduct f g)] with x hm hc hf hg hfg
  rw [hm, hc, hf, hg, hfg]
  change m.value x * f x * g x = m.value x * (f x * g x)
  ring

/-- W¹,∞ 系数乘内部紧支光滑函数的真实弱乘积法则。
在测试 fφ 中调用系数的弱导数定义；不是假设对所有 H¹ 函数的乘积法则。
后续图闭包推广只需这里的测试函数版本和乘子的连续性。 -/
theorem weak_product_test (D : Rect) (m : RegionalWeakCoefficient D)
    (f : TestFunction D) (i : Fin 2) :
    HasWeakPartial D i (m.value.operator (SmoothField.toL2 D f.field))
      ((m.derivative i).operator (SmoothField.toL2 D f.field) +
        m.value.operator (SmoothField.toL2 D (smoothPartial i f.field))) := by
  intro φ
  have hweak := m.weak_partial i (testProduct f φ)
  have hderiv_split :
      ⟪m.value.toL2, SmoothField.toL2 D (smoothPartial i (testProduct f φ).field)⟫_ℝ =
      ⟪m.value.toL2, SmoothField.toL2 D
        (smoothProduct (smoothPartial i f.field) φ.field)⟫_ℝ +
      ⟪m.value.toL2, SmoothField.toL2 D
        (smoothProduct f.field (smoothPartial i φ.field))⟫_ℝ := by
    rw [← inner_add_right, ← map_add]
    congr 2
    apply Subtype.ext
    funext x
    exact smoothPartial_product i f.field φ.field x
  rw [hderiv_split] at hweak
  rw [inner_add_left, inner_regional_smooth, inner_regional_smooth,
    inner_regional_smooth]
  change ⟪(m.derivative i).toL2, SmoothField.toL2 D (testProduct f φ).field⟫_ℝ = _ at hweak
  dsimp only [testProduct] at hweak
  linarith


/-- 候选乘积图是连续线性映射：三坐标分别为 mu、(∂x m)u+m∂x u、
(∂y m)u+m∂y u。此处只建立图坐标，真实弱导数将在下一定理证明。 -/
def weakCoefficientGraphMap (D : Rect) (m : RegionalWeakCoefficient D) :
    weakH1Graph D →L[ℝ] (Fin 3 → ScalarL2 D.measure) :=
  ContinuousLinearMap.pi fun j =>
    if j = 0 then m.value.operator.comp (weakH1Coordinate D 0)
    else if j = 1 then
      (m.derivative 0).operator.comp (weakH1Coordinate D 0) +
        m.value.operator.comp (weakH1Coordinate D 1)
    else
      (m.derivative 1).operator.comp (weakH1Coordinate D 0) +
        m.value.operator.comp (weakH1Coordinate D 2)

/-- 区域 W¹,∞ 系数乘 H₀¹ 函数属于 H¹，并满足真实弱乘积法则。
证明先在紧支光滑测试图上用上一引理，再以图范数连续性推广到定义中的闭包。
没有输入逼近序列或目标乘积关系；闭包只用于原空间自身的定义。 -/
theorem weakCoefficientGraphMap_mem (D : Rect) (m : RegionalWeakCoefficient D)
    (u : zeroBoundaryGraph D) : weakCoefficientGraphMap D m u.val ∈ weakH1Graph D := by
  let target : Submodule ℝ (weakH1Graph D) :=
    (weakH1Graph D).comap (weakCoefficientGraphMap D m).toLinearMap
  have htest : ∀ f : TestFunction D, smoothToWeakH1 D f.field ∈ target := by
    intro f
    change HasWeakPartial D 0 _ _ ∧ HasWeakPartial D 1 _ _
    constructor
    · simpa [weakCoefficientGraphMap, weakH1Coordinate, smoothToWeakH1, smoothPartial]
        using weak_product_test D m f 0
    · simpa [weakCoefficientGraphMap, weakH1Coordinate, smoothToWeakH1, smoothPartial]
        using weak_product_test D m f 1
  have hspan : Submodule.span ℝ (Set.range fun f : TestFunction D =>
      smoothToWeakH1 D f.field) ≤ target := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact htest f
  have hclosed : IsClosed (target : Set (weakH1Graph D)) :=
    (weakH1Graph_isClosed D).preimage (weakCoefficientGraphMap D m).continuous
  exact Submodule.topologicalClosure_minimal _ hspan hclosed u.property

/-- 实际调用上一定理构造新的弱 H¹ 场；值与两个偏导都保存在同一图对象中。
输出暂为 H¹；没有把 H₀¹ 成员保持或提升规范唯一性混入已证范围。 -/
def weakCoefficientMul (D : Rect) (m : RegionalWeakCoefficient D)
    (u : zeroBoundaryGraph D) : weakH1Graph D :=
  ⟨weakCoefficientGraphMap D m u.val, weakCoefficientGraphMap_mem D m u⟩


/-- 旧光滑函数给出区域有界系数；紧致矩形提供幅度界，域外无需有界。
这只是进入新弱空间的一个桥接，不是新 W¹,∞ 类型的必需光滑假设。 -/
def regionalBoundedOfSmooth (D : Rect) (f : SmoothField) : RegionalBounded D := by
  let hexists := (D.closedSet_compact.image f.continuous).isBounded.exists_norm_le
  let B := Classical.choose hexists
  have hB := Classical.choose_spec hexists
  exact ⟨f, f.continuous.measurable, max B 0, le_max_right _ _, fun x hx => by
    have hclosed : x ∈ D.closedSet := by
      rw [← D.closure_openSet]
      exact subset_closure hx
    exact (hB (f x) (mem_image_of_mem f hclosed)).trans (le_max_left _ _)⟩

/-- 上述区域代表转成 L² 后等于旧光滑 toL2；后续实际调用弱乘积法则。 -/
theorem regionalBoundedOfSmooth_toL2 (D : Rect) (f : SmoothField) :
    (regionalBoundedOfSmooth D f).toL2 = SmoothField.toL2 D f := by
  apply Lp.ext
  filter_upwards [(regionalBoundedOfSmooth D f).coe_toL2, SmoothField.coe_toL2 D f]
    with x hx hf
  rw [hx, hf]
  rfl

/-- 旧光滑对象确实进入新区域 W¹,∞ 表示，两个弱导数证据由旧已证桥接填入。
新空间本身不依赖此构造；它仍接受非经典可导而满足测试函数关系的系数。 -/
def weakCoefficientOfSmooth (D : Rect) (f : SmoothField) : RegionalWeakCoefficient D where
  value := regionalBoundedOfSmooth D f
  derivative i := regionalBoundedOfSmooth D (smoothPartial i f)
  weak_partial i := by
    rw [regionalBoundedOfSmooth_toL2, regionalBoundedOfSmooth_toL2]
    exact hasWeakPartial_smooth D i f

/-- 新乘积空间的实际调用：任意旧光滑系数乘任意 H₀¹ 商类都有真实 H¹ 图。
输入只有系数、H₀¹ 成员；输出弱导数由 weakCoefficientGraphMap_mem 推出。 -/
def smoothCoefficientMulWeak (D : Rect) (f : SmoothField)
    (u : zeroBoundaryGraph D) : weakH1Graph D :=
  weakCoefficientMul D (weakCoefficientOfSmooth D f) u


/-- 乘积图的函数分量确为实际 L² 乘法；用于连接原模型的 bg 等约束。 -/
theorem weakCoefficientMul_value (D : Rect) (m : RegionalWeakCoefficient D)
    (u : zeroBoundaryGraph D) :
    (weakCoefficientMul D m u).val 0 = m.value.operator (u.val.val 0) := by
  simp [weakCoefficientMul, weakCoefficientGraphMap, weakH1Coordinate]

/-- 乘积图包含已经证明的两条 Leibniz 公式，按 L² 等价类相等而非逐点读取。 -/
theorem weakCoefficientMul_derivatives (D : Rect) (m : RegionalWeakCoefficient D)
    (u : zeroBoundaryGraph D) :
    (weakCoefficientMul D m u).val 1 =
      (m.derivative 0).operator (u.val.val 0) + m.value.operator (u.val.val 1) ∧
    (weakCoefficientMul D m u).val 2 =
      (m.derivative 1).operator (u.val.val 0) + m.value.operator (u.val.val 2) := by
  simp [weakCoefficientMul, weakCoefficientGraphMap, weakH1Coordinate]

/-- 常数 1 的光滑代表，供非零调用回归使用。 -/
def weakCoefficientOne : SmoothField :=
  ⟨fun _ => 1, by change ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℝ)); exact contDiff_const⟩

/-- 乘常数 1 后函数分量保留；这条结论调用新弱乘积构造。 -/
theorem weakCoefficient_one_value (D : Rect) (u : zeroBoundaryGraph D) :
    (weakCoefficientMul D (weakCoefficientOfSmooth D weakCoefficientOne) u).val 0 =
      u.val.val 0 := by
  rw [weakCoefficientMul_value]
  apply Lp.ext
  filter_upwards [(regionalBoundedOfSmooth D weakCoefficientOne).operator_ae (u.val.val 0)]
    with x hx
  simpa [weakCoefficientOfSmooth, regionalBoundedOfSmooth, weakCoefficientOne] using hx


/-- 上述弱乘积是真实图空间之间的有界线性映射。
闭包推广得到的弱导数证据填入 codRestrict，不作为额外输入。
下游可以在 H¹ 图范数中使用它，不能据此断言输出属于 H₀¹。 -/
def weakCoefficientMulCLM (D : Rect) (m : RegionalWeakCoefficient D) :
    zeroBoundaryGraph D →L[ℝ] weakH1Graph D :=
  ((weakCoefficientGraphMap D m).comp (zeroBoundaryGraph D).subtypeL).codRestrict
    (weakH1Graph D) (fun u => weakCoefficientGraphMap_mem D m u)

/-- 时间不变的区域 W¹,∞ 系数可与真实 H₀¹ 图路径的时间求导交换。
这是乘子连续性推出的结论；输入是真正图范数导数，未以逐点导数替代。 -/
theorem hasDerivAt_weakCoefficientMul (D : Rect) (m : RegionalWeakCoefficient D)
    {u : ℝ → zeroBoundaryGraph D} {udot : zeroBoundaryGraph D} {t : ℝ}
    (hpath : HasDerivAt u udot t) :
    HasDerivAt (fun s => weakCoefficientMul D m (u s))
      (weakCoefficientMul D m udot) t := by
  have hactual : HasDerivAt (fun s => weakCoefficientMulCLM D m (u s))
      (weakCoefficientMulCLM D m udot) t :=
    HasFDerivAt.comp_hasDerivAt (F := zeroBoundaryGraph D) (E := weakH1Graph D) t
      (@ContinuousLinearMap.hasFDerivAt ℝ _ (zeroBoundaryGraph D) _ _ _
        (weakH1Graph D) _ _ _ (weakCoefficientMulCLM D m) (u t)) hpath
  convert hactual using 1
  · funext s
    apply Subtype.ext
    rfl
  · apply Subtype.ext
    rfl

end LeanPML.PML
