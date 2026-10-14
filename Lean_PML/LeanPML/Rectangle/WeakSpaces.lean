import LeanPML.Rectangle.Green
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# v1.0.1：矩形上的真实弱导数图空间

服务于 V7 (6.6) 的弱正则性范围；以下构造由该要求引出，原文未单列。
测试函数是真正 C∞、紧支于整个开矩形 Ω 的函数。弱导数通过所有测试函数的
积分恒等式定义，坐标是普通 L² 商类；没有假设一般 Green、迹或能量结论。

阅读顺序：`TestFunction` → `HasWeakPartial` → `weakH1Graph` → `zeroBoundaryGraph`。
采用三个 L² 的有限乘积图表示；继承的是最大值图范数，不冒称它是欧氏和范数。
H₀¹ 用紧支光滑图的闭包表示；它与未来弱迹核的等价、弱 Green 留到 v1.0.2。
现有光滑 PDE 主定理保持原有强正则性，未因本模块的加入自动变成弱解定理。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open LeanPML.Analysis
namespace LeanPML.Rectangle

/-- 矩形内部的真实测试函数。紧支条件使用拓扑支撑，不允许支撑碰到外边。
对象仍是旧 `SmoothField`，因此偏导来自 fderiv 及已经证明的可微性。 -/
structure TestFunction (D : Rect) where
  field : SmoothField
  compact : HasCompactSupport (⇑field)
  support_inside : tsupport (⇑field) ⊆ D.openSet

/-- 测试函数在 Ω 外为零，由支撑条件推出，不作为额外边界输入。 -/
theorem TestFunction.zero_outside {D : Rect} (φ : TestFunction D)
    {x : ℝ × ℝ} (hx : x ∉ D.openSet) : φ.field x = 0 := by
  by_contra hnonzero
  exact hx (φ.support_inside (subset_closure hnonzero))

/-- 紧支测试函数的四边迹确实为零；供旧光滑 Green 的桥接使用。 -/
theorem TestFunction.zeroBoundary {D : Rect} (φ : TestFunction D) :
    ZeroBoundary D φ.field := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro s hs <;> apply φ.zero_outside
  all_goals simp [Rect.openSet, LeanPML.PML.rectangleDomain]

/-- 选择真实 x/y 偏导；索引 0 是 x，1 是 y。 -/
def smoothPartial (i : Fin 2) (f : SmoothField) : SmoothField :=
  if i = 0 then f.derivativeX else f.derivativeY

/-- 弱偏导的分布定义：∫gφ=−∫f∂ᵢφ，对每个 C_c∞(Ω) 测试成立。
L²×L² 的乘积可积已有 `integrable_product` 保证；内积写法天然与代表元无关。
这不是把待证的一般边界 Green 当作输入：这里只定义内部弱导数。 -/
def HasWeakPartial (D : Rect) (i : Fin 2) (f g : ScalarL2 D.measure) : Prop :=
  ∀ φ : TestFunction D,
    ⟪g, SmoothField.toL2 D φ.field⟫_ℝ =
      -⟪f, SmoothField.toL2 D (smoothPartial i φ.field)⟫_ℝ

/-- H(div) 的内部弱散度定义：∫dφ=−∫X∂xφ−∫Y∂yφ。
没有边界法向迹条件，也没有把通量强行限制为零。 -/
def HasWeakDivergence (D : Rect) (X Y d : ScalarL2 D.measure) : Prop :=
  ∀ φ : TestFunction D,
    ⟪d, SmoothField.toL2 D φ.field⟫_ℝ =
      -⟪X, SmoothField.toL2 D φ.field.derivativeX⟫_ℝ -
        ⟪Y, SmoothField.toL2 D φ.field.derivativeY⟫_ℝ

/-- 所有内部测试配对都为零的 L² 场就是零。
这是 mathlib 的分布基本引理在实际矩形限制测度上的调用；有限测度上的
L²⊂L¹ 提供局部可积性，结论是 a.e. 而非逐点相等。 -/
theorem eq_zero_of_test_inner (D : Rect) (f : ScalarL2 D.measure)
    (htest : ∀ φ : TestFunction D, ⟪f, SmoothField.toL2 D φ.field⟫_ℝ = 0) :
    f = 0 := by
  have hf_integrable : Integrable (⇑f) D.measure :=
    (Lp.memLp f).integrable (by norm_num)
  have hzero := D.openSet_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf_integrable.locallyIntegrable.locallyIntegrableOn D.openSet) (by
      intro g hg_smooth hg_compact hg_inside
      let φ : TestFunction D := ⟨⟨g, hg_smooth⟩, hg_compact, hg_inside⟩
      have hpair := htest φ
      rw [inner_eq_integral] at hpair
      calc
        (∫ x, g x • f x ∂D.measure) =
            ∫ x, f x * (SmoothField.toL2 D φ.field) x ∂D.measure := by
          apply integral_congr_ae
          filter_upwards [SmoothField.coe_toL2 D φ.field] with x hx
          simp only [hx, smul_eq_mul]
          exact mul_comm _ _
        _ = 0 := hpair)
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have hmem : ∀ᵐ x ∂D.measure, x ∈ D.openSet :=
    ae_restrict_mem D.openSet_open.measurableSet
  filter_upwards [hzero, hmem] with x hx hinside
  exact hx hinside

/-- 同一函数的弱偏导在 L² 中唯一。
此结论让后面的梯度算子不依赖图坐标或代表元选择；未假设唯一性。 -/
theorem HasWeakPartial.unique {D : Rect} {i : Fin 2} {f g h : ScalarL2 D.measure}
    (hg : HasWeakPartial D i f g) (hh : HasWeakPartial D i f h) : g = h := by
  apply sub_eq_zero.mp
  apply eq_zero_of_test_inner D (g - h)
  intro φ
  rw [inner_sub_left, hg φ, hh φ, sub_self]

/-- 同一通量的弱散度在 L² 中唯一；允许通量分量本身不在 H¹。 -/
theorem HasWeakDivergence.unique {D : Rect} {X Y d e : ScalarL2 D.measure}
    (hd : HasWeakDivergence D X Y d) (he : HasWeakDivergence D X Y e) : d = e := by
  apply sub_eq_zero.mp
  apply eq_zero_of_test_inner D (d - e)
  intro φ
  rw [inner_sub_left, hd φ, he φ, sub_self]

/-- 旧光滑场的真实散度满足新弱散度定义。
调用已证矩形 Green，并由紧支测试函数的零迹消去四边配对；不接收 hGreen。 -/
theorem hasWeakDivergence_smooth (D : Rect) (X Y : SmoothField) :
    HasWeakDivergence D (SmoothField.toL2 D X) (SmoothField.toL2 D Y)
      (SmoothField.toL2 D X.derivativeX + SmoothField.toL2 D Y.derivativeY) := by
  intro φ
  have hgreen := green_L2 D (fieldOfSmooth D φ.field) (fluxOfSmooth D X Y)
  have htrace : trace D (fieldOfSmooth D φ.field) = 0 := by
    change trace D ⟨SmoothField.toL2 D φ.field, ⟨φ.field, rfl⟩⟩ = 0
    rw [trace_toL2]
    exact (smoothTrace_eq_zero_iff D φ.field).mpr φ.zeroBoundary
  rw [boundary_zero D _ _ htrace] at hgreen
  change ⟪SmoothField.toL2 D φ.field, divergence D (fluxOfSmooth D X Y)⟫_ℝ = _ at hgreen
  rw [divergence_ofSmooth] at hgreen
  change ⟪SmoothField.toL2 D φ.field, _⟫_ℝ =
    -⟪(spatialDomain D).componentX ⟨SmoothField.toL2 D φ.field, ⟨φ.field, rfl⟩⟩,
      SmoothField.toL2 D X⟫_ℝ -
    ⟪(spatialDomain D).componentY ⟨SmoothField.toL2 D φ.field, ⟨φ.field, rfl⟩⟩,
      SmoothField.toL2 D Y⟫_ℝ + 0 at hgreen
  rw [componentX_toL2, componentY_toL2] at hgreen
  simpa only [add_zero, real_inner_comm] using hgreen

/-- 光滑偏导也是弱偏导：分别将另一通量分量设为零。
用于把已验证的光滑状态接入弱图空间，而非只新建一个不相连的空间名。 -/
theorem hasWeakPartial_smooth (D : Rect) (i : Fin 2) (f : SmoothField) :
    HasWeakPartial D i (SmoothField.toL2 D f)
      (SmoothField.toL2 D (smoothPartial i f)) := by
  have hzeroX : (0 : SmoothField).derivativeX = 0 :=
    SmoothField.derivativeXLinear.map_zero
  have hzeroY : (0 : SmoothField).derivativeY = 0 :=
    SmoothField.derivativeYLinear.map_zero
  intro φ
  fin_cases i
  · have hweak := hasWeakDivergence_smooth D f 0 φ
    simpa [smoothPartial, hzeroY] using hweak
  · have hweak := hasWeakDivergence_smooth D 0 f φ
    simpa [smoothPartial, hzeroX] using hweak

/-- H¹ 的实际图：三个 L² 坐标 (u,∂x u,∂y u)，后两个满足内部弱导数定义。
使用有限乘积最大值范数；不是把普通 L² 直接改名为 H¹。 -/
def weakH1Graph (D : Rect) : Submodule ℝ (Fin 3 → ScalarL2 D.measure) where
  carrier := {U | HasWeakPartial D 0 (U 0) (U 1) ∧ HasWeakPartial D 1 (U 0) (U 2)}
  zero_mem' := by constructor <;> intro φ <;> simp
  add_mem' := by
    intro U V hU hV
    constructor
    · intro φ
      simpa only [Pi.add_apply, inner_add_left, neg_add] using congrArg₂ (· + ·) (hU.1 φ) (hV.1 φ)
    · intro φ
      simpa only [Pi.add_apply, inner_add_left, neg_add] using congrArg₂ (· + ·) (hU.2 φ) (hV.2 φ)
  smul_mem' := by
    intro c U hU
    constructor <;> intro φ
    · simpa [inner_smul_left] using congrArg (c * ·) (hU.1 φ)
    · simpa [inner_smul_left] using congrArg (c * ·) (hU.2 φ)

/-- 每个测试配对连续，故弱导数图在三个 L² 的乘积中闭。
这一步使取图范数极限仍保留弱导数，未诉诸尚未证明的边界迹理论。 -/
theorem weakH1Graph_isClosed (D : Rect) :
    IsClosed (weakH1Graph D : Set (Fin 3 → ScalarL2 D.measure)) := by
  have hclosed (i : Fin 2) (j : Fin 3) :
      IsClosed {U : Fin 3 → ScalarL2 D.measure | HasWeakPartial D i (U 0) (U j)} := by
    unfold HasWeakPartial
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro φ
    exact isClosed_eq ((continuous_apply j).inner continuous_const)
      (((continuous_apply 0).inner continuous_const).neg)
  exact (hclosed 0 1).inter (hclosed 1 2)

instance weakH1Graph_completeSpace (D : Rect) : CompleteSpace (weakH1Graph D) :=
  (weakH1Graph_isClosed D).completeSpace_coe

/-- H(div) 的实际图：(Λx,Λy,div Λ)，弱散度为第三个 L² 坐标。
只要求散度在 L²，不要求两个分量各自都具有全部一阶 L² 偏导。 -/
def weakHDivGraph (D : Rect) : Submodule ℝ (Fin 3 → ScalarL2 D.measure) where
  carrier := {U | HasWeakDivergence D (U 0) (U 1) (U 2)}
  zero_mem' := by intro φ; simp
  add_mem' := by
    intro U V hU hV φ
    simp only [Pi.add_apply, inner_add_left]
    rw [hU φ, hV φ]
    ring
  smul_mem' := by
    intro c U hU φ
    simp only [Pi.smul_apply, real_inner_smul_left]
    rw [hU φ]
    ring

/-- 弱散度图闭；连续的是测试配对，不是整个 L² 上的散度算子。 -/
theorem weakHDivGraph_isClosed (D : Rect) :
    IsClosed (weakHDivGraph D : Set (Fin 3 → ScalarL2 D.measure)) := by
  change IsClosed {U | ∀ φ : TestFunction D, _ = _}
  rw [Set.setOf_forall]
  apply isClosed_iInter
  intro φ
  exact isClosed_eq ((continuous_apply 2).inner continuous_const)
    ((((continuous_apply 0).inner continuous_const).neg).sub
      ((continuous_apply 1).inner continuous_const))

instance weakHDivGraph_completeSpace (D : Rect) : CompleteSpace (weakHDivGraph D) :=
  (weakHDivGraph_isClosed D).completeSpace_coe

/-- 旧光滑函数的图进入实际弱 H¹ 图；三个分量都是既有 toL2。 -/
def smoothToWeakH1 (D : Rect) (f : SmoothField) : weakH1Graph D :=
  ⟨![SmoothField.toL2 D f, SmoothField.toL2 D f.derivativeX,
    SmoothField.toL2 D f.derivativeY],
    ⟨hasWeakPartial_smooth D 0 f, hasWeakPartial_smooth D 1 f⟩⟩

/-- 旧光滑通量进入弱 H(div) 图，第三槽由已证明的真实散度识别填入。 -/
def smoothToWeakHDiv (D : Rect) (X Y : SmoothField) : weakHDivGraph D :=
  ⟨![SmoothField.toL2 D X, SmoothField.toL2 D Y,
    SmoothField.toL2 D X.derivativeX + SmoothField.toL2 D Y.derivativeY],
    hasWeakDivergence_smooth D X Y⟩

/-- H₀¹ 的闭包定义：在上述完整弱 H¹ 图范数中取 C_c∞(Ω) 图的线性张成闭包。
有限乘积最大值范数控制三个 L² 坐标。此处不从 L² 等价类读取边界点值；
与弱迹核的等价及任意光滑零边界场的稠密逼近仍是后续接口。 -/
def zeroBoundaryGraph (D : Rect) : Submodule ℝ (weakH1Graph D) :=
  (Submodule.span ℝ (Set.range (fun φ : TestFunction D => smoothToWeakH1 D φ.field))).topologicalClosure

/-- 定义中的闭包确为完备空间；不需要假设 Green 或 Poincaré。 -/
instance zeroBoundaryGraph_completeSpace (D : Rect) : CompleteSpace (zeroBoundaryGraph D) :=
  inferInstanceAs (CompleteSpace
    (Submodule.span ℝ (Set.range (fun φ : TestFunction D => smoothToWeakH1 D φ.field))).topologicalClosure)

/-- 每个内部紧支光滑测试函数确实进入 H₀¹ 闭包表示。 -/
theorem test_mem_zeroBoundaryGraph (D : Rect) (φ : TestFunction D) :
    smoothToWeakH1 D φ.field ∈ zeroBoundaryGraph D :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, rfl⟩)

/-- 弱 H¹ 图到普通 L² 的函数坐标。它在图范数中连续；
梯度只在其像定义域上构造，不宣称普通 L² 上存在有界微分算子。 -/
def weakValue (D : Rect) : weakH1Graph D →ₗ[ℝ] ScalarL2 D.measure :=
  (LinearMap.proj 0).comp (weakH1Graph D).subtype

/-- 函数坐标唯一确定两个弱偏导，因此图表示没有额外自由导数。
这是由测试函数基本引理推出的数学事实，不是图定义中的唯一性字段。 -/
theorem weakValue_injective (D : Rect) : Function.Injective (weakValue D) := by
  intro U V hvalue
  have hbase : U.val 0 = V.val 0 := hvalue
  have hdx : U.val 1 = V.val 1 := by
    apply HasWeakPartial.unique U.property.1
    rw [hbase]
    exact V.property.1
  have hdy : U.val 2 = V.val 2 := by
    apply HasWeakPartial.unique U.property.2
    rw [hbase]
    exact V.property.2
  apply Subtype.ext
  funext i
  fin_cases i
  · exact hbase
  · exact hdx
  · exact hdy

/-- 弱 H¹ 的普通 L² 定义域：存在两个实际 L² 弱偏导。
不是光滑函数像；一般元素无需点值、经典可微性或边界迹。 -/
def weakFieldDomain (D : Rect) : Submodule ℝ (ScalarL2 D.measure) :=
  (weakValue D).range

/-- 旧光滑 L² 定义域包含于新弱 H¹ 定义域。
输入只需旧域成员；偏导成员与弱导数关系由光滑桥接定理填入。 -/
theorem smoothFieldDomain_le_weak (D : Rect) : fieldDomain D ≤ weakFieldDomain D := by
  rintro f ⟨g, rfl⟩
  exact ⟨smoothToWeakH1 D g, rfl⟩

/-- 唯一弱导数图的线性恢复。`ofInjective` 使用上条已证唯一性，
所以后面梯度分量不会依赖存在证据的选择。 -/
def weakLift (D : Rect) : weakFieldDomain D →ₗ[ℝ] weakH1Graph D :=
  (LinearEquiv.ofInjective (weakValue D) (weakValue_injective D)).symm.toLinearMap

/-- 实际弱梯度填入旧空间接口。字段只有定义域和两个线性偏导，
没有输入或伪造 Green、Poincaré、边界迹及能量律。 -/
def weakSpatialDomain (D : Rect) : LeanPML.PML.ConditionalSpatialDomain D.measure where
  domain := weakFieldDomain D
  componentX := ((LinearMap.proj 1).comp (weakH1Graph D).subtype).comp (weakLift D)
  componentY := ((LinearMap.proj 2).comp (weakH1Graph D).subtype).comp (weakLift D)

/-- 光滑图的第零坐标就是旧 toL2；作为具名等式避免隐藏的坐标化简。 -/
theorem weakValue_smooth (D : Rect) (f : SmoothField) :
    weakValue D (smoothToWeakH1 D f) = SmoothField.toL2 D f := rfl

/-- 光滑图恢复后仍是原图，供两个实际偏导连接使用。 -/
theorem weakLift_smooth (D : Rect) (f : SmoothField) :
    weakLift D ⟨SmoothField.toL2 D f, ⟨smoothToWeakH1 D f, weakValue_smooth D f⟩⟩ =
      smoothToWeakH1 D f :=
by
  let e := LinearEquiv.ofInjective (weakValue D) (weakValue_injective D)
  have hidentify : (⟨SmoothField.toL2 D f,
      ⟨smoothToWeakH1 D f, weakValue_smooth D f⟩⟩ : weakFieldDomain D) =
      e (smoothToWeakH1 D f) := by
    apply Subtype.ext
    exact (weakValue_smooth D f).symm
  change e.symm _ = _
  rw [hidentify]
  exact e.symm_apply_apply _

/-- 旧光滑对象的新弱梯度恰好是旧真实偏导的 L² 表示。
此桥接保留 v0.5 的含义，没有把其时间/PDE 正则性假设删去。 -/
theorem weakSpatialDomain_smooth (D : Rect) (f : SmoothField) :
    (weakSpatialDomain D).componentX
        ⟨SmoothField.toL2 D f, ⟨smoothToWeakH1 D f, weakValue_smooth D f⟩⟩ =
      SmoothField.toL2 D f.derivativeX ∧
    (weakSpatialDomain D).componentY
        ⟨SmoothField.toL2 D f, ⟨smoothToWeakH1 D f, weakValue_smooth D f⟩⟩ =
      SmoothField.toL2 D f.derivativeY := by
  have hlift := weakLift_smooth D f
  exact ⟨congrArg (fun U : weakH1Graph D => U.val 1) hlift,
    congrArg (fun U : weakH1Graph D => U.val 2) hlift⟩

/-- 弱 H(div) 图由通量两个分量唯一决定；第三个散度坐标不自由。
法向弱迹的建设不包含在此唯一性结论中。 -/
theorem weakFlux_injective (D : Rect) :
    Function.Injective (fun U : weakHDivGraph D => (U.val 0, U.val 1)) := by
  intro U V hflux
  have hx : U.val 0 = V.val 0 := congrArg Prod.fst hflux
  have hy : U.val 1 = V.val 1 := congrArg Prod.snd hflux
  have hd : U.val 2 = V.val 2 := by
    apply HasWeakDivergence.unique U.property
    rw [hx, hy]
    exact V.property
  apply Subtype.ext
  funext i
  fin_cases i
  · exact hx
  · exact hy
  · exact hd

/-- 图范数直接控制每个 L² 坐标；明确其为最大值乘积范数，
不错误套用普通乘积范数平方等于欧氏分量平方和。 -/
theorem weakH1_coordinate_norm_le (D : Rect) (U : weakH1Graph D) (i : Fin 3) :
    ‖U.val i‖ ≤ ‖U‖ := norm_le_pi_norm U.val i

/-- 同一结论用于通量及弱散度。 -/
theorem weakHDiv_coordinate_norm_le (D : Rect) (U : weakHDivGraph D) (i : Fin 3) :
    ‖U.val i‖ ≤ ‖U‖ := norm_le_pi_norm U.val i

/-- 弱散度的普通 L² 通量投影；两个分量仍独立，不附加磁约束。 -/
def weakFlux (D : Rect) : weakHDivGraph D →ₗ[ℝ]
    (ScalarL2 D.measure × ScalarL2 D.measure) :=
  ((LinearMap.proj 0).comp (weakHDivGraph D).subtype).prod
    ((LinearMap.proj 1).comp (weakHDivGraph D).subtype)

/-- H(div) 作为普通向量 L² 的受限定义域；要求存在 L² 弱散度。 -/
def weakFluxDomain (D : Rect) : Submodule ℝ
    (ScalarL2 D.measure × ScalarL2 D.measure) := (weakFlux D).range

/-- 唯一弱散度作为域上的线性算子。其定义没有要求全部普通 L² 通量可微，
也没有要求任意分量处于 H¹。后续弱 Green 将使用此域，而非假设 Green 字段。 -/
def weakDivergence (D : Rect) : weakFluxDomain D →ₗ[ℝ] ScalarL2 D.measure :=
  ((LinearMap.proj 2).comp (weakHDivGraph D).subtype).comp
    (LinearEquiv.ofInjective (weakFlux D) (weakFlux_injective D)).symm.toLinearMap

/-- 恢复出的散度确实满足测试函数定义；选择无关来自已证唯一性。 -/
theorem weakDivergence_spec (D : Rect) (L : weakFluxDomain D) :
    HasWeakDivergence D L.val.1 L.val.2 (weakDivergence D L) := by
  let e := LinearEquiv.ofInjective (weakFlux D) (weakFlux_injective D)
  let U := e.symm L
  have hflux : weakFlux D U = L.val :=
    congrArg Subtype.val (e.apply_symm_apply L)
  have hx : U.val 0 = L.val.1 := congrArg Prod.fst hflux
  have hy : U.val 1 = L.val.2 := congrArg Prod.snd hflux
  change HasWeakDivergence D L.val.1 L.val.2 (U.val 2)
  rw [← hx, ← hy]
  exact U.property

/-- H₀¹ 闭包通过函数坐标进入实际 L²；它是 H¹ 定义域的子空间。
这里的零边界含义是图范数闭包，不是读取 L² 代表元的边界值。 -/
def weakZeroFieldDomain (D : Rect) : Submodule ℝ (ScalarL2 D.measure) :=
  ((weakValue D).comp (zeroBoundaryGraph D).subtype).range

/-- H₀¹ 的每个元素有两个 L² 弱导数；由闭包已在闭弱导数图内构造而得。 -/
theorem weakZeroFieldDomain_le (D : Rect) : weakZeroFieldDomain D ≤ weakFieldDomain D := by
  rintro f ⟨U, rfl⟩
  exact ⟨U.val, rfl⟩

/-- 将 H₀¹ 的真实弱梯度填入既有定义域接口；不附带弱迹、Green 或能量字段。 -/
def weakZeroSpatialDomain (D : Rect) : LeanPML.PML.ConditionalSpatialDomain D.measure where
  domain := weakZeroFieldDomain D
  componentX := (weakSpatialDomain D).componentX.comp
    (Submodule.inclusion (weakZeroFieldDomain_le D))
  componentY := (weakSpatialDomain D).componentY.comp
    (Submodule.inclusion (weakZeroFieldDomain_le D))

/-- 有限乘积最大值图范数与通常平方和的明确双边界。
因此本文件的闭包拓扑等价于标准 H¹/H(div) 的图拓扑；
并未给最大值范数错误地安装 Hilbert 内积实例。 -/
theorem graph_norm_sq_equivalence (D : Rect) (U : Fin 3 → ScalarL2 D.measure) :
    ‖U‖^2 ≤ ‖U 0‖^2 + ‖U 1‖^2 + ‖U 2‖^2 ∧
    ‖U 0‖^2 + ‖U 1‖^2 + ‖U 2‖^2 ≤ 3 * ‖U‖^2 := by
  let q := ‖U 0‖^2 + ‖U 1‖^2 + ‖U 2‖^2
  have hq_nonneg : 0 ≤ q := by dsimp [q]; positivity
  have hcoordinate (i : Fin 3) : ‖U i‖^2 ≤ q := by
    fin_cases i <;> dsimp [q] <;> nlinarith [sq_nonneg ‖U 0‖,
      sq_nonneg ‖U 1‖, sq_nonneg ‖U 2‖]
  have hnorm_le : ‖U‖ ≤ Real.sqrt q := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg q)).mpr
    intro i
    exact (Real.le_sqrt (norm_nonneg _) hq_nonneg).mpr (hcoordinate i)
  have hnorm_sq : ‖U‖^2 ≤ q := by
    nlinarith [Real.sq_sqrt hq_nonneg, norm_nonneg U, Real.sqrt_nonneg q]
  have hupper (i : Fin 3) : ‖U i‖^2 ≤ ‖U‖^2 := by
    have hle := norm_le_pi_norm U i
    nlinarith [norm_nonneg (U i), norm_nonneg U]
  exact ⟨hnorm_sq, by linarith [hupper 0, hupper 1, hupper 2]⟩

end LeanPML.Rectangle
