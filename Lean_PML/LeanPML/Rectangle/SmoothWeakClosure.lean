import LeanPML.Rectangle.WeakSpaces
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# M1：零迹光滑场的边界截断估计

为 V7 (6.6) 的 H₀¹ 图闭包连接提供实际逼近工具；原文未单列这些引理。
本文件使用真实坐标导数，先由零边界和中值定理控制 f 到四边的距离。
这使截断导数的 1/δ 因子能由 f 的 O(δ) 衰减抵消。
然后分别对函数和两个偏导调用平方差支配收敛，得到 H¹ 图范数逼近与闭包成员。
阅读顺序：norm_le_four_distances → cutoffSequence_toL2_convergence →
smoothToWeakH1_mem_zeroBoundaryGraph。没有假定 Green、Poincaré 或所需逼近序列。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace LeanPML.Rectangle

/-- 闭矩形紧致且两个真实偏导连续，故存在共同的非负上界。
该上界是推出的结论，不是额外的零迹或 H₀¹ 假设。 -/
theorem SmoothField.exists_partial_bound (D : Rect) (f : SmoothField) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ D.closedSet,
      ‖dx f z‖ ≤ M ∧ ‖dy f z‖ ≤ M := by
  obtain ⟨Mx, hMx⟩ := D.closedSet_compact.exists_bound_of_continuousOn
    f.derivativeX.continuous.continuousOn
  obtain ⟨My, hMy⟩ := D.closedSet_compact.exists_bound_of_continuousOn
    f.derivativeY.continuous.continuousOn
  refine ⟨max 0 (max Mx My), le_max_left _ _, ?_⟩
  intro z hz
  exact ⟨(hMx z hz).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hMy z hz).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- 零迹函数在任意内部点的绝对值受“距四边的距离 × 偏导上界”控制。
输入 hbound 由 `exists_partial_bound` 提供；四次中值定理均使用实际 HasDerivAt。
下游截断误差估计使用距离小于 2δ 的那一边。 -/
theorem ZeroBoundary.norm_le_four_distances (D : Rect) (f : SmoothField)
    (hzero : ZeroBoundary D f) {M : ℝ}
    (hbound : ∀ z ∈ D.closedSet, ‖dx f z‖ ≤ M ∧ ‖dy f z‖ ≤ M)
    {z : ℝ × ℝ} (hz : z ∈ D.closedSet) :
    ‖f z‖ ≤ M * (z.1 - D.xlo) ∧
    ‖f z‖ ≤ M * (D.xhi - z.1) ∧
    ‖f z‖ ≤ M * (z.2 - D.ylo) ∧
    ‖f z‖ ≤ M * (D.yhi - z.2) := by
  have hx : z.1 ∈ Icc D.xlo D.xhi := hz.1
  have hy : z.2 ∈ Icc D.ylo D.yhi := hz.2
  have hderivX : ∀ x ∈ Icc D.xlo D.xhi,
      HasDerivWithinAt (fun x => f (x,z.2)) (dx f (x,z.2)) (Icc D.xlo D.xhi) x :=
    fun x _ => (f.hasDerivAt_sliceX (x,z.2)).hasDerivWithinAt
  have hderivY : ∀ y ∈ Icc D.ylo D.yhi,
      HasDerivWithinAt (fun y => f (z.1,y)) (dy f (z.1,y)) (Icc D.ylo D.yhi) y :=
    fun y _ => (f.hasDerivAt_sliceY (z.1,y)).hasDerivWithinAt
  have hboundX : ∀ x ∈ Icc D.xlo D.xhi, ‖dx f (x,z.2)‖ ≤ M :=
    fun x hx => (hbound (x,z.2) ⟨hx,hy⟩).1
  have hboundY : ∀ y ∈ Icc D.ylo D.yhi, ‖dy f (z.1,y)‖ ≤ M :=
    fun y hy => (hbound (z.1,y) ⟨hx,hy⟩).2
  have hleft := (convex_Icc D.xlo D.xhi).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderivX hboundX (left_mem_Icc.mpr D.x_lt.le) hx
  have hright := (convex_Icc D.xlo D.xhi).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderivX hboundX hx (right_mem_Icc.mpr D.x_lt.le)
  have hbottom := (convex_Icc D.ylo D.yhi).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderivY hboundY (left_mem_Icc.mpr D.y_lt.le) hy
  have htop := (convex_Icc D.ylo D.yhi).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderivY hboundY hy (right_mem_Icc.mpr D.y_lt.le)
  simpa only [hzero.2.1 z.2 hy, hzero.1 z.2 hy, hzero.2.2.2 z.1 hx,
    hzero.2.2.1 z.1 hx, sub_zero, zero_sub, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hx.1), abs_of_nonneg (sub_nonneg.mpr hx.2),
    abs_of_nonneg (sub_nonneg.mpr hy.1), abs_of_nonneg (sub_nonneg.mpr hy.2)]
    using And.intro hleft (And.intro hright (And.intro hbottom htop))

/-- 四边光滑截断：距任一边不超过 δ 时为零，距每边至少 2δ 时为一。
这是实际 C∞ 函数；δ>0 用于之后支撑和序关系证明，不作为定义中的隐含事实。 -/
def boundaryCutoff (D : Rect) (δ : ℝ) : SmoothField :=
  ⟨fun z =>
    Real.smoothTransition ((z.1-D.xlo-δ)/δ) *
    Real.smoothTransition ((D.xhi-z.1-δ)/δ) *
    Real.smoothTransition ((z.2-D.ylo-δ)/δ) *
    Real.smoothTransition ((D.yhi-z.2-δ)/δ), by
      change ContDiff ℝ ∞ _
      apply ContDiff.mul
      · apply ContDiff.mul
        · apply ContDiff.mul
          · exact Real.smoothTransition.contDiff.comp (by fun_prop)
          · exact Real.smoothTransition.contDiff.comp (by fun_prop)
        · exact Real.smoothTransition.contDiff.comp (by fun_prop)
      · exact Real.smoothTransition.contDiff.comp (by fun_prop)⟩

/-- 截断值在 [0,1]；来自 mathlib `smoothTransition` 的范围定理。 -/
theorem boundaryCutoff_bounds (D : Rect) (δ : ℝ) (z : ℝ × ℝ) :
    0 ≤ boundaryCutoff D δ z ∧ boundaryCutoff D δ z ≤ 1 := by
  have hmul {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
      0 ≤ a*b ∧ a*b ≤ 1 := ⟨mul_nonneg ha.1 hb.1,
        (mul_le_mul ha.2 hb.2 hb.1 (by norm_num)).trans (by norm_num)⟩
  have htrans (x : ℝ) : 0 ≤ Real.smoothTransition x ∧ Real.smoothTransition x ≤ 1 :=
    ⟨Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x⟩
  exact hmul (hmul (hmul (htrans _) (htrans _)) (htrans _)) (htrans _)

/-- 截断支撑落在严格缩小的闭矩形内；因此不会接触原外边界。
这里先控制非零集合，再用闭集包含其闭包，避免只证明普通 support 的不足。 -/
theorem boundaryCutoff_tsupport (D : Rect) {δ : ℝ} (hδ : 0 < δ) :
    tsupport (⇑(boundaryCutoff D δ)) ⊆
      Icc (D.xlo+δ) (D.xhi-δ) ×ˢ Icc (D.ylo+δ) (D.yhi-δ) := by
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  intro z hz
  change boundaryCutoff D δ z ≠ 0 at hz
  simp only [boundaryCutoff, mul_ne_zero_iff] at hz
  have hleft : 0 < (z.1-D.xlo-δ)/δ :=
    lt_of_not_ge (fun h => hz.1.1.1 (Real.smoothTransition.zero_of_nonpos h))
  have hright : 0 < (D.xhi-z.1-δ)/δ :=
    lt_of_not_ge (fun h => hz.1.1.2 (Real.smoothTransition.zero_of_nonpos h))
  have hbottom : 0 < (z.2-D.ylo-δ)/δ :=
    lt_of_not_ge (fun h => hz.1.2 (Real.smoothTransition.zero_of_nonpos h))
  have htop : 0 < (D.yhi-z.2-δ)/δ :=
    lt_of_not_ge (fun h => hz.2 (Real.smoothTransition.zero_of_nonpos h))
  have hleft' := (div_pos_iff_of_pos_right hδ).mp hleft
  have hright' := (div_pos_iff_of_pos_right hδ).mp hright
  have hbottom' := (div_pos_iff_of_pos_right hδ).mp hbottom
  have htop' := (div_pos_iff_of_pos_right hδ).mp htop
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- 乘上实际截断后的场是内部紧支光滑测试函数。
输入 f 不要求本来紧支，也尚不要求零迹；零迹只会用于梯度误差控制。 -/
def cutoffTest (D : Rect) (f : SmoothField) (δ : ℝ) (hδ : 0 < δ) : TestFunction D where
  field := ⟨fun z => boundaryCutoff D δ z * f z,
    (boundaryCutoff D δ).contDiff.mul f.contDiff⟩
  compact := by
    apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure
    exact tsupport_mul_subset_left.trans (boundaryCutoff_tsupport D hδ)
  support_inside := by
    intro z hz
    have hsmaller := boundaryCutoff_tsupport D hδ (tsupport_mul_subset_left hz)
    change (D.xlo < z.1 ∧ z.1 < D.xhi) ∧ (D.ylo < z.2 ∧ z.2 < D.yhi)
    exact ⟨⟨by linarith [hsmaller.1.1], by linarith [hsmaller.1.2]⟩,
      ⟨by linarith [hsmaller.2.1], by linarith [hsmaller.2.2]⟩⟩

/-- 当点距四边都至少 2δ 时，截断确实等于一。
后续点态收敛需把严格内部点的正距离与 δ→0 结合。 -/
theorem boundaryCutoff_eq_one (D : Rect) {δ : ℝ} (hδ : 0 < δ)
    {z : ℝ × ℝ} (hleft : 2*δ ≤ z.1-D.xlo) (hright : 2*δ ≤ D.xhi-z.1)
    (hbottom : 2*δ ≤ z.2-D.ylo) (htop : 2*δ ≤ D.yhi-z.2) :
    boundaryCutoff D δ z = 1 := by
  have harg (d : ℝ) (hd : 2*δ ≤ d) : 1 ≤ (d-δ)/δ := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  simp only [boundaryCutoff,
    Real.smoothTransition.one_of_one_le (harg _ hleft),
    Real.smoothTransition.one_of_one_le (harg _ hright),
    Real.smoothTransition.one_of_one_le (harg _ hbottom),
    Real.smoothTransition.one_of_one_le (harg _ htop), mul_one]

/-- 平滑阶跃在转换区外的实际导数为零；使用邻域常值而非单点取值求导。 -/
theorem transition_deriv_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hleft | hright
  · have hnear : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [gt_mem_nhds hleft] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    simpa using hnear.deriv_eq
  · have hnear : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [lt_mem_nhds hright] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    simpa using hnear.deriv_eq

/-- 平滑阶跃的实际导数有一个全局有限非负上界。
由紧区间上的连续性和转换区外导数为零推出，不是额外假定截断函数的性能。 -/
theorem transition_deriv_bounded :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖deriv Real.smoothTransition x‖ ≤ B := by
  have hcontinuous : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hcontinuous.continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro x
  by_cases hinside : x ∈ Icc (0 : ℝ) 1
  · exact (hB x hinside).trans (le_max_right _ _)
  · have houtside : x < 0 ∨ 1 < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hinside
    rw [transition_deriv_zero houtside, norm_zero]
    exact le_max_left _ _

/-- 边界层关键抵消：若 d≤2δ、|f|≤Md，而阶跃导数≤B，则
|(阶跃导数/δ)f|≤2BM。分母 δ 的非零性来自 hδ，不对吸收系数作除法。
该纯序估计供下面四个实际边界截断项调用。 -/
theorem cutoff_derivative_term_bound {δ M B d value slope : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hd : d ≤ 2*δ) (hvalue : ‖value‖ ≤ M*d) (hslope : ‖slope‖ ≤ B) :
    ‖(slope/δ)*value‖ ≤ 2*B*M := by
  have hvalueδ : ‖value‖ ≤ 2*M*δ := by nlinarith
  have hdiv : ‖slope / δ‖ ≤ B/δ := by
    rw [norm_div, Real.norm_of_nonneg hδ.le]
    exact div_le_div_of_nonneg_right hslope hδ.le
  calc
    ‖(slope/δ)*value‖ = ‖slope/δ‖ * ‖value‖ := norm_mul _ _
    _ ≤ (B/δ)*(2*M*δ) := mul_le_mul hdiv hvalueδ (norm_nonneg _) (div_nonneg hB hδ.le)
    _ = 2*B*M := by field_simp

/-- 四个边界过渡因子的统一估计，服务于实际截断乘积的两个偏导。 -/
theorem transition_cutoff_term_bound {M B δ d value : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hδ : 0 < δ)
    (htransition : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ B)
    (hvalue : ‖value‖ ≤ M*d) :
    ‖(deriv Real.smoothTransition ((d-δ)/δ)/δ)*value‖ ≤ 2*B*M := by
  by_cases hstrip : d ≤ 2*δ
  · exact cutoff_derivative_term_bound hδ hM hB hstrip hvalue (htransition _)
  · have harg : 1 < (d-δ)/δ := by
      apply (lt_div_iff₀ hδ).mpr
      linarith
    rw [transition_deriv_zero (Or.inr harg)]
    simp only [zero_div, zero_mul, norm_zero]
    positivity

/-- δₙ=1/(n+1) 为正并趋零；所构造的每一项都是真实内部紧支测试函数。 -/
def cutoffSequence (D : Rect) (f : SmoothField) (n : ℕ) : TestFunction D :=
  cutoffTest D f (1/((n:ℝ)+1)) (by positivity)

/-- 在严格内核（距四边 >2δ）内，截断在一个邻域内恒等于一。
邻域相等是接着比较实际偏导的依据；单点 χ=1 不足以作该推理。 -/
theorem cutoffTest_eventuallyEq (D : Rect) (f : SmoothField) {δ : ℝ}
    (hδ : 0 < δ) {z : ℝ × ℝ}
    (hleft : 2*δ < z.1-D.xlo) (hright : 2*δ < D.xhi-z.1)
    (hbottom : 2*δ < z.2-D.ylo) (htop : 2*δ < D.yhi-z.2) :
    (⇑(cutoffTest D f δ hδ).field) =ᶠ[𝓝 z] (⇑f) := by
  have hnearLeft : ∀ᶠ y : ℝ × ℝ in 𝓝 z, 2*δ < y.1-D.xlo :=
    (continuous_fst.sub continuous_const).continuousAt.eventually (lt_mem_nhds hleft)
  have hnearRight : ∀ᶠ y : ℝ × ℝ in 𝓝 z, 2*δ < D.xhi-y.1 :=
    (continuous_const.sub continuous_fst).continuousAt.eventually (lt_mem_nhds hright)
  have hnearBottom : ∀ᶠ y : ℝ × ℝ in 𝓝 z, 2*δ < y.2-D.ylo :=
    (continuous_snd.sub continuous_const).continuousAt.eventually (lt_mem_nhds hbottom)
  have hnearTop : ∀ᶠ y : ℝ × ℝ in 𝓝 z, 2*δ < D.yhi-y.2 :=
    (continuous_const.sub continuous_snd).continuousAt.eventually (lt_mem_nhds htop)
  filter_upwards [hnearLeft,hnearRight,hnearBottom,hnearTop] with y hL hR hB hT
  change boundaryCutoff D δ y * f y = f y
  rw [boundaryCutoff_eq_one D hδ hL.le hR.le hB.le hT.le, one_mul]

/-- 每个严格内部点上，逼近序列最终连同两个真实导数都与 f 完全一致。
尚不能把本结论称为 L² 图范数收敛：还须证明统一的可积控制并调用支配收敛。 -/
theorem cutoffSequence_eventually_eq_with_derivatives (D : Rect) (f : SmoothField)
    {z : ℝ × ℝ} (hz : z ∈ D.openSet) :
    ∀ᶠ n : ℕ in atTop,
      (cutoffSequence D f n).field z = f z ∧
      dx (cutoffSequence D f n).field z = dx f z ∧
      dy (cutoffSequence D f n).field z = dy f z := by
  let d := min (min (z.1-D.xlo) (D.xhi-z.1)) (min (z.2-D.ylo) (D.yhi-z.2))
  have hd_pos : 0 < d := by
    dsimp [d]
    exact lt_min (lt_min (sub_pos.mpr hz.1.1) (sub_pos.mpr hz.1.2))
      (lt_min (sub_pos.mpr hz.2.1) (sub_pos.mpr hz.2.2))
  have hδsmall : ∀ᶠ n : ℕ in atTop, 1/((n:ℝ)+1) < d/2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0)).eventually
        (gt_mem_nhds (by positivity : (0:ℝ) < d/2))
  have hdL : d ≤ z.1-D.xlo := (min_le_left _ _).trans (min_le_left _ _)
  have hdR : d ≤ D.xhi-z.1 := (min_le_left _ _).trans (min_le_right _ _)
  have hdB : d ≤ z.2-D.ylo := (min_le_right _ _).trans (min_le_left _ _)
  have hdT : d ≤ D.yhi-z.2 := (min_le_right _ _).trans (min_le_right _ _)
  filter_upwards [hδsmall] with n hn
  have hnear := cutoffTest_eventuallyEq D f
    (δ := 1/((n:ℝ)+1)) (by positivity) (z := z)
    (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨hnear.eq_of_nhds, ?_, ?_⟩
  · exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0)) hnear.fderiv_eq
  · exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) hnear.fderiv_eq

/-- 四因子截断乘积的导数估计：这是供真实偏导调用的辅助代数层。
a,b 是沿当前坐标变化的因子，c,d 沿该坐标恒定；两项导数误差各受 C 控制。 -/
theorem cutoff_product_derivative_bound {a b c d da db v dv C M : ℝ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (hda : ‖da*v‖ ≤ C) (hdb : ‖db*v‖ ≤ C) (hdv : ‖dv‖ ≤ M) :
    ‖((da*b+a*db)*c*d)*v+(a*b*c*d)*dv‖ ≤ 2*C+M := by
  have hmul {x y : ℝ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x*y‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have htermA : ‖(da*v)*(b*c*d)‖ ≤ C := by
    calc
      _ = ‖da*v‖*‖b*c*d‖ := norm_mul _ _
      _ ≤ ‖da*v‖ := by nlinarith [hmul (hmul hb hc) hd, norm_nonneg (da*v)]
      _ ≤ C := hda
  have htermB : ‖(db*v)*(a*c*d)‖ ≤ C := by
    calc
      _ = ‖db*v‖*‖a*c*d‖ := norm_mul _ _
      _ ≤ ‖db*v‖ := by nlinarith [hmul (hmul ha hc) hd, norm_nonneg (db*v)]
      _ ≤ C := hdb
  have htermV : ‖(a*b*c*d)*dv‖ ≤ M := by
    calc
      _ = ‖a*b*c*d‖*‖dv‖ := norm_mul _ _
      _ ≤ ‖dv‖ := by nlinarith [hmul (hmul (hmul ha hb) hc) hd, norm_nonneg dv]
      _ ≤ M := hdv
  calc
    _ = ‖((da*v)*(b*c*d)+(db*v)*(a*c*d))+(a*b*c*d)*dv‖ := by congr 1; ring
    _ ≤ ‖(da*v)*(b*c*d)‖+‖(db*v)*(a*c*d)‖+‖(a*b*c*d)*dv‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2*C+M := by linarith

/-- 实际截断测试函数的 x 偏导公式。
先对四个阶跃因子及 f 的 x 切片应用真实 HasDerivAt 乘积法则，再取导数值。 -/
theorem cutoffTest_dx (D : Rect) (f : SmoothField) {δ : ℝ} (hδ : 0 < δ)
    (z : ℝ × ℝ) :
    dx (cutoffTest D f δ hδ).field z =
      ((deriv Real.smoothTransition ((z.1-D.xlo-δ)/δ)/δ *
          Real.smoothTransition ((D.xhi-z.1-δ)/δ) +
        Real.smoothTransition ((z.1-D.xlo-δ)/δ) *
          (-deriv Real.smoothTransition ((D.xhi-z.1-δ)/δ)/δ)) *
        Real.smoothTransition ((z.2-D.ylo-δ)/δ) *
        Real.smoothTransition ((D.yhi-z.2-δ)/δ)) * f z +
      boundaryCutoff D δ z * dx f z := by
  have htransition (x : ℝ) : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition x) x :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable (by simp) x).hasDerivAt
  have hleft := (htransition ((z.1-D.xlo-δ)/δ)).comp z.1
    ((((hasDerivAt_id z.1).sub_const D.xlo).sub_const δ).div_const δ)
  have hright := (htransition ((D.xhi-z.1-δ)/δ)).comp z.1
    ((((hasDerivAt_const z.1 D.xhi).sub (hasDerivAt_id z.1)).sub_const δ).div_const δ)
  have hbottom := hasDerivAt_const z.1 (Real.smoothTransition ((z.2-D.ylo-δ)/δ))
  have htop := hasDerivAt_const z.1 (Real.smoothTransition ((D.yhi-z.2-δ)/δ))
  have hproduct := (((hleft.mul hright).mul hbottom).mul htop).mul (f.hasDerivAt_sliceX z)
  dsimp only [Function.comp_def, Pi.mul_apply, Pi.sub_apply, id_eq] at hproduct
  rw [SmoothField.dx_eq_deriv]
  convert hproduct.deriv using 1 <;> first | rfl | (dsimp [cutoffTest, boundaryCutoff]; ring)

/-- 实际截断测试函数的 y 偏导公式；先排列 y 两因子，再复用同一乘积估计。 -/
theorem cutoffTest_dy (D : Rect) (f : SmoothField) {δ : ℝ} (hδ : 0 < δ)
    (z : ℝ × ℝ) :
    dy (cutoffTest D f δ hδ).field z =
      ((deriv Real.smoothTransition ((z.2-D.ylo-δ)/δ)/δ *
          Real.smoothTransition ((D.yhi-z.2-δ)/δ) +
        Real.smoothTransition ((z.2-D.ylo-δ)/δ) *
          (-deriv Real.smoothTransition ((D.yhi-z.2-δ)/δ)/δ)) *
        Real.smoothTransition ((z.1-D.xlo-δ)/δ) *
        Real.smoothTransition ((D.xhi-z.1-δ)/δ)) * f z +
      boundaryCutoff D δ z * dy f z := by
  have htransition (x : ℝ) : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition x) x :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable (by simp) x).hasDerivAt
  have hbottom := (htransition ((z.2-D.ylo-δ)/δ)).comp z.2
    ((((hasDerivAt_id z.2).sub_const D.ylo).sub_const δ).div_const δ)
  have htop := (htransition ((D.yhi-z.2-δ)/δ)).comp z.2
    ((((hasDerivAt_const z.2 D.yhi).sub (hasDerivAt_id z.2)).sub_const δ).div_const δ)
  have hleft := hasDerivAt_const z.2 (Real.smoothTransition ((z.1-D.xlo-δ)/δ))
  have hright := hasDerivAt_const z.2 (Real.smoothTransition ((D.xhi-z.1-δ)/δ))
  have hproduct := (((hleft.mul hright).mul hbottom).mul htop).mul (f.hasDerivAt_sliceY z)
  dsimp only [Function.comp_def, Pi.mul_apply, Pi.sub_apply, id_eq] at hproduct
  rw [SmoothField.dy_eq_deriv]
  convert hproduct.deriv using 1 <;> first | rfl | (dsimp [cutoffTest, boundaryCutoff]; ring)

/-- 零迹使两个实际截断偏导都有与 δ 无关的统一上界 (4B+1)M。
逐边距离估计抵消阶跃导数中的 1/δ；不由点态收敛猜测 L² 收敛。 -/
theorem cutoffTest_partial_bound (D : Rect) (f : SmoothField)
    (hzero : ZeroBoundary D f) {M B δ : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ D.closedSet, ‖dx f z‖ ≤ M ∧ ‖dy f z‖ ≤ M)
    (htransition : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ B)
    (hδ : 0 < δ) {z : ℝ × ℝ} (hz : z ∈ D.closedSet) :
    ‖dx (cutoffTest D f δ hδ).field z‖ ≤ 4*B*M+M ∧
    ‖dy (cutoffTest D f δ hδ).field z‖ ≤ 4*B*M+M := by
  have hnorm (x : ℝ) : ‖Real.smoothTransition x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (Real.smoothTransition.nonneg x)]
    exact Real.smoothTransition.le_one x
  have hdistance := hzero.norm_le_four_distances D f hbound hz
  have hleft := transition_cutoff_term_bound hM hB hδ htransition hdistance.1
  have hright := transition_cutoff_term_bound hM hB hδ htransition hdistance.2.1
  have hbottom := transition_cutoff_term_bound hM hB hδ htransition hdistance.2.2.1
  have htop := transition_cutoff_term_bound hM hB hδ htransition hdistance.2.2.2
  have hrightNeg : ‖(-deriv Real.smoothTransition ((D.xhi-z.1-δ)/δ)/δ)*f z‖ ≤ 2*B*M := by
    simpa only [neg_div, neg_mul, norm_neg] using hright
  have htopNeg : ‖(-deriv Real.smoothTransition ((D.yhi-z.2-δ)/δ)/δ)*f z‖ ≤ 2*B*M := by
    simpa only [neg_div, neg_mul, norm_neg] using htop
  constructor
  · rw [cutoffTest_dx]
    simpa only [boundaryCutoff, show 2*(2*B*M)+M = 4*B*M+M by ring] using
      cutoff_product_derivative_bound (hnorm _) (hnorm _) (hnorm _) (hnorm _)
        hleft hrightNeg (hbound z hz).1
  · rw [cutoffTest_dy]
    have hboundY := cutoff_product_derivative_bound
      (hnorm ((z.2-D.ylo-δ)/δ)) (hnorm ((D.yhi-z.2-δ)/δ))
      (hnorm ((z.1-D.xlo-δ)/δ)) (hnorm ((D.xhi-z.1-δ)/δ))
      hbottom htopNeg (hbound z hz).2
    convert hboundY using 1
    · congr 1
      dsimp [boundaryCutoff]
      ring
    · ring

/-- 紧矩形上统一有界、逐点最终相等的光滑函数，其实际 L² 类收敛。
证明对平方差应用支配收敛，再用 L² 范数平方的积分公式；不假定 L² 收敛。
下游对 f、∂x f、∂y f 分别调用，本引理单独不代表 H¹ 密度。 -/
theorem smoothToL2_tendsto_of_bounded_eventuallyEq (D : Rect)
    (F : ℕ → SmoothField) (f : SmoothField) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n z, z ∈ D.closedSet → ‖F n z‖ ≤ C)
    (hfbound : ∀ z ∈ D.closedSet, ‖f z‖ ≤ C)
    (heventually : ∀ z ∈ D.openSet, ∀ᶠ n : ℕ in atTop, F n z = f z) :
    Tendsto (fun n => SmoothField.toL2 D (F n)) atTop (𝓝 (SmoothField.toL2 D f)) := by
  have hmem : ∀ᵐ z ∂D.measure, z ∈ D.openSet :=
    ae_restrict_mem D.openSet_open.measurableSet
  have hdominated : ∀ n, ∀ᵐ z ∂D.measure, ‖(F n z-f z)^2‖ ≤ (2*C)^2 := by
    intro n
    filter_upwards [hmem] with z hz
    have hclosed : z ∈ D.closedSet := ⟨⟨hz.1.1.le,hz.1.2.le⟩,⟨hz.2.1.le,hz.2.2.le⟩⟩
    have hnorm : ‖F n z-f z‖ ≤ 2*C :=
      (norm_sub_le _ _).trans (by linarith [hbound n z hclosed,hfbound z hclosed])
    rw [norm_pow]
    nlinarith [norm_nonneg (F n z-f z)]
  have hpointwise : ∀ᵐ z ∂D.measure,
      Tendsto (fun n => (F n z-f z)^2) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hmem] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [heventually z hz] with n hn
    simp [hn]
  have hintegral := tendsto_integral_of_dominated_convergence
    (μ := D.measure) (fun _ => (2*C)^2)
    (fun n => (((F n).continuous.sub f.continuous).pow 2).aestronglyMeasurable)
    (integrable_const _) hdominated hpointwise
  have hsquare : Tendsto (fun n => ‖SmoothField.toL2 D (F n)-SmoothField.toL2 D f‖^2)
      atTop (𝓝 (0:ℝ)) := by
    have heq (n : ℕ) : ‖SmoothField.toL2 D (F n)-SmoothField.toL2 D f‖^2 =
        ∫ z, (F n z-f z)^2 ∂D.measure := by
      rw [← map_sub, norm_toL2_sq]
      rfl
    simp only [integral_zero] at hintegral
    exact hintegral.congr' (Eventually.of_forall fun n => (heq n).symm)
  have hnorm := (Real.continuous_sqrt.tendsto 0).comp hsquare
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hnorm

/-- 四边截断同时逼近函数及两个一阶导数的实际 L² 等价类。
零迹仅用于统一偏导界；所有三项最终相等都来自严格内部点的邻域截断。
这是需要的 H¹ 图范数逼近的三个组成结论。 -/
theorem cutoffSequence_toL2_convergence (D : Rect) (f : SmoothField)
    (hzero : ZeroBoundary D f) :
    Tendsto (fun n => SmoothField.toL2 D (cutoffSequence D f n).field)
      atTop (𝓝 (SmoothField.toL2 D f)) ∧
    Tendsto (fun n => SmoothField.toL2 D (cutoffSequence D f n).field.derivativeX)
      atTop (𝓝 (SmoothField.toL2 D f.derivativeX)) ∧
    Tendsto (fun n => SmoothField.toL2 D (cutoffSequence D f n).field.derivativeY)
      atTop (𝓝 (SmoothField.toL2 D f.derivativeY)) := by
  obtain ⟨M,hM,hpartial⟩ := f.exists_partial_bound D
  obtain ⟨B,hB,htransition⟩ := transition_deriv_bounded
  obtain ⟨C,hfunction⟩ := D.closedSet_compact.exists_bound_of_continuousOn f.continuous.continuousOn
  have heventually (z : ℝ × ℝ) (hz : z ∈ D.openSet) :=
    cutoffSequence_eventually_eq_with_derivatives D f hz
  have hpartials (n : ℕ) (z : ℝ × ℝ) (hz : z ∈ D.closedSet) :=
    cutoffTest_partial_bound D f hzero hM hB hpartial htransition
      (δ := 1/((n:ℝ)+1)) (by positivity) hz
  have hMle : M ≤ 4*B*M+M := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · apply smoothToL2_tendsto_of_bounded_eventuallyEq D _ f (C := max 0 C) (le_max_left _ _)
    · intro n z hz
      change ‖boundaryCutoff D (1/((n:ℝ)+1)) z * f z‖ ≤ max 0 C
      have hcut := boundaryCutoff_bounds D (1/((n:ℝ)+1)) z
      rw [norm_mul, Real.norm_of_nonneg hcut.1]
      have hnorm : boundaryCutoff D (1/((n:ℝ)+1)) z * ‖f z‖ ≤ ‖f z‖ := by
        nlinarith [norm_nonneg (f z)]
      exact hnorm.trans ((hfunction z hz).trans (le_max_right _ _))
    · intro z hz
      exact (hfunction z hz).trans (le_max_right _ _)
    · intro z hz
      exact (heventually z hz).mono (fun n hn => hn.1)
  · apply smoothToL2_tendsto_of_bounded_eventuallyEq D _ f.derivativeX
      (C := 4*B*M+M) (by positivity)
    · intro n z hz
      exact (hpartials n z hz).1
    · intro z hz
      exact (hpartial z hz).1.trans hMle
    · intro z hz
      exact (heventually z hz).mono (fun n hn => hn.2.1)
  · apply smoothToL2_tendsto_of_bounded_eventuallyEq D _ f.derivativeY
      (C := 4*B*M+M) (by positivity)
    · intro n z hz
      exact (hpartials n z hz).2
    · intro z hz
      exact (hpartial z hz).2.trans hMle
    · intro z hz
      exact (heventually z hz).mono (fun n hn => hn.2.2)

/-- M1 的一般桥接：任意旧光滑四边零迹场都属于现有 H₀¹ 图闭包。
没有输入逼近序列或闭包成员资格：`cutoffSequence` 已构造内部紧支 C∞ 测试函数，
`cutoffSequence_toL2_convergence` 同时证明函数和两个实际偏导的 L² 收敛。
有限乘积拓扑及子类型拓扑将三项收敛组成原来的 H¹ 最大值图范数收敛。 -/
theorem smoothToWeakH1_mem_zeroBoundaryGraph (D : Rect) (f : SmoothField)
    (hzero : ZeroBoundary D f) : smoothToWeakH1 D f ∈ zeroBoundaryGraph D := by
  have hthree := cutoffSequence_toL2_convergence D f hzero
  have hgraph : Tendsto (fun n => smoothToWeakH1 D (cutoffSequence D f n).field)
      atTop (𝓝 (smoothToWeakH1 D f)) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact hthree.1
    · exact hthree.2.1
    · exact hthree.2.2
  have hclosed : IsClosed (zeroBoundaryGraph D : Set (weakH1Graph D)) :=
    Submodule.isClosed_topologicalClosure _
  exact hclosed.mem_of_tendsto hgraph
    (Eventually.of_forall fun n => test_mem_zeroBoundaryGraph D (cutoffSequence D f n))

/-- 非零回归调用：矩形多项式泡函数并非预先内部紧支，
但由四边零迹和本轮一般桥接进入 H₀¹。非零性是实际 L² 类的非零性。 -/
theorem rectangleBubble_weakH01 (D : Rect) :
    smoothToWeakH1 D (rectangleBubble D) ∈ zeroBoundaryGraph D ∧
    SmoothField.toL2 D (rectangleBubble D) ≠ 0 := by
  exact ⟨smoothToWeakH1_mem_zeroBoundaryGraph D (rectangleBubble D)
    (rectangleBubble_zeroBoundary D), rectangleBubble_toL2_ne_zero D⟩

/-- 旧光滑零迹对象进入现有弱零边界算子的实际 L² 定义域。
这是一般桥接的直接接口调用；没有在普通 L² 等价类上读取边界值。 -/
theorem smooth_zero_mem_weakZeroFieldDomain (D : Rect) (f : SmoothField)
    (hzero : ZeroBoundary D f) : SmoothField.toL2 D f ∈ weakZeroFieldDomain D := by
  exact ⟨⟨smoothToWeakH1 D f, smoothToWeakH1_mem_zeroBoundaryGraph D f hzero⟩, rfl⟩

/-- 旧受限迹核到新 H₀¹ 值域的连接。
Fields/Boundary 已证代表无关性，故通过其代表及本轮图逼近即可进入新域。 -/
theorem smooth_trace_zero_mem_weakZeroFieldDomain (D : Rect) (v : fieldDomain D)
    (htrace : trace D v = 0) : v.val ∈ weakZeroFieldDomain D := by
  have hzero : ZeroBoundary D (representative D v) := (trace_zero_iff D v).mp htrace
  have hmember := smooth_zero_mem_weakZeroFieldDomain D (representative D v) hzero
  rwa [representative_toL2] at hmember

end LeanPML.Rectangle
