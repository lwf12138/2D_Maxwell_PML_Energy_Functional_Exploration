import LeanPML.Rectangle.WeakPoincare
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# V7 (5.1) 精确常数的分析证明

先用正弦对数导数和积分分部证明内部紧支函数的一维 Dirichlet–Wirtinger，
随后通过切片/Fubini 和 H¹ 图闭包进入矩形弱空间。
保守常数模块保持不变；新结论是否接入最终主定理须单独核验。
-/
noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace LeanPML.Rectangle
/-- 精确 Dirichlet 常数的平方展开步骤：q'+q²=−k²。
这里先在无奇点的闭子区间证明；后续必须构造 cot 系数并处理紧支截断。 -/
theorem ground_state_interval_bound {a b k : ℝ} (hab : a ≤ b)
    (f df q : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hq : ContinuousOn q (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hRiccati : ∀ x ∈ Ioo a b, HasDerivAt q (-(k^2) - (q x)^2) x)
    (ha : f a = 0) (hb : f b = 0) :
    k^2 * (∫ x in a..b, (f x)^2) ≤ ∫ x in a..b, (df x)^2 := by
  have hprod : ContinuousOn (fun x => q x * (f x)^2) (Icc a b) := hq.mul (hf.pow 2)
  have hdprod : ∀ x ∈ Ioo a b, HasDerivAt (fun y => q y * (f y)^2)
      ((-(k^2)-(q x)^2)*(f x)^2+2*q x*f x*df x) x := by
    intro x hx
    have hraw := (hRiccati x hx).mul ((hderiv x hx).pow 2)
    exact hraw.congr_deriv (by simp only [Pi.pow_apply]; ring)
  have hiF : IntervalIntegrable (fun x => (f x)^2) volume a b := (hf.pow 2).intervalIntegrable_of_Icc hab
  have hiD : IntervalIntegrable (fun x => (df x)^2) volume a b := (hdf.pow 2).intervalIntegrable_of_Icc hab
  have hiQF : IntervalIntegrable (fun x => (q x)^2*(f x)^2) volume a b := ((hq.pow 2).mul (hf.pow 2)).intervalIntegrable_of_Icc hab
  have hiCross : IntervalIntegrable (fun x => q x*f x*df x) volume a b := ((hq.mul hf).mul hdf).intervalIntegrable_of_Icc hab
  have hiProd : ContinuousOn (fun x => (-(k^2)-(q x)^2)*(f x)^2+2*q x*f x*df x) (Icc a b) := ((continuousOn_const.sub (hq.pow 2)).mul (hf.pow 2)).add
    (((continuousOn_const.mul hq).mul hf).mul hdf)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hprod hdprod
    (hiProd.intervalIntegrable_of_Icc hab)
  have hexpand : (∫ x in a..b, (-(k^2)-(q x)^2)*(f x)^2+2*q x*f x*df x) =
      -(k^2)*(∫ x in a..b, (f x)^2) - (∫ x in a..b, (q x)^2*(f x)^2) +
      2*(∫ x in a..b, q x*f x*df x) := by
    calc
      _ = ∫ x in a..b, (-(k^2)*(f x)^2 - (q x)^2*(f x)^2) + 2*(q x*f x*df x) := by
        apply intervalIntegral.integral_congr; intro x hx; ring
      _ = _ := by
        rw [intervalIntegral.integral_add ((hiF.const_mul _).sub hiQF) (hiCross.const_mul _),
          intervalIntegral.integral_sub (hiF.const_mul _) hiQF,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hexpand, ha, hb] at hFTC
  have hnonneg : 0 ≤ ∫ x in a..b, (df x-q x*f x)^2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)
  have hsquare : (∫ x in a..b, (df x-q x*f x)^2) =
      (∫ x in a..b, (df x)^2) - 2*(∫ x in a..b, q x*f x*df x) +
      (∫ x in a..b, (q x)^2*(f x)^2) := by
    calc
      _ = ∫ x in a..b, ((df x)^2 - 2*(q x*f x*df x)) + (q x)^2*(f x)^2 := by
        apply intervalIntegral.integral_congr; intro x hx; ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hiD.sub (hiCross.const_mul _)) hiQF,
          intervalIntegral.integral_sub hiD (hiCross.const_mul _), intervalIntegral.integral_const_mul]
  rw [hsquare] at hnonneg
  nlinarith

/-- sin 的对数导数在区间内部满足 Riccati 恒等式，端点奇点不被忽略。 -/
theorem sine_log_derivative {a b x : ℝ} (hab : a < b) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => (Real.pi/(b-a)) * Real.cos ((Real.pi/(b-a))*(y-a)) /
      Real.sin ((Real.pi/(b-a))*(y-a)))
      (-((Real.pi/(b-a))^2) - ((Real.pi/(b-a)) * Real.cos ((Real.pi/(b-a))*(x-a)) /
        Real.sin ((Real.pi/(b-a))*(x-a)))^2) x := by
  let k := Real.pi/(b-a)
  have hk : 0 < k := div_pos Real.pi_pos (sub_pos.mpr hab)
  have hangle : k * (x-a) ∈ Ioo 0 Real.pi := by
    constructor
    · exact mul_pos hk (sub_pos.mpr hx.1)
    · have htop : k*(b-a) = Real.pi := div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')
      rw [← htop]
      exact mul_lt_mul_of_pos_left (sub_lt_sub_right hx.2 a) hk
  have hsin : Real.sin (k*(x-a)) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hangle.1 hangle.2).ne'
  have hangle_deriv : HasDerivAt (fun y : ℝ => k*(y-a)) k x := by
    simpa using ((hasDerivAt_id x).sub_const a).const_mul k
  have hcos := hangle_deriv.cos.const_mul k
  have hsine := hangle_deriv.sin
  have hquot := hcos.div hsine hsin
  apply hquot.congr_deriv
  change (k * (-Real.sin (k*(x-a))*k) * Real.sin (k*(x-a)) -
    k * Real.cos (k*(x-a)) * (Real.cos (k*(x-a))*k)) / Real.sin (k*(x-a))^2 =
    -(k^2) - (k * Real.cos (k*(x-a)) / Real.sin (k*(x-a)))^2
  field_simp [hsin]

/-- 对内部紧支 C¹ 函数证明一维 Dirichlet–Wirtinger。
先把积分限制到远离 sin 零点的闭子区间，再用真实支撑恢复全积分。 -/
theorem dirichlet_wirtinger_compact {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ Ioo a b) :
    (Real.pi/(b-a))^2 * (∫ x, (f x)^2) ≤ ∫ x, (deriv f x)^2 := by
  by_cases hzero : f = 0
  · subst f; simp
  have hnonempty : (tsupport f).Nonempty := by
    by_contra hempty
    have hempty' : tsupport f = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    apply hzero
    exact Function.support_eq_empty_iff.mp (Set.eq_empty_of_subset_empty
      (subset_tsupport f |>.trans (by rw [hempty'])))
  obtain ⟨xmin, hminmem, hmin⟩ := hcompact.exists_isMinOn hnonempty continuousOn_id
  obtain ⟨xmax, hmaxmem, hmax⟩ := hcompact.exists_isMaxOn hnonempty continuousOn_id
  let A := (a+xmin)/2
  let B := (b+xmax)/2
  have hA : a < A ∧ A < xmin := by dsimp [A]; constructor <;> linarith [(hsupport hminmem).1]
  have hB : xmax < B ∧ B < b := by dsimp [B]; constructor <;> linarith [(hsupport hmaxmem).2]
  have hminmax : xmin ≤ xmax := hmin hmaxmem
  have hAB : A < B := by linarith
  have hsupportAB : tsupport f ⊆ Ioo A B := by
    intro x hx
    exact ⟨hA.2.trans_le (hmin hx), (hmax hx).trans_lt hB.1⟩
  have hfA : f A = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (lt_irrefl A) (hsupportAB hmem).1
  have hfB : f B = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (lt_irrefl B) (hsupportAB hmem).2
  let k := Real.pi/(b-a)
  let q := fun y => k*Real.cos (k*(y-a))/Real.sin (k*(y-a))
  have hq_deriv : ∀ x ∈ Icc A B, HasDerivAt q (-(k^2)-(q x)^2) x := by
    intro x hx
    exact sine_log_derivative hab ⟨hA.1.trans_le hx.1, hx.2.trans_lt hB.2⟩
  have hq : ContinuousOn q (Icc A B) := fun x hx => (hq_deriv x hx).continuousAt.continuousWithinAt
  have hbound := ground_state_interval_bound hAB.le f (deriv f) q
    hf.continuous.continuousOn (hf.continuous_deriv (by norm_num)).continuousOn hq
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt)
    (fun x hx => hq_deriv x (Ioo_subset_Icc_self hx)) hfA hfB
  have hfsupport : Function.support (fun x => (f x)^2) ⊆ Ioc A B := by
    intro x hx
    have hmem : x ∈ tsupport f := subset_tsupport f (by simpa using hx)
    exact ⟨(hsupportAB hmem).1, (hsupportAB hmem).2.le⟩
  have hdsupport : Function.support (fun x => (deriv f x)^2) ⊆ Ioc A B := by
    intro x hx
    have hmem : x ∈ tsupport f := support_deriv_subset (by simpa using hx)
    exact ⟨(hsupportAB hmem).1, (hsupportAB hmem).2.le⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hfsupport,
    intervalIntegral.integral_eq_integral_of_support_subset hdsupport] at hbound
  exact hbound


/-- 由 (5.1) 推出的一维切片步骤，原文未单列。
测试函数支撑严格在 Ω 内，故每条切片也有内部紧支；导数是实际 dx。 -/
theorem test_slice_wirtinger_x (D : Rect) (φ : TestFunction D) (y : ℝ) :
    (Real.pi/D.Lx)^2 * (∫ x, (φ.field (x,y))^2) ≤
      ∫ x, (dx φ.field (x,y))^2 := by
  have hsupp : tsupport (fun x => φ.field (x,y)) ⊆ Ioo D.xlo D.xhi := by
    intro x hx
    have hpair := tsupport_comp_subset_preimage (⇑φ.field)
      (continuous_id.prodMk continuous_const) hx
    exact (φ.support_inside hpair).1
  have hcompact : HasCompactSupport (fun x => φ.field (x,y)) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (hsupp.trans Ioo_subset_Icc_self)
  have hsmooth : ContDiff ℝ 1 (fun x => φ.field (x,y)) :=
    (φ.field.contDiff.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hbound := dirichlet_wirtinger_compact D.x_lt _ hsmooth hcompact hsupp
  have heq : (fun x => deriv (fun s => φ.field (s,y)) x) = (fun x => dx φ.field (x,y)) :=
    funext (fun x => (φ.field.hasDerivAt_sliceX (x,y)).deriv)
  simp_rw [show ∀ z, deriv (fun s => φ.field (s,y)) z = dx φ.field (z,y) from fun z => congrFun heq z] at hbound
  exact hbound

/-- y 方向的真实切片估计，与 x 方向独立，保留矩形两条边长。 -/
theorem test_slice_wirtinger_y (D : Rect) (φ : TestFunction D) (x : ℝ) :
    (Real.pi/D.Ly)^2 * (∫ y, (φ.field (x,y))^2) ≤
      ∫ y, (dy φ.field (x,y))^2 := by
  have hsupp : tsupport (fun y => φ.field (x,y)) ⊆ Ioo D.ylo D.yhi := by
    intro y hy
    have hpair := tsupport_comp_subset_preimage (⇑φ.field)
      (continuous_const.prodMk continuous_id) hy
    exact (φ.support_inside hpair).2
  have hcompact : HasCompactSupport (fun y => φ.field (x,y)) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (hsupp.trans Ioo_subset_Icc_self)
  have hsmooth : ContDiff ℝ 1 (fun y => φ.field (x,y)) :=
    (φ.field.contDiff.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hbound := dirichlet_wirtinger_compact D.y_lt _ hsmooth hcompact hsupp
  have heq : (fun y => deriv (fun s => φ.field (x,s)) y) = (fun y => dy φ.field (x,y)) :=
    funext (fun y => (φ.field.hasDerivAt_sliceY (x,y)).deriv)
  simp_rw [show ∀ z, deriv (fun s => φ.field (x,s)) z = dy φ.field (x,z) from fun z => congrFun heq z] at hbound
  exact hbound

/-- (5.1) 在真实二维内部紧支测试函数上的方向和估计。
可积性来自紧支连续函数；Fubini 后积分逐条切片的已证一维不等式。 -/
theorem test_sharp_poincare (D : Rect) (φ : TestFunction D) :
    ((Real.pi/D.Lx)^2+(Real.pi/D.Ly)^2) * ‖SmoothField.toL2 D φ.field‖^2 ≤
      ‖SmoothField.toL2 D φ.field.derivativeX‖^2 +
      ‖SmoothField.toL2 D φ.field.derivativeY‖^2 := by
  have hcx : HasCompactSupport (dx φ.field) :=
    (φ.compact.fderiv ℝ).comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0)) (by simp)
  have hcy : HasCompactSupport (dy φ.field) :=
    (φ.compact.fderiv ℝ).comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) (by simp)
  have hiF : Integrable (fun z => (φ.field z)^2) volume :=
    (φ.field.continuous.pow 2).integrable_of_hasCompactSupport
      (φ.compact.comp_left (g := fun x : ℝ => x^2) (by norm_num))
  have hiX : Integrable (fun z => (dx φ.field z)^2) volume :=
    (φ.field.derivativeX.continuous.pow 2).integrable_of_hasCompactSupport (hcx.comp_left (g := fun x : ℝ => x^2) (by norm_num))
  have hiY : Integrable (fun z => (dy φ.field z)^2) volume :=
    (φ.field.derivativeY.continuous.pow 2).integrable_of_hasCompactSupport (hcy.comp_left (g := fun x : ℝ => x^2) (by norm_num))
  have hiFprod := hiF
  have hiXprod := hiX
  have hiYprod := hiY
  rw [Measure.volume_eq_prod] at hiFprod hiXprod hiYprod
  have hx : (Real.pi/D.Lx)^2*(∫ z, (φ.field z)^2) ≤ ∫ z, (dx φ.field z)^2 := by
    rw [Measure.volume_eq_prod, integral_prod_symm _ hiFprod,
      integral_prod_symm _ hiXprod, ← integral_const_mul]
    exact integral_mono (hiFprod.integral_prod_right.const_mul _)
      hiXprod.integral_prod_right (test_slice_wirtinger_x D φ)
  have hy : (Real.pi/D.Ly)^2*(∫ z, (φ.field z)^2) ≤ ∫ z, (dy φ.field z)^2 := by
    rw [Measure.volume_eq_prod, integral_prod _ hiFprod,
      integral_prod _ hiYprod, ← integral_const_mul]
    exact integral_mono (hiFprod.integral_prod_left.const_mul _)
      hiYprod.integral_prod_left (test_slice_wirtinger_y D φ)
  have norm_eq_full (f : SmoothField) (hs : tsupport (⇑f) ⊆ D.openSet) :
      ‖SmoothField.toL2 D f‖^2 = ∫ z, (f z)^2 := by
    rw [norm_toL2_sq]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun hmem => hz (hs hmem)), zero_pow (by decide : 2≠0)]
  have hsx : tsupport (⇑φ.field.derivativeX) ⊆ D.openSet :=
    (tsupport_comp_subset (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0)) (by simp)
      (fderiv ℝ (⇑φ.field))).trans ((tsupport_fderiv_subset ℝ).trans φ.support_inside)
  have hsy : tsupport (⇑φ.field.derivativeY) ⊆ D.openSet :=
    (tsupport_comp_subset (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) (by simp)
      (fderiv ℝ (⇑φ.field))).trans ((tsupport_fderiv_subset ℝ).trans φ.support_inside)
  rw [norm_eq_full φ.field φ.support_inside, norm_eq_full φ.field.derivativeX hsx,
    norm_eq_full φ.field.derivativeY hsy]
  dsimp only [SmoothField.derivativeX_apply, SmoothField.derivativeY_apply]
  nlinarith


/-- 闭包生成元的有限线性组合仍是一个内部紧支光滑测试函数。
此处控制真实函数与导数的共同图，而不是普通 L² 密度。 -/
theorem span_test_has_test (D : Rect) (U : weakH1Graph D)
    (hspan : U ∈ Submodule.span ℝ (Set.range (fun φ : TestFunction D => smoothToWeakH1 D φ.field))) :
    ∃ φ : TestFunction D, smoothToWeakH1 D φ.field = U := by
  induction hspan using Submodule.span_induction with
  | mem U hU => exact hU
  | zero =>
    refine ⟨⟨0, HasCompactSupport.zero, ?_⟩, (smoothGraphLinear D).map_zero⟩
    simp
  | add U V hU hV ihU ihV =>
    rcases ihU with ⟨φ, rfl⟩
    rcases ihV with ⟨ψ, rfl⟩
    refine ⟨⟨φ.field+ψ.field, HasCompactSupport.add φ.compact ψ.compact, ?_⟩,
      (smoothGraphLinear D).map_add φ.field ψ.field⟩
    exact (tsupport_add _ _).trans (union_subset φ.support_inside ψ.support_inside)
  | smul c U hU ih =>
    rcases ih with ⟨φ, rfl⟩
    refine ⟨⟨c • φ.field, ?_, ?_⟩, (smoothGraphLinear D).map_smul c φ.field⟩
    · exact φ.compact.comp_left (g := fun x : ℝ => c*x) (by simp)
    · exact (tsupport_smul_subset_right (fun _ => c) (⇑φ.field)).trans φ.support_inside

/-- (5.1) 的真实 H₀¹ 矩形估计：两个方向的 π²/L² 相加。
图闭包的三个坐标连续，故测试函数估计合法传至所有 H₀¹ 元素。 -/
theorem weak_sharp_poincare_sum (D : Rect) (v : zeroBoundaryGraph D) :
    ((Real.pi/D.Lx)^2+(Real.pi/D.Ly)^2) * ‖v.val.val 0‖^2 ≤
      ‖v.val.val 1‖^2 + ‖v.val.val 2‖^2 := by
  have hspan : (Submodule.span ℝ (Set.range (fun φ : TestFunction D =>
      smoothToWeakH1 D φ.field)) : Set (weakH1Graph D)) ⊆
      {U | ((Real.pi/D.Lx)^2+(Real.pi/D.Ly)^2)*‖U.val 0‖^2 ≤
        ‖U.val 1‖^2+‖U.val 2‖^2} := by
    intro U hU
    rcases span_test_has_test D U hU with ⟨φ,rfl⟩
    exact test_sharp_poincare D φ
  have hcoord (i : Fin 3) : Continuous (fun U : weakH1Graph D => ‖U.val i‖^2) :=
    (((continuous_apply i).comp continuous_subtype_val).norm).pow 2
  have hclosed : IsClosed {U : weakH1Graph D |
      ((Real.pi/D.Lx)^2+(Real.pi/D.Ly)^2)*‖U.val 0‖^2 ≤ ‖U.val 1‖^2+‖U.val 2‖^2} :=
    isClosed_le (continuous_const.mul (hcoord 0)) ((hcoord 1).add (hcoord 2))
  exact closure_minimal hspan hclosed v.property

/-- V7 (5.1) 常数本身，取正平方根；保守 2Lx 定义仍保留。 -/
def sharpPoincareConstant (D : Rect) : ℝ :=
  Real.sqrt ((Real.pi^2/D.Lx^2+Real.pi^2/D.Ly^2)⁻¹)

/-- (5.1) 中分母严格正，来自非退化矩形与 π>0。 -/
theorem sharpPoincareDenominator_pos (D : Rect) : 0 < Real.pi^2/D.Lx^2+Real.pi^2/D.Ly^2 :=
  add_pos (div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos D.Lx_pos))
    (div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos D.Ly_pos))

/-- (5.1) 原常数的正性，供材料阈值使用。 -/
theorem sharpPoincareConstant_pos (D : Rect) : 0 < sharpPoincareConstant D :=
  Real.sqrt_pos.mpr (inv_pos.mpr (sharpPoincareDenominator_pos D))

/-- 原文精确 CP² 公式；没有用浮点近似。 -/
theorem sharpPoincareConstant_sq (D : Rect) : sharpPoincareConstant D^2 =
    (Real.pi^2/D.Lx^2+Real.pi^2/D.Ly^2)⁻¹ :=
  Real.sq_sqrt (inv_nonneg.mpr (sharpPoincareDenominator_pos D).le)

/-- (5.1) 以 CP² 形式用于真实弱 H₀¹，随后交给主能量参数入口。 -/
theorem weak_sharp_poincare (D : Rect) (v : zeroBoundaryGraph D) :
    ‖v.val.val 0‖^2 ≤ sharpPoincareConstant D^2*(‖v.val.val 1‖^2+‖v.val.val 2‖^2) := by
  have hsum := weak_sharp_poincare_sum D v
  rw [sharpPoincareConstant_sq, ← div_eq_inv_mul]
  apply (le_div_iff₀ (sharpPoincareDenominator_pos D)).mpr
  simpa only [div_pow, mul_comm] using hsum

/-- 真实弱梯度定义域中的 (5.1)，与 weakGreenDomain 使用相同零迹域。 -/
theorem weak_sharp_poincare_domain (D : Rect) (v : weakZeroFieldDomain D) :
    ‖v.val‖^2 ≤ sharpPoincareConstant D^2*
      (‖(weakZeroSpatialDomain D).componentX v‖^2+‖(weakZeroSpatialDomain D).componentY v‖^2) := by
  have hestimate := weak_sharp_poincare D (weakZeroLift D v)
  rw [weakZeroLift_value] at hestimate
  exact hestimate

/-- 已证精确矩形估计填入现有接口；调用者不提供 Poincaré 假设。 -/
def sharpWeakPoincareDomain (D : Rect) :
    LeanPML.PML.ConditionalPoincare (weakGreenDomain D).spatial (sharpPoincareConstant D) :=
  LeanPML.PML.ConditionalPoincare.ofGreenTrace (weakGreenDomain D) (sharpPoincareConstant D)
    (fun v _ => weak_sharp_poincare_domain D v)
end LeanPML.Rectangle
