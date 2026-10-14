import LeanPML.Rectangle.WeakPoincare
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
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
end LeanPML.Rectangle
