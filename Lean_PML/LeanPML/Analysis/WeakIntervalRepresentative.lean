import LeanPML.Rectangle.SharpPoincare
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# 一维弱导数与连续代表：测试函数原函数

服务于 V7 §1 的分离 W¹,∞ 剖面。这里不假定弱函数经典可导。
先证明零均值内部紧支测试函数存在同类原函数，再将零弱导数转成
所有测试函数配对，从而应用 mathlib 的分布基本引理。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace LeanPML.Analysis

/-- 区间内部紧支的光滑零均值函数，有内部紧支的光滑原函数。
原文未单列；下游用于证明零弱导数的函数 a.e. 为常数。
零均值保证原函数在右端外也为零，不能省略。 -/
theorem exists_compact_primitive {a b : ℝ} (hab : a < b)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo a b) (hz : ∫ x, η x = 0) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ Ioo a b ∧ ∀ x, HasDerivAt F (η x) x := by
  by_cases hzero : η = 0
  · subst η
    exact ⟨0, contDiff_const, by simp [HasCompactSupport], by simp,
      fun x => by simpa using hasDerivAt_const x (0 : ℝ)⟩
  have hne : (tsupport η).Nonempty := by
    by_contra hempty
    have hs_empty : tsupport η = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    apply hzero
    exact Function.support_eq_empty_iff.mp
      (Set.eq_empty_of_subset_empty ((subset_tsupport η).trans (by rw [hs_empty])))
  obtain ⟨A,hA,hmin⟩ := hc.exists_isMinOn hne continuousOn_id
  obtain ⟨B,hB,hmax⟩ := hc.exists_isMaxOn hne continuousOn_id
  have hAB : A ≤ B := hmin hB
  have hsupport : tsupport η ⊆ Icc A B := fun x hx => ⟨hmin hx,hmax hx⟩
  let F : ℝ → ℝ := fun x => ∫ y in a..x, η y
  have hderiv (x : ℝ) : HasDerivAt F (η x) x :=
    intervalIntegral.integral_hasDerivAt_right (hη.continuous.intervalIntegrable a x)
      hη.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hη.continuous.continuousAt
  have hdiff : ContDiff ℝ ∞ F := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    have hident : deriv F = η := funext fun x => (hderiv x).deriv
    rw [hident]
    exact hη
  have hleft (x : ℝ) (hx : x < A) : F x = 0 := by
    have hends : a < A := (hs hA).1
    have heq : ∀ y ∈ uIcc a x, η y = 0 := by
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro hy_supp
      have hy_bound : y ≤ max a x := hy.2
      have hmax_lt : max a x < A := max_lt hends hx
      exact (not_lt_of_ge (hmin hy_supp)) (hy_bound.trans_lt hmax_lt)
    change (∫ y in a..x, η y) = 0
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
  have hright (x : ℝ) (hx : B < x) : F x = 0 := by
    change (∫ y in a..x, η y) = 0
    rw [intervalIntegral.integral_eq_integral_of_support_subset, hz]
    intro y hy
    have hys := subset_tsupport η hy
    exact ⟨(hs hys).1, (hmax hys).trans hx.le⟩
  have hFsupport : tsupport F ⊆ Icc A B := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hout
    simp only [mem_Icc, not_and_or, not_le] at hout
    rcases hout with h | h
    · exact hx (hleft x h)
    · exact hx (hright x h)
  refine ⟨F,hdiff,isCompact_Icc.of_isClosed_subset isClosed_closure hFsupport, ?_,hderiv⟩
  intro x hx
  exact ⟨(hs hA).1.trans_le (hFsupport hx).1,
    (hFsupport hx).2.trans_lt (hs hB).2⟩


/-- 在任意非空开区间内构造积分为一的真实光滑测试函数。
用于消去测试函数均值；不是假设存在所需代表。 -/
theorem exists_normalized_interval_test {a b : ℝ} (hab : a < b) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioo a b ∧ ∫ x, ρ x = 1 := by
  let bump : ContDiffBump ((a+b)/2) :=
    { rIn := (b-a)/8
      rOut := (b-a)/4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨bump.normed volume, bump.contDiff_normed, bump.hasCompactSupport_normed, ?_,
    bump.integral_normed⟩
  rw [bump.tsupport_normed_eq]
  intro x hx
  have hdist : |x-(a+b)/2| ≤ (b-a)/4 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, bump] using hx
  have hboth := abs_le.mp hdist
  constructor <;> linarith

/-- 零弱导数意味着区间内 a.e. 为常数。
输入只含局部可积性和对真实光滑测试函数导数的配对；
先用零均值原函数把导数测试转为一般测试，再用分布基本引理。
函数的全轴局部可积性可由区域有界函数的零延拓提供，不要求全轴 PDE。 -/
theorem ae_constant_of_weak_derivative_zero {a b : ℝ} (hab : a < b)
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b → ∫ x, deriv η x * f x = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, x ∈ Ioo a b → f x = c := by
  obtain ⟨ρ,hρ,hρc,hρs,hρint⟩ := exists_normalized_interval_test hab
  let c : ℝ := ∫ x, ρ x*f x
  have hpair (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η)
      (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo a b) :
      (∫ x, η x*f x) = (∫ x, η x)*c := by
    let M : ℝ := ∫ x, η x
    let ζ : ℝ → ℝ := fun x => η x-M*ρ x
    have hζ : ContDiff ℝ ∞ ζ := hη.sub (contDiff_const.mul hρ)
    have hζc : HasCompactSupport ζ := hc.sub hρc.mul_left
    have hζs : tsupport ζ ⊆ Ioo a b := by
      have hsub : Function.support ζ ⊆ tsupport η ∪ tsupport ρ := by
        intro x hx
        by_contra hout
        have hn : x ∉ tsupport η ∧ x ∉ tsupport ρ := by simpa using hout
        exact hx (by simp [ζ, image_eq_zero_of_notMem_tsupport hn.1,
          image_eq_zero_of_notMem_tsupport hn.2])
      exact (closure_minimal hsub (isClosed_closure.union isClosed_closure)).trans
        (union_subset hs hρs)
    have hζzero : ∫ x, ζ x = 0 := by
      rw [integral_sub (hη.continuous.integrable_of_hasCompactSupport hc)
        ((hρ.continuous.integrable_of_hasCompactSupport hρc).const_mul M)]
      rw [integral_const_mul,hρint,mul_one]
      exact sub_self _
    obtain ⟨F,hF,hFc,hFs,hFd⟩ := exists_compact_primitive hab ζ hζ hζc hζs hζzero
    have hzero := hweak F hF hFc hFs
    have hderiv : deriv F = ζ := funext fun x => (hFd x).deriv
    rw [hderiv] at hzero
    have hiη : Integrable (fun x => η x*f x) :=
      hf.integrable_smul_left_of_hasCompactSupport hη.continuous hc
    have hiρ : Integrable (fun x => ρ x*f x) :=
      hf.integrable_smul_left_of_hasCompactSupport hρ.continuous hρc
    have heq : (fun x => ζ x*f x) = fun x => η x*f x-M*(ρ x*f x) := by
      funext x; dsimp [ζ]; ring
    rw [heq,integral_sub hiη (hiρ.const_mul M),integral_const_mul] at hzero
    exact sub_eq_zero.mp hzero
  refine ⟨c, ?_⟩
  have hconst : ∀ᵐ x ∂volume, x ∈ Ioo a b → f x-c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.sub continuous_const.locallyIntegrable).locallyIntegrableOn (s := Ioo a b))
    intro η hη hc hs
    have hiη : Integrable (fun x => η x*f x) :=
      hf.integrable_smul_left_of_hasCompactSupport hη.continuous hc
    have hηi := hη.continuous.integrable_of_hasCompactSupport (μ := volume) hc
    simp only [smul_eq_mul, Pi.sub_apply]
    simp_rw [mul_sub]
    rw [integral_sub hiη (hηi.mul_const c),integral_mul_const,hpair η hη hc hs,sub_self]
  filter_upwards [hconst] with x hx
  exact fun hxin => sub_eq_zero.mp (hx hxin)


/-- 局部可积函数在每个有限区间可积；为真实积分原函数提供合法性。 -/
theorem locallyIntegrable_interval (d : ℝ → ℝ) (hd : LocallyIntegrable d volume)
    (a b : ℝ) : IntervalIntegrable d volume a b :=
  intervalIntegrable_iff.mpr
    ((hd.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

/-- 积分原函数的弱导数确实为 d。
这一步对 d 只要求局部可积：Lebesgue 微分定理给 a.e. 导数，
绝对连续积分分部合法转移导数；没有套用要求处处可导的 FTC。 -/
theorem integral_primitive_weak_derivative {a b : ℝ} (hab : a < b)
    (d : ℝ → ℝ) (hd : LocallyIntegrable d volume)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo a b) :
    (∫ x, deriv η x * (∫ y in a..x, d y)) = -(∫ x, η x*d x) := by
  let F : ℝ → ℝ := fun x => ∫ y in a..x, d y
  have hF_ac : AbsolutelyContinuousOnInterval F a b :=
    (locallyIntegrable_interval d hd a b).absolutelyContinuousOnInterval_intervalIntegral
      (left_mem_uIcc)
  have hη_ac : AbsolutelyContinuousOnInterval η a b :=
    (hη.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hηa : η a = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl a) (hs h).1)
  have hηb : η b = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl b) (hs h).2)
  have hparts := hη_ac.integral_mul_deriv_eq_deriv_mul hF_ac
  have hderiv : deriv F =ᵐ[volume] d := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hd] with x hx
    exact (hx a).deriv
  have hident : (∫ x in a..b, η x * deriv F x) = ∫ x in a..b, η x*d x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with x hx
    exact fun _ => by rw [hx]
  rw [hident,hηa,hηb,zero_mul,zero_mul,sub_self,zero_sub] at hparts
  have hsη : Function.support (fun x => η x*d x) ⊆ Ioc a b := by
    intro x hx
    have hmem : x ∈ tsupport η := subset_tsupport η (by
      intro hzero; exact hx (by simp [hzero]))
    exact ⟨(hs hmem).1,(hs hmem).2.le⟩
  have hsη' : Function.support (fun x => deriv η x*F x) ⊆ Ioc a b := by
    intro x hx
    have hmem : x ∈ tsupport η := support_deriv_subset (by
      intro hzero; exact hx (by simp [hzero]))
    exact ⟨(hs hmem).1,(hs hmem).2.le⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsη,
    intervalIntegral.integral_eq_integral_of_support_subset hsη'] at hparts
  linarith

/-- 一维弱导数的积分表示。V7 分离系数连续代表构造的核心步骤。
输入是测试配对，不是普通导数；输出在区间内 a.e. 等于积分原函数加常数。
局部可积性可由区域有界函数的零延拓满足。 -/
theorem ae_eq_integral_primitive_of_weak_derivative {a b : ℝ} (hab : a < b)
    (f d : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hd : LocallyIntegrable d volume)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b → (∫ x, deriv η x*f x) = -(∫ x, η x*d x)) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, x ∈ Ioo a b → f x = c + ∫ y in a..x, d y := by
  let F : ℝ → ℝ := fun x => ∫ y in a..x, d y
  have hF : Continuous F := intervalIntegral.continuous_primitive (locallyIntegrable_interval d hd) a
  obtain ⟨c,hc⟩ := ae_constant_of_weak_derivative_zero hab (fun x => f x-F x)
    (hf.sub hF.locallyIntegrable) (by
      intro η hη hcompact hs
      have hderiv_cont : Continuous (deriv η) := hη.continuous_deriv (by simp)
      have hi1 : Integrable (fun x => deriv η x*f x) :=
        hf.integrable_smul_left_of_hasCompactSupport hderiv_cont hcompact.deriv
      have hi2 : Integrable (fun x => deriv η x*F x) :=
        hF.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hderiv_cont hcompact.deriv
      simp_rw [mul_sub]
      rw [integral_sub hi1 hi2, hweak η hη hcompact hs,
        integral_primitive_weak_derivative hab d hd η hη hcompact hs, sub_self])
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  intro hxin
  have hdiff := hx hxin
  change f x = c + F x
  linarith


/-- 有界导数的积分原函数是 Lipschitz；只用真实积分差与积分范数界。
这里 d 可取区域导数的零延拓，域外不要求物理幅度条件。 -/
theorem lipschitz_integral_primitive (d : ℝ → ℝ) (hd : LocallyIntegrable d volume)
    (C : NNReal) (hbound : ∀ᵐ x ∂volume, ‖d x‖ ≤ C) (a c : ℝ) :
    LipschitzWith C (fun x => c + ∫ y in a..x, d y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left
      (locallyIntegrable_interval d hd a x) (locallyIntegrable_interval d hd a y)]
  simpa only [Real.norm_eq_abs, Real.dist_eq] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := y) (b := x) (hbound.mono fun z hz _ => hz)

/-- 从真实弱导数获得 a.e. 相等的 Lipschitz 代表，包含闭端点的连续延拓。
未预设代表存在；构造是前述积分原函数加已推出的常数。 -/
theorem exists_lipschitz_representative {a b : ℝ} (hab : a < b)
    (f d : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hd : LocallyIntegrable d volume)
    (C : NNReal) (hbound : ∀ᵐ x ∂volume, ‖d x‖ ≤ C)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b → (∫ x, deriv η x*f x) = -(∫ x, η x*d x)) :
    ∃ F : ℝ → ℝ, LipschitzWith C F ∧
      f =ᵐ[volume.restrict (Ioo a b)] F := by
  obtain ⟨c,hrep⟩ := ae_eq_integral_primitive_of_weak_derivative hab f d hf hd hweak
  refine ⟨fun x => c + ∫ y in a..x, d y,
    lipschitz_integral_primitive d hd C hbound a c, ?_⟩
  exact (ae_restrict_iff' measurableSet_Ioo).mpr hrep

/-- 原区域的非负和幅度 a.e. 界传给连续代表的整个闭区间。
端点由连续性/闭包得到，不在 L² 商类中读取端点值。 -/
theorem continuous_representative_bounds {a b S : ℝ} (hab : a < b) (hS : 0 ≤ S)
    (f F : ℝ → ℝ) (hF : Continuous F)
    (hrep : f =ᵐ[volume.restrict (Ioo a b)] F)
    (hf_bounds : ∀ᵐ x ∂volume.restrict (Ioo a b), 0 ≤ f x ∧ f x ≤ S) :
    ∀ x ∈ Icc a b, 0 ≤ F x ∧ F x ≤ S := by
  let G : ℝ → ℝ := fun x => max 0 (min S (F x))
  have hG : Continuous G := continuous_const.max (continuous_const.min hF)
  have heq_ae : F =ᵐ[volume.restrict (Ioo a b)] G := by
    filter_upwards [hrep,hf_bounds] with x hx hb
    dsimp [G]
    rw [← hx,min_eq_right hb.2,max_eq_right hb.1]
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq heq_ae isOpen_Ioo
    hF.continuousOn hG.continuousOn
  have hinside : Ioo a b ⊆ {x | 0 ≤ F x ∧ F x ≤ S} := by
    intro x hx
    change 0 ≤ F x ∧ F x ≤ S
    rw [heq hx]
    exact ⟨le_max_left _ _, max_le hS (min_le_left _ _)⟩
  have hclosed : IsClosed {x | 0 ≤ F x ∧ F x ≤ S} :=
    (isClosed_le continuous_const hF).inter (isClosed_le hF continuous_const)
  have hclosure := closure_minimal hinside hclosed
  rw [closure_Ioo hab.ne] at hclosure
  exact hclosure


/-- 区域有界可测函数的零延拓可积。只用于一维代表构造，
不把跨端点的零延拓声称为原弱导数的全轴延拓。 -/
theorem integrable_interval_extension {a b C : ℝ} (f : ℝ → ℝ)
    (hm : Measurable f) (hbound : ∀ x ∈ Ioo a b, ‖f x‖ ≤ C) :
    Integrable ((Ioo a b).indicator f) volume := by
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  apply Measure.integrableOn_of_bounded (by simp) hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hbound x hx

/-- 完全区域化的一维 W¹,∞ 代表构造。
弱导数输入仅对 (a,b) 上的积分；幅度仅在该区间，域外任意。
内部零延拓后调用已证积分表示，得到原 f 的 a.e. 相等 Lipschitz 代表。 -/
theorem exists_regional_lipschitz_representative {a b : ℝ} (hab : a < b)
    (f d : ℝ → ℝ) (hf : Measurable f) (hd : Measurable d)
    (B : ℝ) (C : NNReal)
    (hf_bound : ∀ x ∈ Ioo a b, ‖f x‖ ≤ B)
    (hd_bound : ∀ x ∈ Ioo a b, ‖d x‖ ≤ C)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b →
      (∫ x in Ioo a b, deriv η x*f x) = -(∫ x in Ioo a b, η x*d x)) :
    ∃ F : ℝ → ℝ, LipschitzWith C F ∧ f =ᵐ[volume.restrict (Ioo a b)] F := by
  let ef := (Ioo a b).indicator f
  let ed := (Ioo a b).indicator d
  have hfi : Integrable ef volume := integrable_interval_extension f hf hf_bound
  have hdi : Integrable ed volume := integrable_interval_extension d hd hd_bound
  have hd_global : ∀ᵐ x ∂volume, ‖ed x‖ ≤ C := by
    filter_upwards [] with x
    by_cases hx : x ∈ Ioo a b
    · simpa [ed,hx] using hd_bound x hx
    · simp [ed,hx]
  have hpair : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b → (∫ x, deriv η x*ef x) = -(∫ x, η x*ed x) := by
    intro η hη hc hs
    have heqf : (fun x => deriv η x*ef x) = (Ioo a b).indicator (fun x => deriv η x*f x) := by
      funext x; by_cases hx : x ∈ Ioo a b <;> simp [ef,hx]
    have heqd : (fun x => η x*ed x) = (Ioo a b).indicator (fun x => η x*d x) := by
      funext x; by_cases hx : x ∈ Ioo a b <;> simp [ed,hx]
    rw [heqf,heqd,integral_indicator measurableSet_Ioo,integral_indicator measurableSet_Ioo]
    exact hweak η hη hc hs
  obtain ⟨F,hLip,hrep⟩ := exists_lipschitz_representative hab ef ed hfi.locallyIntegrable
    hdi.locallyIntegrable C hd_global hpair
  refine ⟨F,hLip, ?_⟩
  filter_upwards [hrep,ae_restrict_mem measurableSet_Ioo] with x hx hxin
  simpa [ef,hxin] using hx

end LeanPML.Analysis
