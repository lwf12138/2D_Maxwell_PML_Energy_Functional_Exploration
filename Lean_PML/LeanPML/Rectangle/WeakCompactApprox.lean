import LeanPML.PML.WeakCoefficients
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Thickening

/-!
# 内部粗糙弱场的光滑化：实际 L² 收敛步骤

服务于区域 W¹,∞ 乘 H₀¹ 的零迹保持。归一化卷积核是真实 C∞ 函数；
其收敛先由 mathlib Lebesgue 微分定理给出 a.e. 收敛，再以统一界支配平方差。
本文件还给出内部紧支、真实卷积求导及缩核序列；下游 WeakZeroProduct
将区域弱导数转移到核上，组合为同一光滑序列的 H¹ 图逼近。
-/
noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
open LeanPML.Analysis
namespace LeanPML.Rectangle

local instance rectangleVolumeHaar : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  infer_instance

/-- 归一化紧支卷积核作用于局部可积函数，产生实际光滑函数。
来源：mathlib 卷积求导；不假设原函数经典可导。 -/
def mollifiedField (ρ : ContDiffBump (0 : ℝ × ℝ))
    (g : ℝ × ℝ → ℝ) (hg : LocallyIntegrable g volume) : SmoothField :=
  ⟨ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g,
    ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (ρ.contDiff.div_const _) hg⟩

/-- 归一化非负卷积核保留全局幅度界；用于平方差的可积支配函数。
这里需要的是原有界代表的界，不是能量权重 w 的有界性。 -/
theorem mollifiedField_norm_le (ρ : ContDiffBump (0 : ℝ × ℝ))
    (g : ℝ × ℝ → ℝ) (hg : LocallyIntegrable g volume)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖g x‖ ≤ C) (x : ℝ × ℝ) :
    ‖mollifiedField ρ g hg x‖ ≤ C := by
  have hdist := MeasureTheory.dist_convolution_le (μ := volume) (g := g)
    (x₀ := x) (z₀ := (0 : ℝ)) hC ρ.support_normed_eq.subset
    ρ.nonneg_normed ρ.integral_normed hg.aestronglyMeasurable
    (fun y _ => by simpa using hbound y)
  simpa only [dist_zero_right, mollifiedField] using hdist

/-- 实际矩形 L² 的支配收敛桥接：极限可以只是 L² 商类，未要求光滑。
Fₙ 的统一有界性与 a.e. 收敛共同控制平方差，而非只调用普通函数密度。 -/
theorem smoothToL2_tendsto_of_bounded_ae (D : Rect) (F : ℕ → SmoothField)
    (g : ScalarL2 D.measure) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n x, ‖F n x‖ ≤ C)
    (hgbound : ∀ᵐ x ∂D.measure, ‖g x‖ ≤ C)
    (hconv : ∀ᵐ x ∂D.measure, Tendsto (fun n => F n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => SmoothField.toL2 D (F n)) atTop (𝓝 g) := by
  have hdominated : ∀ n, ∀ᵐ x ∂D.measure, ‖(F n x-g x)^2‖ ≤ (2*C)^2 := by
    intro n
    filter_upwards [hgbound] with x hgx
    have hnorm : ‖F n x-g x‖ ≤ 2*C :=
      (norm_sub_le _ _).trans (by linarith [hbound n x])
    rw [norm_pow]
    nlinarith [norm_nonneg (F n x-g x)]
  have hpointwise : ∀ᵐ x ∂D.measure,
      Tendsto (fun n => (F n x-g x)^2) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hconv] with x hx
    simpa using (hx.sub (tendsto_const_nhds (x := g x))).pow 2
  have hintegral := tendsto_integral_of_dominated_convergence
    (μ := D.measure) (fun _ => (2*C)^2)
    (fun n => (((F n).continuous.aestronglyMeasurable.sub (Lp.memLp g).aestronglyMeasurable).pow 2))
    (integrable_const _) hdominated hpointwise
  have hsquare : Tendsto (fun n => ‖SmoothField.toL2 D (F n)-g‖^2)
      atTop (𝓝 (0:ℝ)) := by
    have heq (n : ℕ) : ‖SmoothField.toL2 D (F n)-g‖^2 =
        ∫ x, (F n x-g x)^2 ∂D.measure := by
      rw [norm_sq_eq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (SmoothField.toL2 D (F n)) g,
        SmoothField.coe_toL2 D (F n)] with x hsub hF
      simp only [hsub, Pi.sub_apply, hF]
    simp only [integral_zero] at hintegral
    exact hintegral.congr' (Eventually.of_forall fun n => (heq n).symm)
  have hnorm := (Real.continuous_sqrt.tendsto 0).comp hsquare
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hnorm

/-- 缩小归一化 bump 对有界局部可积代表在矩形 L² 中真正收敛。
核的内外半径比保持有界，正是 mathlib a.e. Lebesgue 微分定理的条件。
下游对粗糙乘积及两弱偏导分别调用，再以已证核测试公式识别卷积偏导。 -/
theorem mollifiedField_toL2_tendsto (D : Rect)
    (ρ : ℕ → ContDiffBump (0 : ℝ × ℝ))
    (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hratio : ∀ᶠ n in atTop, (ρ n).rOut ≤ K*(ρ n).rIn)
    (g : ℝ × ℝ → ℝ) (hg : LocallyIntegrable g volume)
    (v : ScalarL2 D.measure) (hrep : g =ᵐ[D.measure] ⇑v)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖g x‖ ≤ C) :
    Tendsto (fun n => SmoothField.toL2 D (mollifiedField (ρ n) g hg)) atTop (𝓝 v) := by
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hρ hratio hg
  apply smoothToL2_tendsto_of_bounded_ae D _ v hC
    (fun n x => mollifiedField_norm_le (ρ n) g hg hC hbound x)
  · filter_upwards [hrep] with x hx
    rw [← hx]
    exact hbound x
  · filter_upwards [ae_restrict_of_ae hae, hrep] with x hx hrep_x
    simpa only [mollifiedField, hrep_x] using hx

/-- 内部紧支粗糙函数卷积后仍严格内部紧支，只要核半径小于支撑的边界余量。
余量由紧致性与 Ω 开性推出，不作为外加的逼近假设。 -/
theorem mollifiedField_support_inside (D : Rect) (g : ℝ × ℝ → ℝ)
    (hg : LocallyIntegrable g volume) (hc : HasCompactSupport g)
    (hinside : tsupport g ⊆ D.openSet) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ContDiffBump (0 : ℝ × ℝ), ρ.rOut ≤ δ →
      HasCompactSupport (⇑(mollifiedField ρ g hg)) ∧
      tsupport (⇑(mollifiedField ρ g hg)) ⊆ D.openSet := by
  obtain ⟨δ, hδ, hthick⟩ := hc.isCompact.exists_cthickening_subset_open D.openSet_open hinside
  refine ⟨δ, hδ, fun ρ hρ => ⟨ρ.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hc, ?_⟩⟩
  apply (closure_minimal ?_ (Metric.isClosed_cthickening)).trans hthick
  intro x hx
  have hsupport := MeasureTheory.support_convolution_subset_swap (L := lsmul ℝ ℝ) (μ := volume) hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hsupport
  have hz_norm : ‖z‖ < ρ.rOut := by
    simpa only [ρ.support_normed_eq, Metric.mem_ball, dist_zero_right] using hz
  apply Metric.mem_cthickening_of_dist_le (y+z) y δ (tsupport g) (subset_closure hy)
  simpa only [dist_eq_norm, add_sub_cancel_left] using hz_norm.le.trans hρ

/-- 卷积的真实方向导数等于对光滑核求导后的积分。
这一步仅调用 mathlib 的实际 Fréchet 导数；弱导数转移需要另证测试配对恒等式。 -/
theorem mollifiedField_fderiv (ρ : ContDiffBump (0 : ℝ × ℝ))
    (g : ℝ × ℝ → ℝ) (hg : LocallyIntegrable g volume) (x v : ℝ × ℝ) :
    fderiv ℝ (⇑(mollifiedField ρ g hg)) x v =
      ∫ y, g y * fderiv ℝ (ρ.normed volume) (x-y) v := by
  have hkernel : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff.div_const _
  have hswap : (⇑(mollifiedField ρ g hg)) =
      g ⋆[lsmul ℝ ℝ, volume] (ρ.normed volume) := by
    funext z
    change (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z = _
    rw [MeasureTheory.convolution_eq_swap]
    simp only [MeasureTheory.convolution_def, lsmul_apply, smul_eq_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => mul_comm _ _
  rw [hswap]
  have hderiv := ρ.hasCompactSupport_normed.hasFDerivAt_convolution_right
    (lsmul ℝ ℝ) hg (hkernel.of_le (by simp)) x
  rw [hderiv.fderiv]
  rw [MeasureTheory.convolution_precompR_apply (lsmul ℝ ℝ) hg
    (ρ.hasCompactSupport_normed.fderiv ℝ) (hkernel.continuous_fderiv (by simp))]
  rfl

/-- 平移并反射的光滑核，作为粗糙弱导数的实际测试探针。 -/
def reflectedSmooth (k : SmoothField) (x : ℝ × ℝ) : SmoothField :=
  ⟨fun y => k (x-y), k.contDiff.comp (contDiff_const.sub contDiff_id)⟩

/-- 核反射产生负号；通过实际 Fréchet 链式法则证明。 -/
theorem smoothPartial_reflected (k : SmoothField) (x y : ℝ × ℝ) (i : Fin 2) :
    smoothPartial i (reflectedSmooth k x) y = -smoothPartial i k (x-y) := by
  have hmap : HasFDerivAt (fun z : ℝ × ℝ => x-z)
      (0 - ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_const x y).sub (hasFDerivAt_id y)
  have hcomp := (k.differentiable (x-y)).hasFDerivAt.comp y hmap
  fin_cases i
  · change fderiv ℝ (fun z => k (x-z)) y (1,0) = -fderiv ℝ (⇑k) (x-y) (1,0)
    simpa [Function.comp_def] using congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0)) hcomp.fderiv
  · change fderiv ℝ (fun z => k (x-z)) y (0,1) = -fderiv ℝ (⇑k) (x-y) (0,1)
    simpa [Function.comp_def] using congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) hcomp.fderiv

/-- 选定一组真正缩小的光滑核，内半径始终为外半径的一半。 -/
def shrinkingMollifier (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := (δ/((n:ℝ)+1))/2
  rOut := δ/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hpositive : 0 < δ/((n:ℝ)+1) := by positivity
    linarith

/-- 核半径趋于零且不超过已构造的边界余量；用于实际内部测试逼近。 -/
theorem shrinkingMollifier_properties (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (shrinkingMollifier δ hδ n).rOut) atTop (𝓝 0) ∧
    (∀ n, (shrinkingMollifier δ hδ n).rOut ≤ δ) ∧
    (∀ n, (shrinkingMollifier δ hδ n).rOut ≤ 2*(shrinkingMollifier δ hδ n).rIn) := by
  refine ⟨?_, ?_, ?_⟩
  · have ht := (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0)).const_mul δ
    simpa [shrinkingMollifier, div_eq_mul_inv] using ht
  · intro n
    exact div_le_self hδ.le (by have : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
  · intro n
    dsimp [shrinkingMollifier]
    linarith

end LeanPML.Rectangle
