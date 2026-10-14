import LeanPML.Analysis.WeakIntervalRepresentative
import LeanPML.PML.SeparatedWeakCoefficients

/-!
# 二维分离弱系数到一维分布关系

V7 §1 的 p(x)、r(y) 从实际区域弱偏导定义出发。
以 η(x)ρ(y) 为二维紧支测试，归一化横向积分取得一维弱导数。
所有积分先由区域有界性和光滑测试函数证明可积，再调用 Fubini。
本文件不对无界能量权重求导，也不要求系数全轴物理幅度。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

/-- 两个一维实际光滑函数的张量测试场，偏导由切片求导验证。 -/
def tensorField (η ρ : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hρ : ContDiff ℝ ∞ ρ) :
    SmoothField := ⟨fun z => η z.1*ρ z.2, (hη.comp contDiff_fst).mul (hρ.comp contDiff_snd)⟩

/-- 张量函数的拓扑支撑落在两支撑的乘积中；下游保证严格域内紧支。 -/
theorem tensorField_support (η ρ : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hρ : ContDiff ℝ ∞ ρ) :
    tsupport (⇑(tensorField η ρ hη hρ)) ⊆ tsupport η ×ˢ tsupport ρ := by
  apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
  intro z hz
  have hnonzero : η z.1*ρ z.2 ≠ 0 := hz
  exact ⟨subset_tsupport η (mul_ne_zero_iff.mp hnonzero).1,
    subset_tsupport ρ (mul_ne_zero_iff.mp hnonzero).2⟩

/-- 内部紧支一维测试构成当前矩形弱导数定义允许的真实二维测试。 -/
def tensorTest (D : Rect) (η ρ : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hρ : ContDiff ℝ ∞ ρ)
    (hcη : HasCompactSupport η) (hcρ : HasCompactSupport ρ)
    (hsη : tsupport η ⊆ Ioo D.xlo D.xhi) (hsρ : tsupport ρ ⊆ Ioo D.ylo D.yhi) :
    TestFunction D where
  field := tensorField η ρ hη hρ
  compact := (hcη.prod hcρ).of_isClosed_subset isClosed_closure
    (tensorField_support η ρ hη hρ)
  support_inside := (tensorField_support η ρ hη hρ).trans (prod_mono hsη hsρ)

/-- x 偏导是真实的 η′(x)ρ(y)，不是给函数改名。 -/
theorem tensorField_dx (η ρ : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hρ : ContDiff ℝ ∞ ρ)
    (z : ℝ × ℝ) : dx (tensorField η ρ hη hρ) z = deriv η z.1 * ρ z.2 := by
  have hslice := ((hη.differentiable (by simp) z.1).hasDerivAt).mul_const (ρ z.2)
  exact ((tensorField η ρ hη hρ).hasDerivAt_sliceX z).unique hslice

/-- y 偏导是真实的 η(x)ρ′(y)，不是给函数改名。 -/
theorem tensorField_dy (η ρ : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hρ : ContDiff ℝ ∞ ρ)
    (z : ℝ × ℝ) : dy (tensorField η ρ hη hρ) z = η z.1 * deriv ρ z.2 := by
  have hslice := ((hρ.differentiable (by simp) z.2).hasDerivAt).const_mul (η z.1)
  exact ((tensorField η ρ hη hρ).hasDerivAt_sliceY z).unique hslice

/-- 将已有弱偏导的 L² 内积等式写回真实区域积分。
两个乘积可积由 integrable_regional_smooth 提供；不读取商类的固定点。 -/
theorem regional_weak_partial_integral (D : Rect) (m : RegionalWeakCoefficient D)
    (i : Fin 2) (φ : TestFunction D) :
    (∫ z, m.value.value z * smoothPartial i φ.field z ∂D.measure) =
      -(∫ z, (m.derivative i).value z * φ.field z ∂D.measure) := by
  have hw := m.weak_partial i φ
  rw [inner_eq_integral,inner_eq_integral] at hw
  have hleft : (∫ z, (m.derivative i).toL2 z * SmoothField.toL2 D φ.field z ∂D.measure) =
      ∫ z, (m.derivative i).value z * φ.field z ∂D.measure := by
    apply integral_congr_ae
    filter_upwards [(m.derivative i).coe_toL2,SmoothField.coe_toL2 D φ.field] with z hz hφ
    rw [hz,hφ]
  have hright : (∫ z, m.value.toL2 z * SmoothField.toL2 D (smoothPartial i φ.field) z ∂D.measure) =
      ∫ z, m.value.value z * smoothPartial i φ.field z ∂D.measure := by
    apply integral_congr_ae
    filter_upwards [m.value.coe_toL2,SmoothField.coe_toL2 D (smoothPartial i φ.field)] with z hz hφ
    rw [hz,hφ]
  rw [hleft,hright] at hw
  linarith

/-- 归一化横截面平均的真实函数。导数代表可以二维依赖；不偷加它也分离的假设。 -/
def averagedDerivativeX (D : Rect) (m : RegionalWeakCoefficient D) (ρ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Ioo D.ylo D.yhi, (m.derivative 0).value (x,y)*ρ y

/-- 二维弱偏导经真实 Fubini 推出一维剖面的弱导数关系。
ρ 的积分为1是所选测试核的已证性质，后续构造会实际提供它。 -/
theorem separated_weak_derivative_x (D : Rect) (m : RegionalWeakCoefficient D)
    (p : ℝ → ℝ) (hsep : ∀ z ∈ D.openSet, m.value.value z = p z.1)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hsρ : tsupport ρ ⊆ Ioo D.ylo D.yhi)
    (hρint : (∫ y in Ioo D.ylo D.yhi, ρ y) = 1)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Ioo D.xlo D.xhi) :
    (∫ x in Ioo D.xlo D.xhi, deriv η x*p x) =
      -(∫ x in Ioo D.xlo D.xhi, η x*averagedDerivativeX D m ρ x) := by
  let φ := tensorTest D η ρ hη hρ hcη hcρ hsη hsρ
  have hweak := regional_weak_partial_integral D m 0 φ
  have hleft_integrable : Integrable (fun z => m.value.value z * smoothPartial 0 φ.field z) D.measure :=
    integrable_regional_smooth D m.value (smoothPartial 0 φ.field)
  have hright_integrable : Integrable (fun z => (m.derivative 0).value z * φ.field z) D.measure :=
    integrable_regional_smooth D (m.derivative 0) φ.field
  rw [D.integral_fubini _ hleft_integrable,D.integral_fubini _ hright_integrable] at hweak
  have hleft : (∫ x in Ioo D.xlo D.xhi, ∫ y in Ioo D.ylo D.yhi,
      m.value.value (x,y) * smoothPartial 0 φ.field (x,y)) =
      ∫ x in Ioo D.xlo D.xhi, deriv η x*p x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hinner : (∫ y in Ioo D.ylo D.yhi,
        m.value.value (x,y)*smoothPartial 0 φ.field (x,y)) =
        ∫ y in Ioo D.ylo D.yhi, (deriv η x*p x)*ρ y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      rw [hsep (x,y) ⟨hx,hy⟩]
      change p x * dx (tensorField η ρ hη hρ) (x,y) = _
      rw [tensorField_dx]
      ring
    rw [hinner,integral_const_mul,hρint,mul_one]
  have hright : (∫ x in Ioo D.xlo D.xhi, ∫ y in Ioo D.ylo D.yhi,
      (m.derivative 0).value (x,y)*φ.field (x,y)) =
      ∫ x in Ioo D.xlo D.xhi, η x*averagedDerivativeX D m ρ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    change (∫ y in Ioo D.ylo D.yhi, (m.derivative 0).value (x,y)*(η x*ρ y)) = _
    simp_rw [show ∀ y, (m.derivative 0).value (x,y)*(η x*ρ y) =
      η x*((m.derivative 0).value (x,y)*ρ y) by intro y; ring]
    rw [integral_const_mul]
    rfl
  rwa [hleft,hright] at hweak

/-- 归一化横截面平均的真实函数。导数代表可以二维依赖；不偷加它也分离的假设。 -/
def averagedDerivativeY (D : Rect) (m : RegionalWeakCoefficient D) (ρ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Ioo D.xlo D.xhi, (m.derivative 1).value (y,x)*ρ y

/-- 二维弱偏导经真实 Fubini 推出一维剖面的弱导数关系。
ρ 的积分为1是所选测试核的已证性质，后续构造会实际提供它。 -/
theorem separated_weak_derivative_y (D : Rect) (m : RegionalWeakCoefficient D)
    (p : ℝ → ℝ) (hsep : ∀ z ∈ D.openSet, m.value.value z = p z.2)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hsρ : tsupport ρ ⊆ Ioo D.xlo D.xhi)
    (hρint : (∫ y in Ioo D.xlo D.xhi, ρ y) = 1)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Ioo D.ylo D.yhi) :
    (∫ x in Ioo D.ylo D.yhi, deriv η x*p x) =
      -(∫ x in Ioo D.ylo D.yhi, η x*averagedDerivativeY D m ρ x) := by
  let φ := tensorTest D ρ η hρ hη hcρ hcη hsρ hsη
  have hweak := regional_weak_partial_integral D m 1 φ
  have hleft_integrable : Integrable (fun z => m.value.value z * smoothPartial 1 φ.field z) D.measure :=
    integrable_regional_smooth D m.value (smoothPartial 1 φ.field)
  have hright_integrable : Integrable (fun z => (m.derivative 1).value z * φ.field z) D.measure :=
    integrable_regional_smooth D (m.derivative 1) φ.field
  rw [D.measure_eq_prod] at hleft_integrable hright_integrable hweak
  rw [integral_prod_symm _ hleft_integrable,integral_prod_symm _ hright_integrable] at hweak
  have hleft : (∫ x in Ioo D.ylo D.yhi, ∫ y in Ioo D.xlo D.xhi,
      m.value.value (y,x) * smoothPartial 1 φ.field (y,x)) =
      ∫ x in Ioo D.ylo D.yhi, deriv η x*p x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hinner : (∫ y in Ioo D.xlo D.xhi,
        m.value.value (y,x)*smoothPartial 1 φ.field (y,x)) =
        ∫ y in Ioo D.xlo D.xhi, (deriv η x*p x)*ρ y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      rw [hsep (y,x) ⟨hy,hx⟩]
      change p x * dy (tensorField ρ η hρ hη) (y,x) = _
      rw [tensorField_dy]
      ring
    rw [hinner,integral_const_mul,hρint,mul_one]
  have hright : (∫ x in Ioo D.ylo D.yhi, ∫ y in Ioo D.xlo D.xhi,
      (m.derivative 1).value (y,x)*φ.field (y,x)) =
      ∫ x in Ioo D.ylo D.yhi, η x*averagedDerivativeY D m ρ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    change (∫ y in Ioo D.xlo D.xhi, (m.derivative 1).value (y,x)*(ρ y*η x)) = _
    simp_rw [show ∀ y, (m.derivative 1).value (y,x)*(ρ y*η x) =
      η x*((m.derivative 1).value (y,x)*ρ y) by intro y; ring]
    rw [integral_const_mul]
    rfl
  rwa [hleft,hright] at hweak

/-- 横向测试核实际取非负归一化 bump；非负性用于平均导数的同常数界。 -/
theorem exists_positive_normalized_test {a b : ℝ} (hab : a < b) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioo a b ∧ (∀ x, 0 ≤ ρ x) ∧ (∫ x in Ioo a b, ρ x) = 1 := by
  let bump : ContDiffBump ((a+b)/2) :=
    { rIn := (b-a)/8
      rOut := (b-a)/4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hs : tsupport (bump.normed volume) ⊆ Ioo a b := by
    rw [bump.tsupport_normed_eq]
    intro x hx
    have hdist : |x-(a+b)/2| ≤ (b-a)/4 := by
      simpa only [Metric.mem_closedBall,Real.dist_eq,bump] using hx
    have hboth := abs_le.mp hdist
    constructor <;> linarith
  refine ⟨bump.normed volume,bump.contDiff_normed,bump.hasCompactSupport_normed,hs,
    bump.nonneg_normed,?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact bump.integral_normed
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))

/-- 平均弱导数为可测函数，且在实际 x 区间内保持原导数的幅度上界。
积分核非负且积分为一；这里没有读取 L² 商类的点值。 -/
theorem averagedDerivativeX_properties (D : Rect) (m : RegionalWeakCoefficient D)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hnρ : ∀ y, 0 ≤ ρ y) (hiρ : (∫ y in Ioo D.ylo D.yhi, ρ y) = 1) :
    Measurable (averagedDerivativeX D m ρ) ∧
    ∀ x ∈ Ioo D.xlo D.xhi, ‖averagedDerivativeX D m ρ x‖ ≤ (m.derivative 0).bound := by
  have hmeas : Measurable (fun z : ℝ × ℝ => (m.derivative 0).value z * ρ z.2) :=
    (m.derivative 0).measurable.mul (hρ.continuous.measurable.comp measurable_snd)
  refine ⟨hmeas.stronglyMeasurable.integral_prod_right'.measurable,?_⟩
  intro x hx
  have hρint : IntegrableOn ρ (Ioo D.ylo D.yhi) volume :=
    (hρ.continuous.integrable_of_hasCompactSupport hcρ).integrableOn
  have hdom : ∀ᵐ y ∂volume.restrict (Ioo D.ylo D.yhi),
      ‖(m.derivative 0).value (x,y)*ρ y‖ ≤ (m.derivative 0).bound*ρ y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hnρ y)]
    exact mul_le_mul_of_nonneg_right ((m.derivative 0).bound_on (x,y) ⟨hx,hy⟩) (hnρ y)
  calc
    ‖averagedDerivativeX D m ρ x‖ ≤ ∫ y in Ioo D.ylo D.yhi, (m.derivative 0).bound*ρ y :=
      norm_integral_le_of_norm_le (hρint.const_mul _) hdom
    _ = (m.derivative 0).bound := by rw [integral_const_mul,hiρ,mul_one]

/-- 真实二维分离 W¹,∞ 系数具有一维 Lipschitz 代表。
只使用区域弱导数、可测性和有界性；连续性不是输入。
输出在坐标区间的 a.e. 等式，下一步提升到矩形乘积测度。 -/
theorem separated_lipschitz_representative_x (D : Rect) (m : RegionalWeakCoefficient D)
    (p : ℝ → ℝ) (hsep : ∀ z ∈ D.openSet, m.value.value z = p z.1) :
    ∃ F : ℝ → ℝ, LipschitzWith ⟨(m.derivative 0).bound,(m.derivative 0).bound_nonneg⟩ F ∧
      p =ᵐ[volume.restrict (Ioo D.xlo D.xhi)] F := by
  obtain ⟨ρ,hρ,hcρ,hsρ,hnρ,hiρ⟩ := exists_positive_normalized_test D.y_lt
  let y₀ : ℝ := (D.ylo+D.yhi)/2
  have hy₀ : y₀ ∈ Ioo D.ylo D.yhi := by dsimp [y₀]; constructor <;> linarith [D.y_lt]
  let f : ℝ → ℝ := fun x => m.value.value (x,y₀)
  have hf : Measurable f := m.value.measurable.comp (measurable_id.prodMk measurable_const)
  have hf_eq (x : ℝ) (hx : x ∈ Ioo D.xlo D.xhi) : f x = p x := hsep (x,y₀) ⟨hx,hy₀⟩
  have hderivative := averagedDerivativeX_properties D m ρ hρ hcρ hnρ hiρ
  have hweak (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hsη : tsupport η ⊆ Ioo D.xlo D.xhi) :
      (∫ x in Ioo D.xlo D.xhi, deriv η x*f x) =
        -(∫ x in Ioo D.xlo D.xhi, η x*averagedDerivativeX D m ρ x) := by
    calc
      _ = ∫ x in Ioo D.xlo D.xhi, deriv η x*p x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        rw [hf_eq x hx]
      _ = _ := separated_weak_derivative_x D m p hsep ρ hρ hcρ hsρ hiρ η hη hcη hsη
  obtain ⟨F,hF,hrep⟩ := exists_regional_lipschitz_representative D.x_lt f
    (averagedDerivativeX D m ρ) hf hderivative.1 m.value.bound
    ⟨(m.derivative 0).bound,(m.derivative 0).bound_nonneg⟩
    (fun x hx => by simpa only [Real.norm_eq_abs] using m.value.bound_on (x,y₀) ⟨hx,hy₀⟩)
    hderivative.2 hweak
  refine ⟨F,hF,?_⟩
  filter_upwards [hrep,ae_restrict_mem measurableSet_Ioo] with x hx hxin
  exact (hf_eq x hxin).symm.trans hx
/-- 平均弱导数为可测函数，且在实际 y 区间内保持原导数的幅度上界。
积分核非负且积分为一；这里没有读取 L² 商类的点值。 -/
theorem averagedDerivativeY_properties (D : Rect) (m : RegionalWeakCoefficient D)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hnρ : ∀ y, 0 ≤ ρ y) (hiρ : (∫ y in Ioo D.xlo D.xhi, ρ y) = 1) :
    Measurable (averagedDerivativeY D m ρ) ∧
    ∀ x ∈ Ioo D.ylo D.yhi, ‖averagedDerivativeY D m ρ x‖ ≤ (m.derivative 1).bound := by
  have hmeas : Measurable (fun z : ℝ × ℝ => (m.derivative 1).value (z.2,z.1) * ρ z.2) :=
    ((m.derivative 1).measurable.comp measurable_swap).mul (hρ.continuous.measurable.comp measurable_snd)
  refine ⟨hmeas.stronglyMeasurable.integral_prod_right'.measurable,?_⟩
  intro x hx
  have hρint : IntegrableOn ρ (Ioo D.xlo D.xhi) volume :=
    (hρ.continuous.integrable_of_hasCompactSupport hcρ).integrableOn
  have hdom : ∀ᵐ y ∂volume.restrict (Ioo D.xlo D.xhi),
      ‖(m.derivative 1).value (y,x)*ρ y‖ ≤ (m.derivative 1).bound*ρ y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hnρ y)]
    exact mul_le_mul_of_nonneg_right ((m.derivative 1).bound_on (y,x) ⟨hy,hx⟩) (hnρ y)
  calc
    ‖averagedDerivativeY D m ρ x‖ ≤ ∫ y in Ioo D.xlo D.xhi, (m.derivative 1).bound*ρ y :=
      norm_integral_le_of_norm_le (hρint.const_mul _) hdom
    _ = (m.derivative 1).bound := by rw [integral_const_mul,hiρ,mul_one]

/-- 真实二维分离 W¹,∞ 系数具有一维 Lipschitz 代表。
只使用区域弱导数、可测性和有界性；连续性不是输入。
输出在坐标区间的 a.e. 等式，下一步提升到矩形乘积测度。 -/
theorem separated_lipschitz_representative_y (D : Rect) (m : RegionalWeakCoefficient D)
    (p : ℝ → ℝ) (hsep : ∀ z ∈ D.openSet, m.value.value z = p z.2) :
    ∃ F : ℝ → ℝ, LipschitzWith ⟨(m.derivative 1).bound,(m.derivative 1).bound_nonneg⟩ F ∧
      p =ᵐ[volume.restrict (Ioo D.ylo D.yhi)] F := by
  obtain ⟨ρ,hρ,hcρ,hsρ,hnρ,hiρ⟩ := exists_positive_normalized_test D.x_lt
  let y₀ : ℝ := (D.xlo+D.xhi)/2
  have hy₀ : y₀ ∈ Ioo D.xlo D.xhi := by dsimp [y₀]; constructor <;> linarith [D.x_lt]
  let f : ℝ → ℝ := fun x => m.value.value (y₀,x)
  have hf : Measurable f := m.value.measurable.comp (measurable_const.prodMk measurable_id)
  have hf_eq (x : ℝ) (hx : x ∈ Ioo D.ylo D.yhi) : f x = p x := hsep (y₀,x) ⟨hy₀,hx⟩
  have hderivative := averagedDerivativeY_properties D m ρ hρ hcρ hnρ hiρ
  have hweak (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hsη : tsupport η ⊆ Ioo D.ylo D.yhi) :
      (∫ x in Ioo D.ylo D.yhi, deriv η x*f x) =
        -(∫ x in Ioo D.ylo D.yhi, η x*averagedDerivativeY D m ρ x) := by
    calc
      _ = ∫ x in Ioo D.ylo D.yhi, deriv η x*p x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        rw [hf_eq x hx]
      _ = _ := separated_weak_derivative_y D m p hsep ρ hρ hcρ hsρ hiρ η hη hcη hsη
  obtain ⟨F,hF,hrep⟩ := exists_regional_lipschitz_representative D.y_lt f
    (averagedDerivativeY D m ρ) hf hderivative.1 m.value.bound
    ⟨(m.derivative 1).bound,(m.derivative 1).bound_nonneg⟩
    (fun x hx => by simpa only [Real.norm_eq_abs] using m.value.bound_on (y₀,x) ⟨hy₀,hx⟩)
    hderivative.2 hweak
  refine ⟨F,hF,?_⟩
  filter_upwards [hrep,ae_restrict_mem measurableSet_Ioo] with x hx hxin
  exact (hf_eq x hxin).symm.trans hx

/-- 一维 a.e. 代表相等沿 x 投影提升到真实矩形测度，不交换时间量词。 -/
theorem representative_ae_rectangle_x (D : Rect) (m : RegionalWeakCoefficient D)
    (p F : ℝ → ℝ) (hsep : ∀ z ∈ D.openSet, m.value.value z = p z.1)
    (hrep : p =ᵐ[volume.restrict (Ioo D.xlo D.xhi)] F) :
    m.value.value =ᵐ[D.measure] (fun z => F z.1) := by
  have hp : ∀ᵐ z ∂(volume.restrict (Ioo D.xlo D.xhi)).prod
      (volume.restrict (Ioo D.ylo D.yhi)), p z.1 = F z.1 :=
    Measure.quasiMeasurePreserving_fst.ae hrep
  rw [← D.measure_eq_prod] at hp
  filter_upwards [hp,ae_restrict_mem D.openSet_open.measurableSet] with z hz hin
  exact (hsep z hin).trans hz

/-- y 投影版本，与 x 版本共享整个计算域，保留零吸收集合。 -/
theorem representative_ae_rectangle_y (D : Rect) (m : RegionalWeakCoefficient D)
    (p F : ℝ → ℝ) (hsep : ∀ z ∈ D.openSet, m.value.value z = p z.2)
    (hrep : p =ᵐ[volume.restrict (Ioo D.ylo D.yhi)] F) :
    m.value.value =ᵐ[D.measure] (fun z => F z.2) := by
  have hp : ∀ᵐ z ∂(volume.restrict (Ioo D.xlo D.xhi)).prod
      (volume.restrict (Ioo D.ylo D.yhi)), p z.2 = F z.2 :=
    Measure.quasiMeasurePreserving_snd.ae hrep
  rw [← D.measure_eq_prod] at hp
  filter_upwards [hp,ae_restrict_mem D.openSet_open.measurableSet] with z hz hin
  exact (hsep z hin).trans hz

/-- 更换区域有界代表不改变实际 L² 元素。 -/
theorem RegionalBounded.toL2_eq_of_ae {D : Rect} (m n : RegionalBounded D)
    (heq : m.value =ᵐ[D.measure] n.value) : m.toL2 = n.toL2 := by
  apply Lp.ext
  filter_upwards [m.coe_toL2,n.coe_toL2,heq] with x hm hn hmn
  rw [hm,hn,hmn]

/-- 更换代表不改变有界乘法算子；幅度证书和域外值可以不同。 -/
theorem RegionalBounded.operator_eq_of_ae {D : Rect} (m n : RegionalBounded D)
    (heq : m.value =ᵐ[D.measure] n.value) : m.operator = n.operator := by
  ext f
  filter_upwards [m.operator_ae f,n.operator_ae f,heq] with x hm hn hmn
  rw [hm,hn,hmn]

/-- 沿 a.e. 相等替换弱系数的函数代表，保留原弱导数的商类证据。
没有把连续性或新弱导数作为输入。 -/
def RegionalWeakCoefficient.replaceValue {D : Rect} (m : RegionalWeakCoefficient D)
    (n : RegionalBounded D) (heq : m.value.value =ᵐ[D.measure] n.value) :
    RegionalWeakCoefficient D where
  value := n
  derivative := m.derivative
  weak_partial i := by
    rw [← RegionalBounded.toL2_eq_of_ae m.value n heq]
    exact m.weak_partial i

end LeanPML.PML
