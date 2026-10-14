import LeanPML.PML.SeparatedWeakCoefficients
import LeanPML.Rectangle.WeakGreen

/-!
# V7 §5.3：真实弱空间中的规范差值消去

先用光滑坐标乘子构造 H(div) 通量，再调用已证弱 Green。
因此不要求粗糙系数乘积 pg 本身已进入 H₀¹，也不假设一般切片零迹。
零吸收区保留独立梯度条件；连续区域代表只用于正吸收区开集局部性。
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ContDiff Topology
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

/-- 区域实系数 L² 乘法在真实内积中可交换到另一侧。a.e. 改写消除代表选择。 -/
theorem regional_inner_switch (D : Rect) (m : RegionalBounded D)
    (f g : ScalarL2 D.measure) : ⟪m.operator f,g⟫_ℝ = ⟪f,m.operator g⟫_ℝ := by
  rw [inner_eq_integral,inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [m.operator_ae f,m.operator_ae g] with x hf hg
  rw [hf,hg]
  ring

/-- 光滑乘子乘内部测试函数仍内部紧支；无需乘子自身紧支。 -/
def smoothTimesTest {D : Rect} (χ : SmoothField) (φ : TestFunction D) : TestFunction D where
  field := smoothProduct χ φ.field
  compact := φ.compact.mul_left
  support_inside := tsupport_mul_subset_right.trans φ.support_inside

/-- 实际光滑函数乘积与有界区域乘子的 L² 表示一致。 -/
theorem smooth_mul_toL2 (D : Rect) (χ φ : SmoothField) :
    SmoothField.toL2 D (smoothProduct χ φ) =
      (regionalBoundedOfSmooth D χ).operator (SmoothField.toL2 D φ) := by
  apply Lp.ext
  filter_upwards [SmoothField.coe_toL2 D (smoothProduct χ φ),
    (regionalBoundedOfSmooth D χ).operator_ae (SmoothField.toL2 D φ),
    SmoothField.coe_toL2 D φ] with x hprod hop hφ
  rw [hprod,hop,hφ]
  rfl

/-- 光滑乘子作用在真实弱偏导上；由测试 χφ 的分布关系推导。
此处 f 不要求零迹，正好可应用于尚未证明属于 H₀¹ 的 pg。 -/
theorem HasWeakPartial.mul_smooth {D : Rect} {i : Fin 2}
    {f df : ScalarL2 D.measure} (hpartial : HasWeakPartial D i f df)
    (χ : SmoothField) :
    HasWeakPartial D i ((regionalBoundedOfSmooth D χ).operator f)
      ((regionalBoundedOfSmooth D (smoothPartial i χ)).operator f +
        (regionalBoundedOfSmooth D χ).operator df) := by
  intro φ
  have hweak := hpartial (smoothTimesTest χ φ)
  have hsplit : SmoothField.toL2 D (smoothPartial i (smoothTimesTest χ φ).field) =
      (regionalBoundedOfSmooth D (smoothPartial i χ)).operator
        (SmoothField.toL2 D φ.field) +
      (regionalBoundedOfSmooth D χ).operator
        (SmoothField.toL2 D (smoothPartial i φ.field)) := by
    rw [← smooth_mul_toL2,← smooth_mul_toL2,← map_add]
    congr 1
    apply Subtype.ext
    funext x
    exact smoothPartial_product i χ φ.field x
  change ⟪df,SmoothField.toL2 D (smoothProduct χ φ.field)⟫_ℝ = _ at hweak
  rw [smooth_mul_toL2,hsplit,inner_add_right] at hweak
  rw [inner_add_left,regional_inner_switch,regional_inner_switch,regional_inner_switch]
  linarith

/-- 坐标函数 χᵢ(x,y)=x 或 y，光滑且在有限矩形上有界。 -/
def coordinateField (i : Fin 2) : SmoothField :=
  if i = 0 then ⟨Prod.fst,by change ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ); exact contDiff_fst⟩
  else ⟨Prod.snd,by change ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ); exact contDiff_snd⟩

/-- 坐标沿自身方向的真实偏导为常数 1。 -/
theorem coordinateField_partial (i : Fin 2) :
    smoothPartial i (coordinateField i) = weakCoefficientOne := by
  apply Subtype.ext
  funext x
  fin_cases i <;> simp [smoothPartial,coordinateField,SmoothField.derivativeX_apply,
    SmoothField.derivativeY_apply,dx,dy,weakCoefficientOne,fderiv_fst,fderiv_snd]

/-- 常数 1 的区域乘子是恒等，不因选择区域延拓而改变域内场。 -/
theorem regional_one_operator (D : Rect) (f : ScalarL2 D.measure) :
    (regionalBoundedOfSmooth D weakCoefficientOne).operator f = f := by
  apply Lp.ext
  filter_upwards [(regionalBoundedOfSmooth D weakCoefficientOne).operator_ae f]
    with x hx
  simpa [regionalBoundedOfSmooth,weakCoefficientOne] using hx

/-- 若 ∂ᵢf=0，则坐标乘积 χᵢf 的 i 弱偏导为 f；用来构造 Green 通量。 -/
theorem coordinate_mul_partial {D : Rect} (i : Fin 2) (f : ScalarL2 D.measure)
    (hpartial : HasWeakPartial D i f 0) :
    HasWeakPartial D i ((regionalBoundedOfSmooth D (coordinateField i)).operator f) f := by
  have hproduct := HasWeakPartial.mul_smooth hpartial (coordinateField i)
  simpa [coordinateField_partial,regional_one_operator] using hproduct

/-- 横向导数为零的非负系数乘积必为零。
输入为 u∈H₀¹、f=mu、∂ᵢf=0、m∂ᵢu=0；以 χᵢf 为单分量通量调用弱Green，
得到 ∫m u²=0，再由非负性推出 mu=0。没有要求 mu∈H₀¹。 -/
theorem coefficient_product_zero_of_transverse (D : Rect) (m : RegionalBounded D)
    (u : zeroBoundaryGraph D) (i : Fin 2)
    (hm_nonneg : ∀ x ∈ D.openSet, 0 ≤ m.value x)
    (hpartial : HasWeakPartial D i (m.operator (u.val.val 0)) 0)
    (htransverse : m.operator (u.val.val (if i = 0 then 1 else 2)) = 0) :
    m.operator (u.val.val 0) = 0 := by
  let f := m.operator (u.val.val 0)
  let χ := regionalBoundedOfSmooth D (coordinateField i)
  have hcoordinate : HasWeakPartial D i (χ.operator f) f :=
    coordinate_mul_partial i f hpartial
  have hpair : ⟪u.val.val 0,f⟫_ℝ = 0 := by
    have hgradient_pair : ⟪u.val.val (if i = 0 then 1 else 2),χ.operator f⟫_ℝ = 0 := by
      rw [inner_eq_integral]
      apply integral_eq_zero_of_ae
      filter_upwards [χ.operator_ae f,m.operator_ae (u.val.val 0),
        m.operator_ae (u.val.val (if i = 0 then 1 else 2)),
        Lp.eq_zero_iff_ae_eq_zero.mp htransverse] with x hχ hf hmul hzero
      change _ = 0
      have hproduct : m.value x * u.val.val (if i = 0 then 1 else 2) x = 0 :=
        hmul.symm.trans hzero
      rw [hχ,hf]
      calc
        _ = χ.value x * u.val.val 0 x *
            (m.value x * u.val.val (if i = 0 then 1 else 2) x) := by ring
        _ = 0 := by rw [hproduct,mul_zero]
    fin_cases i
    · let flux : weakHDivGraph D := ⟨![χ.operator f,0,f],by
        intro φ
        simpa [HasWeakPartial,smoothPartial] using hcoordinate φ⟩
      have hgreen := weak_green D u flux
      change ⟪u.val.val 1,χ.operator f⟫_ℝ + ⟪u.val.val 2,0⟫_ℝ =
        -⟪u.val.val 0,f⟫_ℝ at hgreen
      simp only [inner_zero_right,add_zero] at hgreen
      change ⟪u.val.val 1,χ.operator f⟫_ℝ = 0 at hgradient_pair
      linarith
    · let flux : weakHDivGraph D := ⟨![0,χ.operator f,f],by
        intro φ
        simpa [HasWeakPartial,smoothPartial] using hcoordinate φ⟩
      have hgreen := weak_green D u flux
      change ⟪u.val.val 1,0⟫_ℝ + ⟪u.val.val 2,χ.operator f⟫_ℝ =
        -⟪u.val.val 0,f⟫_ℝ at hgreen
      simp only [inner_zero_right,zero_add] at hgreen
      change ⟪u.val.val 2,χ.operator f⟫_ℝ = 0 at hgradient_pair
      linarith
  have hdensity_nonneg : 0 ≤ᵐ[D.measure] (fun x => u.val.val 0 x * f x) := by
    filter_upwards [m.operator_ae (u.val.val 0),
      ae_restrict_mem D.openSet_open.measurableSet] with x hf hx
    change 0 ≤ u.val.val 0 x * f x
    rw [hf]
    nlinarith [mul_nonneg (hm_nonneg x hx) (sq_nonneg (u.val.val 0 x))]
  have hdensity_zero := (integral_eq_zero_iff_of_nonneg_ae hdensity_nonneg
    (integrable_product D.measure (u.val.val 0) f)).mp (by
      rw [← inner_eq_integral];exact hpair)
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hdensity_zero,m.operator_ae (u.val.val 0)] with x hzero hf
  change u.val.val 0 x * f x = 0 at hzero
  rcases mul_eq_zero.mp hzero with hu | hfx
  · change f x = 0
    rw [hf,hu,mul_zero]
  · exact hfx

/-- 若区域系数的 L² 商类为零，它对任何 L² 场的乘子也是零。
用于把已证横向弱导数为零接到弱乘积法则，而非读取商类的任意点值。 -/
theorem regional_operator_zero_of_toL2_zero (D : Rect) (m : RegionalBounded D)
    (hm : m.toL2 = 0) (f : ScalarL2 D.measure) : m.operator f = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [m.operator_ae f,m.coe_toL2,Lp.eq_zero_iff_ae_eq_zero.mp hm]
    with x hmul hrepr hzero
  have hm_value : m.value x = 0 := hrepr.symm.trans hzero
  change m.operator f x = 0
  rw [hmul,hm_value,zero_mul]

/-- V7 §5.3 规范差值的弱空间主引理。
g∈H₀¹、p∂yg=r∂xg=0、零区∇g=0，推出 g=0（实际等价类意义）。
分离区域 W¹,∞ 给出横向弱导数零；弱乘积+坐标通量Green推出 pg=rg=0；
连续代表使 Ω₊ 开，从局部性得到剩余弱梯度零，最后用弱Poincaré。
因此原文的附加 bg=0 在这条等价路线中不再需要；没有把梯度零/唯一性设为输入。
连续性是区域代表的明确技术条件，不宣称仅由可测字段自动推出。 -/
theorem weak_lift_difference_zero (D : Rect) (m : SeparatedRegionalWeakCoefficients D)
    (g : zeroBoundaryGraph D)
    (hp_continuous : ContinuousOn m.p.value.value D.openSet)
    (hr_continuous : ContinuousOn m.r.value.value D.openSet)
    (hp_nonneg : ∀ x ∈ D.openSet, 0 ≤ m.p.value.value x)
    (hr_nonneg : ∀ x ∈ D.openSet, 0 ≤ m.r.value.value x)
    (hp_dy : m.p.value.operator (g.val.val 2) = 0)
    (hr_dx : m.r.value.operator (g.val.val 1) = 0)
    (hzero_zone : ∀ᵐ x ∂D.measure,
      m.p.value.value x + m.r.value.value x = 0 →
      g.val.val 1 x = 0 ∧ g.val.val 2 x = 0) : g = 0 := by
  have htransverse := m.transverse_zero
  have hp_product_partial : HasWeakPartial D 1
      (m.p.value.operator (g.val.val 0)) 0 := by
    have hweak := (weakCoefficientMul D m.p g).property.2
    have hcoordinates := weakCoefficientMul_derivatives D m.p g
    rw [weakCoefficientMul_value,hcoordinates.2] at hweak
    rw [regional_operator_zero_of_toL2_zero D (m.p.derivative 1)
      htransverse.1, hp_dy,add_zero] at hweak
    exact hweak
  have hr_product_partial : HasWeakPartial D 0
      (m.r.value.operator (g.val.val 0)) 0 := by
    have hweak := (weakCoefficientMul D m.r g).property.1
    have hcoordinates := weakCoefficientMul_derivatives D m.r g
    rw [weakCoefficientMul_value,hcoordinates.1] at hweak
    rw [regional_operator_zero_of_toL2_zero D (m.r.derivative 0)
      htransverse.2, hr_dx,add_zero] at hweak
    exact hweak
  have hpg_zero : m.p.value.operator (g.val.val 0) = 0 :=
    coefficient_product_zero_of_transverse D m.p.value g 1
      hp_nonneg hp_product_partial hp_dy
  have hrg_zero : m.r.value.operator (g.val.val 0) = 0 :=
    coefficient_product_zero_of_transverse D m.r.value g 0
      hr_nonneg hr_product_partial hr_dx
  exact weak_zero_of_coefficient_products D m.p.value m.r.value g
    hp_continuous hr_continuous hp_nonneg hr_nonneg hpg_zero hrg_zero hzero_zone

end LeanPML.PML
