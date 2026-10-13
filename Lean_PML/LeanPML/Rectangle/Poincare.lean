import LeanPML.Rectangle.Green
import LeanPML.PML.Coercivity

/-!
# v0.4.2：具体矩形 Poincaré 的保守常数

对应 V7 (5.1) 的用途，但本轮证明的常数是 C_P=2L_x，**不是原文的 π 精确常数**。
Green 对 (x−x₋)f 给出平方积分与交叉项的关系，再积分一个非负平方得到估计。
此构造只用真实积分、导数和边界值；不给调用者留下 estimate 参数。

随后在与 greenDomain 相同的四边迹核上构造 ConditionalPoincare。
所有后续 K=8μ(ε+2κ)C_P²、c_* 必须使用这里的常数重新实例化；
原文精确常数下的数值证书没有在这里被沿用。
阅读顺序：poincare_integral_right_zero → poincare_estimate → poincareDomain。
当前是光滑代表域，不覆盖完整 H₀¹ 弱空间。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace
open LeanPML.Analysis LeanPML.PML
namespace LeanPML.Rectangle

/-- 由 V7 (5.1) 所需控制推出的保守版本，原文未单列本常数。
对矩形光滑函数，单用右边零值就有 ∫f²≤(2Lx)²∫f_x²；
完整 PEC 的四边零值当然包含该条件。证明依赖本项目已证真实 Green。 -/
theorem poincare_integral_right_zero (a b : ℝ × ℝ) (hab : a ≤ b) (f : ℝ × ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hboundary : ∀ y ∈ Icc a.2 b.2, f (b.1,y)=0) :
    (∫ z in Icc a b, (f z)^2) ≤
      (2*(b.1-a.1))^2 * ∫ z in Icc a b, (fderiv ℝ f z (1,0))^2 := by
  let χ : ℝ × ℝ → ℝ := fun z => z.1-a.1
  let fx : ℝ × ℝ → ℝ := fun z => fderiv ℝ f z (1,0)
  have hχ : ContDiff ℝ ∞ χ := contDiff_fst.sub contDiff_const
  have hfx : Continuous fx := (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfχ : ContDiff ℝ ∞ (fun z => χ z * f z) := hχ.mul hf
  have hdx : ∀ z, fderiv ℝ (fun z => χ z*f z) z (1,0) = f z + χ z*fx z := by
    intro z
    change fderiv ℝ (χ*f) z (1,0) = _
    rw [fderiv_mul (hχ.differentiable (by simp) z) (hf.differentiable (by simp) z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    dsimp [χ, fx]
    rw [fderiv_sub_const, fderiv_fst]
    simp [add_comm]
  have hright : (∫ y in a.2..b.2, f (b.1,y)*(χ (b.1,y)*f (b.1,y))) = 0 := by
    calc
      _ = ∫ y in a.2..b.2, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hab.2] at hy
        simp [hboundary y hy]
      _ = 0 := by simp
  -- 对测试函数 f 和通量 ((x−x₋)f,0) 调用已证 Green；右边 f=0，左边乘子为零。
  have hgreen := green_smooth_functions a b hab f (fun z => χ z*f z) (fun _ => 0)
    hf hfχ contDiff_const
  have hzeroDeriv : ∀ z : ℝ × ℝ, fderiv ℝ (fun _ : ℝ × ℝ => (0:ℝ)) z = 0 := fun z => (hasFDerivAt_const (0:ℝ) z).fderiv
  simp only [hdx, hzeroDeriv, zero_apply, add_zero, mul_zero,
    intervalIntegral.integral_zero, integral_zero, sub_zero, χ, sub_self, zero_mul, hright] at hgreen
  have hiF : Integrable (fun z => (f z)^2) (volume.restrict (Icc a b)) :=
    (hf.continuous.pow 2).integrableOn_Icc
  have hiCross : Integrable (fun z => χ z * f z * fx z) (volume.restrict (Icc a b)) :=
    ((hχ.continuous.mul hf.continuous).mul hfx).integrableOn_Icc
  have hiDx : Integrable (fun z => (fx z)^2) (volume.restrict (Icc a b)) :=
    (hfx.pow 2).integrableOn_Icc
  have hiWeighted : Integrable (fun z => (χ z)^2 * (fx z)^2) (volume.restrict (Icc a b)) :=
    ((hχ.continuous.pow 2).mul (hfx.pow 2)).integrableOn_Icc
  have hleft : (∫ z in Icc a b, f z*(f z+χ z*fx z)) =
      (∫ z in Icc a b, (f z)^2) + ∫ z in Icc a b, χ z*f z*fx z := by
    calc
      _ = ∫ z in Icc a b, (f z)^2 + χ z*f z*fx z := by
        apply integral_congr_ae; filter_upwards [] with z; ring
      _ = _ := integral_add hiF hiCross
  have hrightCross : (∫ z in Icc a b, fderiv ℝ f z (1,0)*((z.1-a.1)*f z)) =
      ∫ z in Icc a b, χ z*f z*fx z := by
    apply integral_congr_ae; filter_upwards [] with z; dsimp [χ,fx]; ring
  rw [hleft, hrightCross] at hgreen
  have hzero : (∫ z in Icc a b, (f z)^2) +
      2*(∫ z in Icc a b, χ z*f z*fx z) = 0 := by linarith
  -- 这里使用积分的真实非负性：(f+2χf_x)²≥0，而非把 Poincaré 写入输入。
  have hsquare : 0 ≤ ∫ z in Icc a b, (f z + 2*χ z*fx z)^2 :=
    integral_nonneg (fun z => sq_nonneg _)
  have hsquare_expand : (∫ z in Icc a b, (f z + 2*χ z*fx z)^2) =
      (∫ z in Icc a b, (f z)^2) +
      4*(∫ z in Icc a b, χ z*f z*fx z) +
      4*(∫ z in Icc a b, (χ z)^2*(fx z)^2) := by
    calc
      _ = ∫ z in Icc a b, (f z)^2+4*(χ z*f z*fx z)+4*((χ z)^2*(fx z)^2) := by
        apply integral_congr_ae; filter_upwards [] with z; ring
      _ = _ := by
        have hsum := integral_add (hiF.add (hiCross.const_mul 4)) (hiWeighted.const_mul 4)
        simp only [Pi.add_apply] at hsum
        rw [hsum, integral_add hiF (hiCross.const_mul 4), integral_const_mul, integral_const_mul]
  -- 闭矩形内 0≤χ≤Lx，故 χ²≤Lx²。积分序关系前已有各项可积性。
  have hweight : (∫ z in Icc a b, (χ z)^2*(fx z)^2) ≤
      (b.1-a.1)^2 * ∫ z in Icc a b, (fx z)^2 := by
    calc
      _ ≤ ∫ z in Icc a b, (b.1-a.1)^2*(fx z)^2 := by
        apply setIntegral_mono_on hiWeighted (hiDx.const_mul _) measurableSet_Icc
        intro z hz
        have hχbounds : 0 ≤ χ z ∧ χ z ≤ b.1-a.1 := by
          dsimp [χ]; constructor <;> linarith [hz.1.1,hz.2.1]
        have hχsquare : (χ z)^2 ≤ (b.1-a.1)^2 := by nlinarith [hχbounds.1,hχbounds.2]
        exact mul_le_mul_of_nonneg_right hχsquare (sq_nonneg _)
      _ = _ := integral_const_mul _ _
  rw [hsquare_expand] at hsquare
  dsimp [fx] at hweight
  nlinarith

/-- 本轮实际证明的正 Poincaré 常数 C_P=2Lx；不声称为最优常数。 -/
def poincareConstant (D : Rect) : ℝ := 2*D.Lx

/-- 矩形非退化保证本轮常数为正，后续阈值分母合法。 -/
theorem poincareConstant_pos (D : Rect) : 0 < poincareConstant D :=
  mul_pos (by norm_num) D.Lx_pos

/-- 具体光滑零边界函数的 Poincaré 空间积分估计；保留两个梯度分量。
只用了右边零值作证明，但输入仍是与 Green 一致的整个外边界条件。 -/
theorem poincare_smooth (D : Rect) (f : SmoothField) (htrace : ZeroBoundary D f) :
    (∫ z, (f z)^2 ∂D.measure) ≤ poincareConstant D ^2 *
      ((∫ z, (dx f z)^2 ∂D.measure) + ∫ z, (dy f z)^2 ∂D.measure) := by
  have hx := poincare_integral_right_zero (D.xlo,D.ylo) (D.xhi,D.yhi)
    ⟨D.x_lt.le,D.y_lt.le⟩ f f.contDiff htrace.1
  have hy_nonneg : 0 ≤ ∫ z, (dy f z)^2 ∂D.measure := integral_nonneg (fun z => sq_nonneg _)
  rw [D.measure_eq_closed,D.closedSet_eq_Icc] at hy_nonneg ⊢
  dsimp [poincareConstant,Rect.Lx,dx,dy] at hx hy_nonneg ⊢
  have hpositive := mul_nonneg (sq_nonneg (2*(D.xhi-D.xlo))) hy_nonneg
  nlinarith only [hx,hpositive]

/-- 与旧工程一致的实际 L² Poincaré；迹就是矩形 Green 所用的 trace。
代表先由闭矩形唯一性取出四边零值，再用已证积分估计；没有 estimate 输入。 -/
theorem poincare_estimate (D : Rect) (U : fieldDomain D) (htrace : trace D U = 0) :
    ‖(U : ScalarL2 D.measure)‖^2 ≤ poincareConstant D ^2 *
      (‖(spatialDomain D).componentX U‖^2 + ‖(spatialDomain D).componentY U‖^2) := by
  have hboundary : ZeroBoundary D (representative D U) := (trace_zero_iff D U).mp htrace
  have hintegral := poincare_smooth D (representative D U) hboundary
  change ‖(U : ScalarL2 D.measure)‖^2 ≤ poincareConstant D ^2 *
    (‖SmoothField.toL2 D (representative D U).derivativeX‖^2 +
     ‖SmoothField.toL2 D (representative D U).derivativeY‖^2)
  rw [← representative_toL2 D U, norm_toL2_sq, norm_toL2_sq, norm_toL2_sq]
  exact hintegral

/-- 用真实矩形估计填入旧工程 Poincaré 接口；零迹域是同一 Green trace 的核。
构造调用者无需也不能另外传入一个未经证明的 estimate。 -/
def poincareDomain (D : Rect) : ConditionalPoincare (spatialDomain D) (poincareConstant D) :=
  ConditionalPoincare.ofGreenTrace (greenDomain D) (poincareConstant D) (poincare_estimate D)

/-- 本轮常数给出的 K 精确为 32μ(ε+2κ)Lx²；后续 c_* 必须同步使用它。
这是参数实例化的恒等式，不改写原文 (5.1)。 -/
theorem scaleK_rectangle (D : Rect) (ε κ μ : ℝ) :
    scaleK ε κ μ (poincareConstant D) = 32*μ*materialA ε κ*D.Lx^2 := by
  unfold scaleK poincareConstant
  ring

/-- 对本轮常数调用旧阈值正性；材料正性与非退化矩形给出合法非空小量范围。
没有继续沿用精确 π 常数版本的数值证书。 -/
theorem threshold_rectangle_pos (D : Rect) (ε κ τ μ : ℝ)
    (hε : 0<ε) (hκ : 0<κ) (hτ : 0<τ) (hμ : 0<μ) :
    0 < threshold ε κ τ μ (poincareConstant D) :=
  threshold_pos ε κ τ μ (poincareConstant D) hε hκ hτ hμ (poincareConstant_pos D)

/-- 非平凡调用：多项式泡函数的实际 L² 类非零、四边零迹，且满足本轮 Poincaré。
它检验真实接口的非零定义域；不冒称存在一条非零 PDE 解。 -/
theorem rectangleBubble_poincare (D : Rect) :
    SmoothField.toL2 D (rectangleBubble D) ≠ 0 ∧
    ‖SmoothField.toL2 D (rectangleBubble D)‖^2 ≤ poincareConstant D ^2 *
      (‖SmoothField.toL2 D (rectangleBubble D).derivativeX‖^2 +
       ‖SmoothField.toL2 D (rectangleBubble D).derivativeY‖^2) := by
  refine ⟨rectangleBubble_toL2_ne_zero D, ?_⟩
  have htrace : trace D ⟨SmoothField.toL2 D (rectangleBubble D),⟨rectangleBubble D,rfl⟩⟩ = 0 := by
    rw [trace_toL2]
    exact (smoothTrace_eq_zero_iff D _).mpr (rectangleBubble_zeroBoundary D)
  have hbound := poincare_estimate D
    ⟨SmoothField.toL2 D (rectangleBubble D),⟨rectangleBubble D,rfl⟩⟩ htrace
  erw [componentX_toL2,componentY_toL2] at hbound
  exact hbound

end LeanPML.Rectangle
