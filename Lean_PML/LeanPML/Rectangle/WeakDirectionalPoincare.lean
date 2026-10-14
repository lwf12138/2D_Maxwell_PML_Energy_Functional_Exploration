import LeanPML.Rectangle.WeakPoincare
import LeanPML.Examples.WeakSpaces

/-!
# H₀¹ 的方向 Poincaré 与单个弱偏导的零分离

服务于 V7 §5.3 的提升规范约束，原文未单列以下方向估计。
先使用真实矩形 Green 得到只含一个导数的保守界，再以三个 L² 坐标的
图范数闭包推广。不是把“完整梯度为零”换名为“单个导数为零”。
本文件不证明分离系数乘积的零迹保持，也不声称已经得到规范唯一性。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace
open LeanPML.Analysis LeanPML.PML
namespace LeanPML.Rectangle

/-- 由 §5.3 所需方向控制推出：仅上边零值便有 ∫f²≤(2Ly)²∫f_y²。
在真实 Green 中选通量 (0,(y−y₋)f)；上边用零迹，下边乘子为零。
各项可积性由闭矩形上的光滑性证明，未输入目标 Poincaré。 -/
theorem poincare_integral_top_zero (a b : ℝ × ℝ) (hab : a ≤ b) (f : ℝ × ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hboundary : ∀ x ∈ Icc a.1 b.1, f (x,b.2)=0) :
    (∫ z in Icc a b, (f z)^2) ≤
      (2*(b.2-a.2))^2 * ∫ z in Icc a b, (fderiv ℝ f z (0,1))^2 := by
  let χ : ℝ × ℝ → ℝ := fun z => z.2-a.2
  let fy : ℝ × ℝ → ℝ := fun z => fderiv ℝ f z (0,1)
  have hχ : ContDiff ℝ ∞ χ := contDiff_snd.sub contDiff_const
  have hfy : Continuous fy := (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfχ : ContDiff ℝ ∞ (fun z => χ z * f z) := hχ.mul hf
  have hdy : ∀ z, fderiv ℝ (fun z => χ z*f z) z (0,1) = f z + χ z*fy z := by
    intro z
    change fderiv ℝ (χ*f) z (0,1) = _
    rw [fderiv_mul (hχ.differentiable (by simp) z) (hf.differentiable (by simp) z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    dsimp [χ, fy]
    rw [fderiv_sub_const, fderiv_snd]
    simp [add_comm]
  have htop : (∫ x in a.1..b.1, f (x,b.2)*(χ (x,b.2)*f (x,b.2))) = 0 := by
    calc
      _ = ∫ x in a.1..b.1, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab.1] at hx
        simp [hboundary x hx]
      _ = 0 := by simp
  -- 对测试函数 f 和通量 (0,(y−y₋)f) 调用已证 Green；上边 f=0，下边乘子为零。
  have hgreen := green_smooth_functions a b hab f (fun _ => 0) (fun z => χ z*f z)
    hf contDiff_const hfχ
  have hzeroDeriv : ∀ z : ℝ × ℝ, fderiv ℝ (fun _ : ℝ × ℝ => (0:ℝ)) z = 0 := fun z => (hasFDerivAt_const (0:ℝ) z).fderiv
  simp only [hdy, hzeroDeriv, zero_apply, add_zero, zero_add, mul_zero,
    intervalIntegral.integral_zero, integral_zero, zero_sub, neg_zero, χ, sub_self, zero_mul, htop] at hgreen
  have hiF : Integrable (fun z => (f z)^2) (volume.restrict (Icc a b)) :=
    (hf.continuous.pow 2).integrableOn_Icc
  have hiCross : Integrable (fun z => χ z * f z * fy z) (volume.restrict (Icc a b)) :=
    ((hχ.continuous.mul hf.continuous).mul hfy).integrableOn_Icc
  have hiDy : Integrable (fun z => (fy z)^2) (volume.restrict (Icc a b)) :=
    (hfy.pow 2).integrableOn_Icc
  have hiWeighted : Integrable (fun z => (χ z)^2 * (fy z)^2) (volume.restrict (Icc a b)) :=
    ((hχ.continuous.pow 2).mul (hfy.pow 2)).integrableOn_Icc
  have hleft : (∫ z in Icc a b, f z*(f z+χ z*fy z)) =
      (∫ z in Icc a b, (f z)^2) + ∫ z in Icc a b, χ z*f z*fy z := by
    calc
      _ = ∫ z in Icc a b, (f z)^2 + χ z*f z*fy z := by
        apply integral_congr_ae; filter_upwards [] with z; ring
      _ = _ := integral_add hiF hiCross
  have hcross_reorder : (∫ z in Icc a b, fderiv ℝ f z (0,1)*((z.2-a.2)*f z)) =
      ∫ z in Icc a b, χ z*f z*fy z := by
    apply integral_congr_ae; filter_upwards [] with z; dsimp [χ,fy]; ring
  rw [hleft, hcross_reorder] at hgreen
  have hzero : (∫ z in Icc a b, (f z)^2) +
      2*(∫ z in Icc a b, χ z*f z*fy z) = 0 := by linarith
  -- 这里使用积分的真实非负性：(f+2χf_y)²≥0，而非把 Poincaré 写入输入。
  have hsquare : 0 ≤ ∫ z in Icc a b, (f z + 2*χ z*fy z)^2 :=
    integral_nonneg (fun z => sq_nonneg _)
  have hsquare_expand : (∫ z in Icc a b, (f z + 2*χ z*fy z)^2) =
      (∫ z in Icc a b, (f z)^2) +
      4*(∫ z in Icc a b, χ z*f z*fy z) +
      4*(∫ z in Icc a b, (χ z)^2*(fy z)^2) := by
    calc
      _ = ∫ z in Icc a b, (f z)^2+4*(χ z*f z*fy z)+4*((χ z)^2*(fy z)^2) := by
        apply integral_congr_ae; filter_upwards [] with z; ring
      _ = _ := by
        have hsum := integral_add (hiF.add (hiCross.const_mul 4)) (hiWeighted.const_mul 4)
        simp only [Pi.add_apply] at hsum
        rw [hsum, integral_add hiF (hiCross.const_mul 4), integral_const_mul, integral_const_mul]
  -- 闭矩形内 0≤χ≤Ly，故 χ²≤Ly²。积分序关系前已有各项可积性。
  have hweight : (∫ z in Icc a b, (χ z)^2*(fy z)^2) ≤
      (b.2-a.2)^2 * ∫ z in Icc a b, (fy z)^2 := by
    calc
      _ ≤ ∫ z in Icc a b, (b.2-a.2)^2*(fy z)^2 := by
        apply setIntegral_mono_on hiWeighted (hiDy.const_mul _) measurableSet_Icc
        intro z hz
        have hχbounds : 0 ≤ χ z ∧ χ z ≤ b.2-a.2 := by
          dsimp [χ]; constructor <;> linarith [hz.1.2,hz.2.2]
        have hχsquare : (χ z)^2 ≤ (b.2-a.2)^2 := by nlinarith [hχbounds.1,hχbounds.2]
        exact mul_le_mul_of_nonneg_right hχsquare (sq_nonneg _)
      _ = _ := integral_const_mul _ _
  rw [hsquare_expand] at hsquare
  dsimp [fy] at hweight
  nlinarith



/-- 方向保守常数：x 用 2Lx，y 用 2Ly。只是本辅助估计，不改变主能量中的 CP。 -/
def directionalPoincareConstant (D : Rect) (i : Fin 2) : ℝ :=
  if i = 0 then 2 * D.Lx else 2 * D.Ly

/-- 光滑零迹场只用一个偏导的实际 L² 估计；四边零迹提供相应右边/上边条件。 -/
theorem smooth_directional_poincare (D : Rect) (f : SmoothField)
    (htrace : ZeroBoundary D f) (i : Fin 2) :
    ‖SmoothField.toL2 D f‖ ^ 2 ≤ directionalPoincareConstant D i ^ 2 *
      ‖SmoothField.toL2 D (smoothPartial i f)‖ ^ 2 := by
  fin_cases i
  · have hbound := poincare_integral_right_zero (D.xlo,D.ylo) (D.xhi,D.yhi)
      ⟨D.x_lt.le,D.y_lt.le⟩ f f.contDiff htrace.1
    simp only [norm_toL2_sq, D.measure_eq_closed, D.closedSet_eq_Icc]
    exact hbound
  · have hbound := poincare_integral_top_zero (D.xlo,D.ylo) (D.xhi,D.yhi)
      ⟨D.x_lt.le,D.y_lt.le⟩ f f.contDiff htrace.2.2.1
    simp only [norm_toL2_sq, D.measure_eq_closed, D.closedSet_eq_Icc]
    exact hbound

/-- x/y 偏导在三坐标弱 H¹ 图中的索引。 -/
def partialGraphIndex (i : Fin 2) : Fin 3 := if i = 0 then 1 else 2

/-- H₀¹ 上的方向 Poincaré：‖g‖²≤(2Li)²‖∂i g‖²。
先在紧支光滑图的有限张成上证明，再以两个坐标范数的连续性取闭包。
无切片正则性假设，亦未假设目标方向估计。 -/
theorem weak_directional_poincare (D : Rect) (v : zeroBoundaryGraph D) (i : Fin 2) :
    ‖v.val.val 0‖ ^ 2 ≤ directionalPoincareConstant D i ^ 2 *
      ‖v.val.val (partialGraphIndex i)‖ ^ 2 := by
  have hspan : (Submodule.span ℝ (Set.range (fun φ : TestFunction D =>
      smoothToWeakH1 D φ.field)) : Set (weakH1Graph D)) ⊆
      {U | ‖U.val 0‖ ^ 2 ≤ directionalPoincareConstant D i ^ 2 *
        ‖U.val (partialGraphIndex i)‖ ^ 2} := by
    intro U hU
    rcases span_test_has_smooth_zeroBoundary D U hU with ⟨f, hf, rfl⟩
    have hbound := smooth_directional_poincare D f hf i
    fin_cases i <;> exact hbound
  have hcoord (j : Fin 3) : Continuous (fun U : weakH1Graph D => ‖U.val j‖ ^ 2) :=
    (((continuous_apply j).comp continuous_subtype_val).norm).pow 2
  have hclosed : IsClosed {U : weakH1Graph D | ‖U.val 0‖ ^ 2 ≤
      directionalPoincareConstant D i ^ 2 * ‖U.val (partialGraphIndex i)‖ ^ 2} :=
    isClosed_le (hcoord 0) (continuous_const.mul (hcoord (partialGraphIndex i)))
  exact closure_minimal hspan hclosed v.property

/-- H₀¹ 中仅一个弱偏导为零就推出整个场为零。
先由方向估计得到函数坐标零，再由弱导数唯一性确定完整图；不要求另一偏导零。 -/
theorem weak_zero_of_partial_zero (D : Rect) (v : zeroBoundaryGraph D) (i : Fin 2)
    (hpartial : v.val.val (partialGraphIndex i) = 0) : v = 0 := by
  have hestimate := weak_directional_poincare D v i
  rw [hpartial, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hestimate
  have hvalue : v.val.val 0 = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (v.val.val 0)]
  apply Subtype.ext
  apply weakValue_injective D
  exact hvalue

/-- 单独 ∂x g=0 的具体入口，供分离系数 r(y)g 的后续规范论证使用。 -/
theorem weak_zero_of_dx_zero (D : Rect) (v : zeroBoundaryGraph D)
    (hx : v.val.val 1 = 0) : v = 0 :=
  weak_zero_of_partial_zero D v 0 hx

/-- 单独 ∂y g=0 的具体入口，供分离系数 p(x)g 的后续规范论证使用。 -/
theorem weak_zero_of_dy_zero (D : Rect) (v : zeroBoundaryGraph D)
    (hy : v.val.val 2 = 0) : v = 0 :=
  weak_zero_of_partial_zero D v 1 hy

/-- 既有非零物理区 bump 的 H₀¹ 图，成员资格调用旧证明。 -/
def directionalExample : zeroBoundaryGraph ParameterCertificate.unitSquare :=
  ⟨smoothToWeakH1 ParameterCertificate.unitSquare
    LeanPML.Examples.WeakSpaces.physicalTest.field,
    LeanPML.Examples.WeakSpaces.physicalTest_nonzero_member.1⟩

/-- 非零二维 bump 对两个方向分别调用一般方向估计，验证没有只证明零场特例。
此处是实际弱场空间调用，不冒称新的 PDE 解。 -/
theorem nonzero_directional_poincare_call (i : Fin 2) :
    directionalExample.val.val 0 ≠ 0 ∧
      ‖directionalExample.val.val 0‖ ^ 2 ≤
        directionalPoincareConstant ParameterCertificate.unitSquare i ^ 2 *
        ‖directionalExample.val.val (partialGraphIndex i)‖ ^ 2 := by
  constructor
  · exact LeanPML.Examples.WeakSpaces.physicalTest_nonzero_member.2
  · exact weak_directional_poincare ParameterCertificate.unitSquare directionalExample i

end LeanPML.Rectangle
