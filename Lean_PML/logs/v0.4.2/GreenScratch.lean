import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import LeanPML.PML.Coercivity
open MeasureTheory Set
open scoped Topology ContDiff
noncomputable section

theorem green_raw (a b : ℝ × ℝ) (hab : a ≤ b) (f X Y : ℝ × ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    (∫ z in Icc a b, f z * (fderiv ℝ X z (1,0) + fderiv ℝ Y z (0,1))) =
    -(∫ z in Icc a b, fderiv ℝ f z (1,0) * X z) -
      (∫ z in Icc a b, fderiv ℝ f z (0,1) * Y z) +
      (((∫ x in a.1..b.1, f (x,b.2)*Y (x,b.2)) -
       (∫ x in a.1..b.1, f (x,a.2)*Y (x,a.2))) +
       (∫ y in a.2..b.2, f (b.1,y)*X (b.1,y)) -
       (∫ y in a.2..b.2, f (a.1,y)*X (a.1,y))) := by
  have hdf := hf.differentiable (by simp)
  have hdX := hX.differentiable (by simp)
  have hdY := hY.differentiable (by simp)
  have hfx : Continuous (fun z => fderiv ℝ f z (1,0)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfy : Continuous (fun z => fderiv ℝ f z (0,1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hXx : Continuous (fun z => fderiv ℝ X z (1,0)) :=
    (hX.continuous_fderiv (by simp)).clm_apply continuous_const
  have hYy : Continuous (fun z => fderiv ℝ Y z (0,1)) :=
    (hY.continuous_fderiv (by simp)).clm_apply continuous_const
  have hprodX : ContDiff ℝ ∞ (fun z => f z * X z) := hf.mul hX
  have hprodY : ContDiff ℝ ∞ (fun z => f z * Y z) := hf.mul hY
  have hdiv_cont : Continuous (fun z =>
      fderiv ℝ (fun z => f z * X z) z (1,0) +
      fderiv ℝ (fun z => f z * Y z) z (0,1)) :=
    ((hprodX.continuous_fderiv (by simp)).clm_apply continuous_const).add
      ((hprodY.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hgreen := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (fun z => f z*X z) (fun z => f z*Y z)
    (fderiv ℝ (fun z => f z*X z)) (fderiv ℝ (fun z => f z*Y z))
    a b hab hprodX.continuous.continuousOn hprodY.continuous.continuousOn
    (fun z _ => (hprodX.differentiable (by simp) z).hasFDerivAt)
    (fun z _ => (hprodY.differentiable (by simp) z).hasFDerivAt)
    hdiv_cont.integrableOn_Icc
  have hexpand : ∀ z, fderiv ℝ (fun z => f z*X z) z (1,0) +
      fderiv ℝ (fun z => f z*Y z) z (0,1) =
      f z * (fderiv ℝ X z (1,0) + fderiv ℝ Y z (0,1)) +
      fderiv ℝ f z (1,0)*X z + fderiv ℝ f z (0,1)*Y z := by
    intro z
    change fderiv ℝ (f * X) z (1,0) + fderiv ℝ (f * Y) z (0,1) = _
    rw [fderiv_mul (hdf z) (hdX z), fderiv_mul (hdf z) (hdY z)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  simp_rw [hexpand] at hgreen
  have hiMain : Integrable (fun z => f z * (fderiv ℝ X z (1,0) + fderiv ℝ Y z (0,1)))
      (volume.restrict (Icc a b)) := (hf.continuous.mul (hXx.add hYy)).integrableOn_Icc
  have hiX : Integrable (fun z => fderiv ℝ f z (1,0)*X z)
      (volume.restrict (Icc a b)) := (hfx.mul hX.continuous).integrableOn_Icc
  have hiY : Integrable (fun z => fderiv ℝ f z (0,1)*Y z)
      (volume.restrict (Icc a b)) := (hfy.mul hY.continuous).integrableOn_Icc
  have hsum := integral_add (hiMain.add hiX) hiY
  have hsumMain := integral_add hiMain hiX
  simp only [Pi.add_apply] at hsum hsumMain
  rw [hsum, hsumMain] at hgreen
  linarith


 theorem poincare_raw (a b : ℝ × ℝ) (hab : a ≤ b) (f : ℝ × ℝ → ℝ)
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
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
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
  have hgreen := green_raw a b hab f (fun z => χ z*f z) (fun _ => 0)
    hf hfχ contDiff_const
  have hzeroDeriv : ∀ z : ℝ × ℝ, fderiv ℝ (fun _ : ℝ × ℝ => (0:ℝ)) z = 0 := fun z => (hasFDerivAt_const (0:ℝ) z).fderiv
  simp only [hdx, hzeroDeriv, ContinuousLinearMap.zero_apply, add_zero, mul_zero,
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
