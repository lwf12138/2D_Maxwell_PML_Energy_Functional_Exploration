import LeanPML.PML.BalanceInterfaces

/-!
# V7 (7.1)–(7.2)：实际加权空间中的空间块抵消

先把单方向点态恒等式连接零吸收分支，再对真实 L² / WeightedL2 内积积分。
输入的 dU 只有配合上层 StateHasDerivAt 才是时间导数；此处整理已经求得的
spatialRate。ψ 的交叉项可积性来自加权空间，不要求无界 w 是普通 L² 乘子。
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open LeanPML.Analysis

namespace LeanPML.PML
variable {α : Type*} [MeasurableSpace α]

/-- 由 V7 (7.1) 及其后零区公式推出，原文未单列：单方向空间率加耗散
等于乘子通量。f=l−h；零区 f=0 是兼容输入，并非 si=sj=0 自动推出。 -/
theorem spatial_rate_add_dissipation_pointwise (c si sj h l g f df dl : ℝ)
    (hsi : 0 ≤ si) (hsj : 0 ≤ sj)
    (hf : f=l-h) (hdf : df=sj*h-si*l) (hdl : dl=g+df)
    (hzero : absorptionSum si sj=0 → f=0) :
    l*dl+energyWeightX c si sj*f*df+spatialDissipation c si sj h l =
      (g+c*h)*l := by
  by_cases ha_pos : 0 < absorptionSum si sj
  · have hidentity := spatial_rate_identity c si sj h l g ha_pos
    rw [hdl, hdf, hf, spatialDissipation, if_pos ha_pos]
    nlinarith only [hidentity]
  · have ha_zero : absorptionSum si sj=0 :=
      le_antisymm (le_of_not_gt ha_pos) (absorptionSum_nonneg si sj hsi hsj)
    have hp_zero := (absorptionSum_eq_zero_iff si sj hsi hsj).mp ha_zero
    have hf_zero : f=0 := hzero ha_zero
    have hl_eq : l=h := by linarith [hf]
    simp only [spatialDissipation, if_neg ha_pos, hf_zero, mul_zero, zero_mul, add_zero]
    rw [hdl, hdf, hp_zero.1, hp_zero.2, hl_eq]
    ring

private theorem coefficient_product_ae (ν : Measure α) (k : BoundedCoefficient α)
    (f : ScalarL2 ν) :
    ⇑(k.operator ν f) =ᵐ[ν] fun x => k.value x*f x :=
  coeFn_boundedMul ν k.value k.measurable k.bound k.abs_le f

/-- 从 L² 辅助演化得到代表函数的 a.e. 等式；原文未单列。
不能要求任意选出的代表函数逐点相等，故此步明确经过 coeFn_sub。 -/
private theorem auxiliary_evolution_ae (ν : Measure α)
    (k m : BoundedCoefficient α) (h l df : ScalarL2 ν)
    (hevolution : df=k.operator ν h-m.operator ν l) :
    ∀ᵐ x ∂ν, df x=k.value x*h x-m.value x*l x := by
  rw [hevolution]
  filter_upwards [Lp.coeFn_sub (k.operator ν h) (m.operator ν l),
    coefficient_product_ae ν k h, coefficient_product_ae ν m l]
    with x hsub hk hm
  simpa only [Pi.sub_apply, hk, hm] using hsub

/-- V7 (7.1)–(7.2) 的实际空间积分版本。
输入是两方向辅助演化及 Λ_t=∇V+ψ_t；gx、gy 的真实梯度意义由上层域接口给出。
输出完整乘子通量，尚未使用 Green，也没有删除零区 c|h|²。 -/
theorem spatialRate_add_dissipation (ν : Measure α) (C : SpatialAbsorption α)
    (U dU : FieldState ν C.wx C.wy) (gx gy : ScalarL2 ν)
    (hψx : physicalX ν C dU.ψx =
      C.rCoeff.operator ν (spatialComponentX U)-C.pCoeff.operator ν U.Λx)
    (hψy : physicalY ν C dU.ψy =
      C.pCoeff.operator ν (spatialComponentY U)-C.rCoeff.operator ν U.Λy)
    (hΛx : dU.Λx=gx+physicalX ν C dU.ψx)
    (hΛy : dU.Λy=gy+physicalY ν C dU.ψy) :
    spatialRate U dU + fieldSpatialDissipation ν C U =
      ⟪gx+C.c • spatialComponentX U,U.Λx⟫_ℝ+
      ⟪gy+C.c • spatialComponentY U,U.Λy⟫_ℝ := by
  let rate : α → ℝ := fun x =>
    U.Λx x*dU.Λx x+U.Λy x*dU.Λy x+
      C.wx x*physicalX ν C U.ψx x*physicalX ν C dU.ψx x+
      C.wy x*physicalY ν C U.ψy x*physicalY ν C dU.ψy x
  let flux : α → ℝ := fun x =>
    (gx x+C.c*spatialComponentX U x)*U.Λx x+
      (gy x+C.c*spatialComponentY U x)*U.Λy x
  have hlx_integrable := integrable_product ν U.Λx dU.Λx
  have hly_integrable := integrable_product ν U.Λy dU.Λy
  have hwx_integrable := integrable_weighted_product ν C.wx C.wx_measurable C.wx_gap U.ψx dU.ψx
  have hwy_integrable := integrable_weighted_product ν C.wy C.wy_measurable C.wy_gap U.ψy dU.ψy
  have hrate_integrable : Integrable rate ν :=
    ((hlx_integrable.fun_add hly_integrable).fun_add hwx_integrable).fun_add hwy_integrable
  -- 这里只改写已经合法的普通/加权内积；没有交换逐点导数与积分。
  have hrate_integral : spatialRate U dU=∫ x,rate x ∂ν := by
    unfold spatialRate
    rw [inner_eq_integral, inner_eq_integral,
      weighted_inner_eq_integral ν C.wx C.wx_measurable C.wx_gap,
      weighted_inner_eq_integral ν C.wy C.wy_measurable C.wy_gap]
    dsimp only [rate, physicalX, physicalY]
    rw [integral_add ((hlx_integrable.fun_add hly_integrable).fun_add hwx_integrable)
        hwy_integrable,
      integral_add (hlx_integrable.fun_add hly_integrable) hwx_integrable,
      integral_add hlx_integrable hly_integrable]
  have hflux_integral :
      ⟪gx+C.c • spatialComponentX U,U.Λx⟫_ℝ+
        ⟪gy+C.c • spatialComponentY U,U.Λy⟫_ℝ = ∫ x,flux x ∂ν := by
    have hgx := integrable_product ν gx U.Λx
    have hgy := integrable_product ν gy U.Λy
    have hhx := (integrable_product ν (spatialComponentX U) U.Λx).const_mul C.c
    have hhy := (integrable_product ν (spatialComponentY U) U.Λy).const_mul C.c
    simp only [inner_add_left, real_inner_smul_left, inner_eq_integral]
    dsimp [flux]
    simp only [add_mul, mul_assoc]
    rw [integral_add (hgx.fun_add hhx) (hgy.fun_add hhy),
      integral_add hgx hhx, integral_add hgy hhy, integral_const_mul, integral_const_mul]
  -- 两方向原演化先转换为 a.e. 关系。x 用 r*h−p*Λ，y 用 p*h−r*Λ。
  have hdx := auxiliary_evolution_ae ν C.rCoeff C.pCoeff
    (spatialComponentX U) U.Λx (physicalX ν C dU.ψx) hψx
  have hdy := auxiliary_evolution_ae ν C.pCoeff C.rCoeff
    (spatialComponentY U) U.Λy (physicalY ν C dU.ψy) hψy
  have hzeroX := physicalL2_zero_on_zero ν C.wx C.wx_measurable C.wx_gap U.ψx
  have hzeroY := physicalL2_zero_on_zero ν C.wy C.wy_measurable C.wy_gap U.ψy
  rw [hrate_integral, fieldSpatialDissipation_eq_integral, hflux_integral,
    ← integral_add hrate_integrable (fieldSpatialDissipation_integrable ν C U)]
  apply integral_congr_ae
  -- 在同一个满测度集合上统一所有代表函数的加减关系，再调用点态恒等式。
  -- physicalL2_zero_on_zero 在零区给 ψ=0，故该分支仍保留 c*h² 的抵消。
  filter_upwards [hdx,hdy,hzeroX,hzeroY,
    Lp.coeFn_sub U.Λx (physicalX ν C U.ψx),
    Lp.coeFn_sub U.Λy (physicalY ν C U.ψy),
    Lp.coeFn_add gx (physicalX ν C dU.ψx),
    Lp.coeFn_add gy (physicalY ν C dU.ψy)]
    with x hdx_point hdy_point hzeroX_point hzeroY_point hx_component hy_component
      hx_deriv hy_deriv
  have hx : spatialComponentX U x=U.Λx x-physicalX ν C U.ψx x := hx_component
  have hy : spatialComponentY U x=U.Λy x-physicalY ν C U.ψy x := hy_component
  have hdlx : dU.Λx x=gx x+physicalX ν C dU.ψx x := by
    rw [hΛx]
    exact hx_deriv
  have hdly : dU.Λy x=gy x+physicalY ν C dU.ψy x := by
    rw [hΛy]
    exact hy_deriv
  have hidentityX := spatial_rate_add_dissipation_pointwise C.c (C.p x) (C.r x)
    (spatialComponentX U x) (U.Λx x) (gx x) (physicalX ν C U.ψx x)
    (physicalX ν C dU.ψx x) (dU.Λx x)
    (C.p_nonneg x) (C.r_nonneg x) (by linarith) hdx_point hdlx
    (fun ha_zero => hzeroX_point ((C.wx_eq_zero_iff x).mpr ha_zero))
  have hidentityY := spatial_rate_add_dissipation_pointwise C.c (C.r x) (C.p x)
    (spatialComponentY U x) (U.Λy x) (gy x) (physicalY ν C U.ψy x)
    (physicalY ν C dU.ψy x) (dU.Λy x)
    (C.r_nonneg x) (C.p_nonneg x) (by linarith) hdy_point hdly
    (fun ha_zero => hzeroY_point ((C.wy_eq_zero_iff x).mpr
      (by simpa only [SpatialAbsorption.a, absorptionSum, add_comm] using ha_zero)))
  rw [energyWeightX_swap] at hidentityY
  dsimp only [rate,flux,fieldSpatialDissipationDensity,spatialDissipation2D]
  dsimp only [SpatialAbsorption.wx, SpatialAbsorption.wy]
  linarith

end LeanPML.PML
