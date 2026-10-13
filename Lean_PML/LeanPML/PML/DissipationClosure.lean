import LeanPML.PML.Coercivity
import LeanPML.PML.BalanceAbstract
import LeanPML.PML.GradientControl

/-!
# V7 §9：两类耗散分别吸收两个不利项

本文件复用实际 L²/加权能量和耗散。顺序是 (9.1) 的单层下界、
(9.6) 的空间吸收、(9.7) 的 Debye 吸收，最后保留原文的 1/2 与 1/4。
局部代数和实际积分分开；真实时间关系由同源路径及邻域 primitive 方程取得。
具体矩形的 Green、迹、Poincaré 和时间交换仍是显式条件接口。
-/

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace
open LeanPML.Analysis

namespace LeanPML.PML
variable {α : Type*} [MeasurableSpace α]

/-- §9.1 未编号的单层计算，电块部分：丢弃 aV²、bcv² 两个非负项。
这里 v、V 是实数，尚未宣称真实时间导数；下方积分定理使用此引理。 -/
theorem electricRemainder_lower_pointwise (ε a b c v V : ℝ)
    (hε : 0 ≤ ε) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    -c*ε*V^2 ≤ electricRemainder ε a b c v V := by
  have hpositiveV : 0 ≤ ε*a*V^2 := mul_nonneg (mul_nonneg hε ha) (sq_nonneg V)
  have hpositivev : 0 ≤ ε*b*c*v^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hε hb) hc) (sq_nonneg v)
  unfold electricRemainder
  nlinarith only [hpositiveV, hpositivev]

/-- §9.1 未编号的极化估计：R=κV−τRdot，cτ≤1/4，故
D_D≥τ/(2κ) Rdot²−2cκV²。κ>0 使消分母不改变序关系。
先用 (κV+τRdot)²≥0 得到两项平方和估计，再保留半份 Debye 耗散。 -/
theorem polarRemainder_lower_pointwise (a b c κ τ V R z Rdot : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hκ : 0 < κ) (hτ : 0 ≤ τ) (hac : 0 ≤ a*c-b)
    (hsmall : c*τ ≤ 1/4) (hpolar : R + τ*Rdot = κ*V) :
    τ/(2*κ)*Rdot^2 - 2*c*κ*V^2 ≤ polarRemainder a b c κ τ R z Rdot := by
  have hRbound : R^2 ≤ 2*κ^2*V^2 + 2*τ^2*Rdot^2 := by
    have hR : R = κ*V - τ*Rdot := by linarith only [hpolar]
    rw [hR]
    nlinarith only [sq_nonneg (κ*V + τ*Rdot)]
  have hRscaled := mul_le_mul_of_nonneg_left hRbound hc
  have hmaterial : 0 ≤ τ*(1/2-2*c*τ)*Rdot^2 := by
    have hgap : 0 ≤ 1/2-2*c*τ := by linarith
    exact mul_nonneg (mul_nonneg hτ hgap) (sq_nonneg Rdot)
  have hpositiveR : 0 ≤ (a+τ*(a*c-b))*R^2 :=
    mul_nonneg (add_nonneg ha (mul_nonneg hτ hac)) (sq_nonneg R)
  have hpositivez : 0 ≤ b*c*z^2 := mul_nonneg (mul_nonneg hb hc) (sq_nonneg z)
  -- κ>0 已显式给出；把 1/κ 移到左侧后仅剩多项式不等式。
  apply (le_div_iff₀ hκ).2
  have hcancel : (τ/(2*κ)*Rdot^2 - 2*c*κ*V^2)*κ =
      τ/2*Rdot^2 - 2*c*κ^2*V^2 := by field_simp
  change (τ/(2*κ)*Rdot^2 - 2*c*κ*V^2)*κ ≤ _
  rw [hcancel]
  nlinarith only [hRscaled, hmaterial, hpositiveR, hpositivez]

/-- §9.1 的实际 L² 单层下界。hpolar 是状态与导数数据的 Debye 关系；
低层允许输入该关系，最终同源路径入口会从真实兼容求导获得它。
原幅度条件给 a,b,ac−b≥0，原阈值给 cτ≤1/4；不要求任何吸收正下界。 -/
theorem fieldDissipation_lower (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (U : FieldState ν C.wx C.wy) (Rdot : ScalarL2 ν)
    (hpolar : U.R + τ • Rdot = κ • U.V) :
    fieldSpatialDissipation ν C U + μ*τ/(2*κ)*‖Rdot‖^2 -
      μ*C.c*materialA ε κ*‖U.V‖^2 ≤ fieldDissipation ν C ε κ τ μ U Rdot := by
  have hsmall : C.c*τ ≤ 1/4 :=
    (c_mul_tau_bounds ε κ τ μ CP C.c hp.ε_pos hp.κ_pos hp.τ_pos hp.μ_pos
      hp.CP_pos C.c_pos hp.c_le_threshold).2.2.2
  have hpolar_ae : ∀ᵐ x ∂ν, U.R x + τ*Rdot x = κ*U.V x := by
    filter_upwards [Lp.coeFn_add U.R (τ • Rdot), Lp.coeFn_smul τ Rdot,
      Lp.coeFn_smul κ U.V] with x hadd hRt hV
    have heq := congrArg (fun f : ScalarL2 ν => f x) hpolar
    simpa only [hadd, hRt, hV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using heq
  have hV := (Lp.memLp U.V).integrable_sq
  have hRt := (Lp.memLp Rdot).integrable_sq
  have helectric := integral_mono_ae (hV.const_mul (-C.c*ε))
    (fieldElectricRemainder_integrable ν C ε U)
    (Filter.Eventually.of_forall (fun x => electricRemainder_lower_pointwise ε
      (C.a x) (C.b x) C.c (U.v x) (U.V x) hp.ε_pos.le
      (absorptionSum_nonneg _ _ (C.p_nonneg x) (C.r_nonneg x))
      (mul_nonneg (C.p_nonneg x) (C.r_nonneg x)) C.c_pos.le))
  have hpolar_bound : ∀ᵐ x ∂ν, τ/(2*κ)*(Rdot x)^2 - 2*C.c*κ*(U.V x)^2 ≤
      polarRemainder (C.a x) (C.b x) C.c κ τ (U.R x) (U.z x) (Rdot x) := by
    filter_upwards [hpolar_ae] with x hx
    have hac := absorptionSum_mul_sub_product_nonneg (C.p x) (C.r x) C.c
      (C.p_nonneg x) (C.r_nonneg x)
      (absorptionSum_le_half _ _ C.S C.c (C.p_le_S x) (C.r_le_S x) C.S_le_quarter)
    exact polarRemainder_lower_pointwise _ _ _ _ _ _ _ _ _
      (absorptionSum_nonneg _ _ (C.p_nonneg x) (C.r_nonneg x))
      (mul_nonneg (C.p_nonneg x) (C.r_nonneg x)) C.c_pos.le hp.κ_pos hp.τ_pos.le hac hsmall hx
  have hpolar_integral := integral_mono_ae
    ((hRt.const_mul (τ/(2*κ))).sub (hV.const_mul (2*C.c*κ)))
    (fieldPolarRemainder_integrable ν C κ τ U Rdot) hpolar_bound
  -- 各平方及块密度均已证明可积，现在才使用积分的线性和序关系。
  rw [integral_const_mul, ← norm_sq_eq_integral,
    ← fieldElectricRemainder_eq_integral] at helectric
  simp only [Pi.sub_apply] at hpolar_integral
  rw [integral_sub (hRt.const_mul (τ/(2*κ))) (hV.const_mul (2*C.c*κ)),
    integral_const_mul, integral_const_mul, ← norm_sq_eq_integral, ← norm_sq_eq_integral,
    ← fieldPolarRemainder_eq_integral] at hpolar_integral
  have helectric_scaled := mul_le_mul_of_nonneg_left helectric hp.μ_pos.le
  have hpolar_scaled := mul_le_mul_of_nonneg_left hpolar_integral hp.μ_pos.le
  unfold fieldDissipation materialA
  ring_nf at helectric_scaled hpolar_scaled ⊢
  linarith only [helectric_scaled, hpolar_scaled]

/-- 由 (5.2)–(5.3) 推出的幅度平方链，用于 (9.6) 后的吸收。
Nonempty 只说空间载体 α 非空；二维载体 ℝ×ℝ 自带此实例，仍允许零测度。
取一个点，由 0≤p≤S 得 S≥0，因此平方幅度界合法；不要求吸收严格为正。 -/
theorem scale_amplitude_chain [Nonempty α] (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP) :
    0 ≤ C.S ∧ scaleK ε κ μ CP*C.S^2 ≤ scaleK ε κ μ CP*C.c^2/16 ∧
      scaleK ε κ μ CP*C.c^2/16 ≤ 1/16 ∧ (1/16 : ℝ) ≤ 1 := by
  let x : α := Classical.choice (inferInstance : Nonempty α)
  have hS_nonneg : 0 ≤ C.S := (C.p_nonneg x).trans (C.p_le_S x)
  have hc_pos := C.c_pos
  have hK_pos := scaleK_pos ε κ μ CP hp.ε_pos hp.κ_pos hp.μ_pos hp.CP_pos
  have hS_square : C.S^2 ≤ C.c^2/16 := by
    nlinarith only [hS_nonneg, C.S_le_quarter, hc_pos]
  have hscaled := mul_le_mul_of_nonneg_left hS_square hK_pos.le
  have hsmall := (le_threshold_iff_explicit ε κ τ μ CP C.c hp.ε_pos hp.κ_pos
    hp.τ_pos hp.μ_pos hp.CP_pos C.c_pos).mp hp.c_le_threshold
  refine ⟨hS_nonneg, ?_, ?_, by norm_num⟩
  · nlinarith only [hscaled]
  · nlinarith only [hsmall.1]

/-- V7 §9.1、§9.3 使用的两条真实 Debye 关系。
先对邻域内原极化兼容求导取得 first.polar，再在开集内求导取得 second.polar。
配合 z_t=R、v_t=V 的真实同源证据，得到 R+τR_t=κV；不是对单点等式求导。 -/
theorem debye_relations_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    {G : ConditionalGreenDomain ν Boundary} {C : SpatialAbsorption α} {I : Set ℝ}
    (ε κ τ μ : ℝ) (path : SameSourcePath ν C.wx C.wy I)
    (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    (path.base t).R + τ • (path.first t).R = κ • (path.base t).V ∧
    (path.first t).R + τ • (path.second t).R = κ • (path.first t).V := by
  have hfirst_all : ∀ s ∈ interior I, PrimitiveAtConditional G C ε κ τ μ
      (path.first s) (path.second s) (regular.first_v s) (regular.first_flux s) :=
    fun s hs => primitive_first_Conditional ε κ τ μ path regular hbase hs
  have hfirst_polar : PolarConstraint κ τ (path.first t) := (hfirst_all t ht).polar
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ interior I := isOpen_interior.mem_nhds ht
  have hsecond_polar : PolarConstraint κ τ (path.second t) :=
    polarConstraint_derivative_Conditional κ τ (path.deriv_first t (interior_subset ht))
      (hnear.mono (fun s hs => (hfirst_all s hs).polar))
  have hbase_coordinates := sameSource_coordinates path (interior_subset ht)
  have hfirst_coordinates := sameSource_first_coordinates_of_mem_interior path ht
  change (path.first t).z + τ • (path.first t).R = κ • (path.first t).v at hfirst_polar
  change (path.second t).z + τ • (path.second t).R = κ • (path.second t).v at hsecond_polar
  rw [hbase_coordinates.1, hbase_coordinates.2] at hfirst_polar
  rw [hfirst_coordinates.1, hfirst_coordinates.2] at hsecond_polar
  exact ⟨hfirst_polar, hsecond_polar⟩

/-- V7 (9.1)：两层实际耗散下界。P_t、P_tt 分别为 first.R、second.R，
均由 SameSourcePath 的 HasDerivAt 绑定。两条单层估计相加，尚未吸收负项。 -/
theorem dissipation7_preliminary_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP) {I : Set ℝ}
    (path : SameSourcePath ν C.wx C.wy I) (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    fieldSpatialDissipation ν C (path.base t) +
      scaleK ε κ μ CP * fieldSpatialDissipation ν C (path.first t) +
      μ*τ/(2*κ)*(‖(path.first t).R‖^2 + scaleK ε κ μ CP*‖(path.second t).R‖^2) -
      μ*C.c*materialA ε κ*‖(path.base t).V‖^2 -
      μ*C.c*materialA ε κ*scaleK ε κ μ CP*‖(path.first t).V‖^2 ≤
      dissipation7 ν C ε κ τ μ CP path t := by
  have hrelations := debye_relations_Conditional ε κ τ μ path regular hbase ht
  have hbase_lower := fieldDissipation_lower ν C ε κ τ μ CP hp
    (path.base t) (path.first t).R hrelations.1
  have hfirst_lower := fieldDissipation_lower ν C ε κ τ μ CP hp
    (path.first t) (path.second t).R hrelations.2
  have hK_nonneg : 0 ≤ scaleK ε κ μ CP :=
    (scaleK_pos ε κ μ CP hp.ε_pos hp.κ_pos hp.μ_pos hp.CP_pos).le
  have hfirst_scaled := mul_le_mul_of_nonneg_left hfirst_lower hK_nonneg
  unfold dissipation7 twoLayerDissipation
  ring_nf at hbase_lower hfirst_scaled ⊢
  linarith only [hbase_lower, hfirst_scaled]

/-- §9.3 未编号的二项平方估计，适用于任何真实 Hilbert 场。
这只是低层代数/范数引理，最终 (9.7) 会从真实 Debye 求导提供 hrelation。 -/
theorem debye_velocity_square_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (κ τ : ℝ) (V R Rdot : H) (hrelation : R + τ • Rdot = κ • V) :
    κ^2*‖V‖^2 ≤ 2*(‖R‖^2+τ^2*‖Rdot‖^2) := by
  have hsum := norm_sub_sq_le_twice R (-(τ • Rdot))
  simp only [sub_neg_eq_add, norm_neg] at hsum
  rw [hrelation, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at hsum
  simpa only [mul_pow, sq_abs] using hsum

/-- V7 §9.3、(9.7) 之前未编号的分项估计。
将 κ²‖V‖²≤2(‖R‖²+τ²‖Rdot‖²) 乘正系数，再除 κ²；
右侧两项将在下条定理分别由两个材料阈值控制。 -/
theorem debye_absorption_split (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (V R Rdot : ScalarL2 ν) (hrelation : R + τ • Rdot = κ • V) :
    μ*C.c*materialA ε κ*scaleK ε κ μ CP*‖V‖^2 ≤
      (2*μ*C.c*materialA ε κ*scaleK ε κ μ CP/κ^2)*‖R‖^2 +
      (2*μ*C.c*materialA ε κ*scaleK ε κ μ CP*τ^2/κ^2)*‖Rdot‖^2 := by
  have hκ_pos := hp.κ_pos
  have hc_pos := C.c_pos
  have hμ_pos := hp.μ_pos
  have hA_pos := materialA_pos ε κ hp.ε_pos hp.κ_pos
  have hK_pos := scaleK_pos ε κ μ CP hp.ε_pos hp.κ_pos hp.μ_pos hp.CP_pos
  have hnorm := debye_velocity_square_le κ τ V R Rdot hrelation
  have hscaled := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ μ*C.c*materialA ε κ*scaleK ε κ μ CP by positivity)
  apply (mul_le_mul_iff_right₀ (show 0 < κ^2 by positivity)).mp
  have hcancel : κ^2 *
      ((2*μ*C.c*materialA ε κ*scaleK ε κ μ CP/κ^2)*‖R‖^2 +
       (2*μ*C.c*materialA ε κ*scaleK ε κ μ CP*τ^2/κ^2)*‖Rdot‖^2) =
      2*μ*C.c*materialA ε κ*scaleK ε κ μ CP*(‖R‖^2+τ^2*‖Rdot‖^2) := by
    field_simp
  rw [hcancel]
  nlinarith only [hscaled]

/-- V7 (9.7) 的低层吸收：先使用 κ²‖V‖² 的二项界，
再分别使用 8cAK≤κτ 与 8cAτ≤κ。两条条件来自 c≤c_*，而非新增假设。
κ>0、τ>0 给出分母和乘法因子的正性；没有重复使用空间耗散。 -/
theorem debye_absorption (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (V R Rdot : ScalarL2 ν) (hrelation : R + τ • Rdot = κ • V) :
    μ*C.c*materialA ε κ*scaleK ε κ μ CP*‖V‖^2 ≤
      μ*τ/(4*κ)*(‖R‖^2+scaleK ε κ μ CP*‖Rdot‖^2) := by
  have hc_pos := C.c_pos
  have hκ_pos := hp.κ_pos
  have hμ_pos := hp.μ_pos
  have hτ_pos := hp.τ_pos
  have hA_pos := materialA_pos ε κ hp.ε_pos hp.κ_pos
  have hK_pos := scaleK_pos ε κ μ CP hp.ε_pos hp.κ_pos hp.μ_pos hp.CP_pos
  have hsmall := (le_threshold_iff_explicit ε κ τ μ CP C.c hp.ε_pos hp.κ_pos
    hp.τ_pos hp.μ_pos hp.CP_pos C.c_pos).mp hp.c_le_threshold
  have hsplit := debye_absorption_split ν C ε κ τ μ CP hp V R Rdot hrelation
  have hscaled := mul_le_mul_of_nonneg_left hsplit (sq_nonneg κ)
  have hcancel_split : κ^2 *
      ((2*μ*C.c*materialA ε κ*scaleK ε κ μ CP/κ^2)*‖R‖^2 +
       (2*μ*C.c*materialA ε κ*scaleK ε κ μ CP*τ^2/κ^2)*‖Rdot‖^2) =
      2*μ*C.c*materialA ε κ*scaleK ε κ μ CP*(‖R‖^2+τ^2*‖Rdot‖^2) := by
    field_simp
  rw [hcancel_split] at hscaled
  have hfirst_coeff : 8*μ*C.c*materialA ε κ*scaleK ε κ μ CP ≤ μ*κ*τ := by
    have h := mul_le_mul_of_nonneg_left hsmall.2.1 hp.μ_pos.le
    nlinarith only [h]
  have hsecond_coeff : 8*μ*C.c*materialA ε κ*scaleK ε κ μ CP*τ^2 ≤
      μ*κ*τ*scaleK ε κ μ CP := by
    have h := mul_le_mul_of_nonneg_left hsmall.2.2
      (show 0 ≤ μ*τ*scaleK ε κ μ CP by positivity)
    nlinarith only [h]
  have hfirst_term := mul_le_mul_of_nonneg_right hfirst_coeff (sq_nonneg ‖R‖)
  have hsecond_term := mul_le_mul_of_nonneg_right hsecond_coeff (sq_nonneg ‖Rdot‖)
  -- 乘以正的 4κ² 后，目标没有任何分母；原阈值恰好支付两项系数。
  apply (mul_le_mul_iff_right₀ (show 0 < 4*κ^2 by positivity)).mp
  have hcancel : (4*κ^2)*(μ*τ/(4*κ)*(‖R‖^2+scaleK ε κ μ CP*‖Rdot‖^2)) =
      μ*κ*τ*(‖R‖^2+scaleK ε κ μ CP*‖Rdot‖^2) := by
    field_simp
  rw [hcancel]
  nlinarith only [hscaled, hfirst_term, hsecond_term]

/-- V7 (9.7) 的真实同源入口：κE_t=P_t+τP_tt 已由 debye_relations_Conditional
对原极化关系求导；本定理不输入这条派生等式，更不输入目标吸收估计。 -/
theorem debye_absorption_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP) {I : Set ℝ}
    (path : SameSourcePath ν C.wx C.wy I) (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    μ*C.c*materialA ε κ*scaleK ε κ μ CP*‖(path.first t).V‖^2 ≤
      μ*τ/(4*κ)*(‖(path.first t).R‖^2+scaleK ε κ μ CP*‖(path.second t).R‖^2) := by
  exact debye_absorption ν C ε κ τ μ CP hp _ _ _
    (debye_relations_Conditional ε κ τ μ path regular hbase ht).2

/-- V7 (9.6) 第一行到最后一行：先对 E 使用与 Green 相同迹核的 Poincaré，
再调用由原辅助演化证明的 (9.5) 和真实空间耗散 (9.3)。
输入没有 J 控制式；这些估计均由本工程定理获得。 -/
theorem spatial_absorption_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
      ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
        (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2)) {I : Set ℝ}
    (path : SameSourcePath ν C.wx C.wy I) (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    μ*C.c*materialA ε κ*‖(path.base t).V‖^2 ≤
      scaleK ε κ μ CP/2 * (fieldSpatialDissipation ν C (path.first t) +
        C.S^2*fieldSpatialDissipation ν C (path.base t)) := by
  have ht_mem : t ∈ I := interior_subset ht
  have hμ_pos := hp.μ_pos
  have hc_pos := C.c_pos
  have hA_pos := materialA_pos ε κ hp.ε_pos hp.κ_pos
  have hCP_pos := hp.CP_pos
  have hgradient := gradient_control_Conditional ε κ τ μ path regular hbase ht
  have hpoincare := estimate (regular.first_v t) (regular.trace_first_v t ht_mem)
  have hcoordinate := (sameSource_coordinates path ht_mem).1
  rw [regular.first_v_eq t ht_mem, hcoordinate] at hpoincare
  have hgradient_scaled := mul_le_mul_of_nonneg_left hgradient (sq_nonneg CP)
  have hnorm : ‖(path.base t).V‖^2 ≤
      3*CP^2*(fieldJ ν C (path.first t) + C.S^2*fieldJ ν C (path.base t)) := by
    nlinarith only [hpoincare, hgradient_scaled]
  have hnorm_scaled := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ μ*C.c*materialA ε κ by positivity)
  have hSbase := (fieldSpatialDissipation_ge_J ν C (path.base t)).2
  have hSfirst := (fieldSpatialDissipation_ge_J ν C (path.first t)).2
  have hSbase_scaled := mul_le_mul_of_nonneg_left hSbase (sq_nonneg C.S)
  have hJbudget : 3*C.c/4*(fieldJ ν C (path.first t) + C.S^2*fieldJ ν C (path.base t)) ≤
      fieldSpatialDissipation ν C (path.first t) +
        C.S^2*fieldSpatialDissipation ν C (path.base t) := by
    nlinarith only [hSfirst, hSbase_scaled]
  have hJbudget_scaled := mul_le_mul_of_nonneg_left hJbudget
    (show 0 ≤ 4*μ*materialA ε κ*CP^2 by positivity)
  unfold scaleK
  nlinarith only [hnorm_scaled, hJbudget_scaled]

/-- (9.6) 后的精确预算：KS²≤1/16≤1，故 E 项最多消耗空间耗散的一半。
Nonempty α 仅用于说明 S≥0；零吸收域和零测度仍完整保留。 -/
theorem spatial_absorption_half_Conditional [Nonempty α]
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
      ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
        (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2)) {I : Set ℝ}
    (path : SameSourcePath ν C.wx C.wy I) (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    μ*C.c*materialA ε κ*‖(path.base t).V‖^2 ≤
      (fieldSpatialDissipation ν C (path.base t) +
        scaleK ε κ μ CP*fieldSpatialDissipation ν C (path.first t))/2 := by
  have hfirst := spatial_absorption_Conditional G C ε κ τ μ CP hp estimate path regular hbase ht
  have hchain := scale_amplitude_chain C ε κ τ μ CP hp
  have hsmall : scaleK ε κ μ CP*C.S^2 ≤ 1 := hchain.2.1.trans (hchain.2.2.1.trans hchain.2.2.2)
  have hspatial_nonneg := fieldSpatialDissipation_nonneg ν C (path.base t)
  have hbudget := mul_le_mul_of_nonneg_right hsmall hspatial_nonneg
  nlinarith only [hfirst, hbudget]

/-- V7 (9.7) 后未编号下界，即 (6.8) 的定量耗散闭合。
空间正项支付 E 的负项，Debye 正项支付 E_t 的负项；各保留 1/2、1/4。
这里直接使用现有 dissipation7，而非另设任意实数耗散。
所需 Green/Poincaré/时间交换仍是具体矩形待兑现的接口。 -/
theorem dissipation7_lower_Conditional [Nonempty α]
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
      ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
        (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2)) {I : Set ℝ}
    (path : SameSourcePath ν C.wx C.wy I) (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    (fieldSpatialDissipation ν C (path.base t) +
      scaleK ε κ μ CP*fieldSpatialDissipation ν C (path.first t))/2 +
      μ*τ/(4*κ)*(‖(path.first t).R‖^2 + scaleK ε κ μ CP*‖(path.second t).R‖^2) ≤
      dissipation7 ν C ε κ τ μ CP path t := by
  have hpreliminary := dissipation7_preliminary_Conditional G C ε κ τ μ CP hp path regular hbase ht
  have hspatial := spatial_absorption_half_Conditional G C ε κ τ μ CP hp estimate path regular hbase ht
  have hdebye := debye_absorption_Conditional G C ε κ τ μ CP hp path regular hbase ht
  -- 同时扣除两类负项，避免重复使用同一份耗散预算。
  ring_nf at hpreliminary hspatial hdebye ⊢
  linarith only [hpreliminary, hspatial, hdebye]

/-- (6.8) 的非负性是上述定量下界的推论。
空间耗散已由积分非负性证明；剩余 Debye 项是正系数乘实际 L² 平方范数。
本条尚不声称时间单调性，后续 MainAbstract 还要结合真实能量求导和连续性。 -/
theorem dissipation7_nonneg_Conditional [Nonempty α]
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
      ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
        (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2)) {I : Set ℝ}
    (path : SameSourcePath ν C.wx C.wy I) (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) : 0 ≤ dissipation7 ν C ε κ τ μ CP path t := by
  have hlower := dissipation7_lower_Conditional G C ε κ τ μ CP hp estimate path regular hbase ht
  have hK_pos := scaleK_pos ε κ μ CP hp.ε_pos hp.κ_pos hp.μ_pos hp.CP_pos
  have hκ_pos := hp.κ_pos
  have hμ_pos := hp.μ_pos
  have hτ_pos := hp.τ_pos
  have hSbase := fieldSpatialDissipation_nonneg ν C (path.base t)
  have hSfirst := fieldSpatialDissipation_nonneg ν C (path.first t)
  have hremaining : 0 ≤
      (fieldSpatialDissipation ν C (path.base t) +
        scaleK ε κ μ CP*fieldSpatialDissipation ν C (path.first t))/2 +
        μ*τ/(4*κ)*(‖(path.first t).R‖^2 + scaleK ε κ μ CP*‖(path.second t).R‖^2) := by
    positivity
  exact hremaining.trans hlower

end LeanPML.PML
