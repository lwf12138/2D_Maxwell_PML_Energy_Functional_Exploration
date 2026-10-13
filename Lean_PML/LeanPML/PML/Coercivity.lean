import LeanPML.PML.BalanceInterfaces

/-!
# V7 §8：受空间约束的能量正定性

顺序：(8.3) 的梯度与 Poincaré 控制 → (8.1) 消元和 (8.2) 系数界
→ §8.1、§8.2 的 Young 估计 → (6.7) 两层界及零分离。
所有范数均为实际普通或加权 L² 范数。Poincaré 仍是明确的零迹域接口；
没有把任意状态的 v、z 当作独立正定矩阵坐标，也未安装未经证明的 Norm 实例。
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open LeanPML.Analysis

namespace LeanPML.PML
variable {α : Type*} [MeasurableSpace α]

/-- V7 (5.2)–(5.3) 的原始材料条件。吸收的非负性与幅度已在 C 中。
字段仅含正性和论文阈值；(8.2)、能量界均由后续定理推出。 -/
structure CoercivityParameters (C : SpatialAbsorption α) (ε κ τ μ CP : ℝ) : Prop where
  ε_pos : 0 < ε
  κ_pos : 0 < κ
  τ_pos : 0 < τ
  μ_pos : 0 < μ
  CP_pos : 0 < CP
  c_le_threshold : C.c ≤ threshold ε κ τ μ CP

/-- (8.3) 使用的条件性 Poincaré 接口。zeroTrace 是梯度定义域中的零迹子域；
具体 Green 接口可取 trace 的核。estimate 是一般函数的不等式，不含能量。
矩形 Sobolev 实例留到后续具体空间阶段。 -/
structure ConditionalPoincare {ν : Measure α}
    (spatial : ConditionalSpatialDomain ν) (CP : ℝ) where
  zeroTrace : Submodule ℝ spatial.domain
  estimate : ∀ f : spatial.domain, f ∈ zeroTrace →
    ‖(f : ScalarL2 ν)‖ ^ 2 ≤
      CP ^ 2 * (‖spatial.componentX f‖ ^ 2 + ‖spatial.componentY f‖ ^ 2)

/-- (6.1)、§8 的状态约束：实际梯度分量接口、零迹域成员、极化兼容。
它们都不是待证明的能量不等式。 -/
structure StateCoercivityConstraints (ν : Measure α) (C : SpatialAbsorption α)
    (spatialDomain : ConditionalSpatialDomain ν) {CP : ℝ}
    (poincare : ConditionalPoincare spatialDomain CP) (κ τ : ℝ)
    (U : FieldState ν C.wx C.wy) : Prop where
  spatial : FieldSpatialConstraint ν C spatialDomain U
  zeroTrace : (⟨U.v, spatial.mem_domain⟩ : spatialDomain.domain) ∈ poincare.zeroTrace
  polar : PolarConstraint κ τ U

/-- V7 (8.3) 的 B_sp，等于 (6.2) 空间能量的两倍；四项均为真实平方范数。 -/
def spatialBudget {ν : Measure α} {C : SpatialAbsorption α}
    (U : FieldState ν C.wx C.wy) : ℝ :=
  ‖U.Λx‖ ^ 2 + ‖U.Λy‖ ^ 2 + ‖U.ψx‖ ^ 2 + ‖U.ψy‖ ^ 2

theorem spatialBudget_nonneg {ν : Measure α} {C : SpatialAbsorption α}
    (U : FieldState ν C.wx C.wy) : 0 ≤ spatialBudget U := by
  unfold spatialBudget
  positivity

/-- (8.3) 的基本 Hilbert 估计，原文未单列：差的平方至多两倍平方和。
用于 Λ−ψ；不要求无界权重是普通 L² 乘子。 -/
theorem norm_sub_sq_le_twice {H : Type*} [NormedAddCommGroup H] (x y : H) :
    ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have htriangle : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have hsquare : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr htriangle
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- (8.3) 第一条：Λ=∇v+ψ 与已证加权嵌入推出梯度平方控制。
零区由 physicalX/Y 的零延拓处理，不在零区要求 w≥1。 -/
theorem gradient_square_le_spatialBudget (ν : Measure α) (C : SpatialAbsorption α)
    (spatial : ConditionalSpatialDomain ν) (U : FieldState ν C.wx C.wy)
    (hsp : FieldSpatialConstraint ν C spatial U) :
    ‖spatial.componentX ⟨U.v, hsp.mem_domain⟩‖ ^ 2 +
      ‖spatial.componentY ⟨U.v, hsp.mem_domain⟩‖ ^ 2 ≤ 2 * spatialBudget U := by
  have hx : spatial.componentX ⟨U.v, hsp.mem_domain⟩ =
      U.Λx - physicalX ν C U.ψx := eq_sub_of_add_eq hsp.fluxX.symm
  have hy : spatial.componentY ⟨U.v, hsp.mem_domain⟩ =
      U.Λy - physicalY ν C U.ψy := eq_sub_of_add_eq hsp.fluxY.symm
  have hdiffx := norm_sub_sq_le_twice U.Λx (physicalX ν C U.ψx)
  have hdiffy := norm_sub_sq_le_twice U.Λy (physicalY ν C U.ψy)
  have hembedding := auxiliary_embedding_square ν C U
  rw [hx, hy]
  unfold spatialBudget
  linarith

/-- (8.3) 第二条：先使用一般零迹 Poincaré，再调用上一梯度界。
此结论是条件性空间分析；Poincaré 本身尚未在矩形上证明。 -/
theorem state_norm_sq_le_spatialBudget (ν : Measure α) (C : SpatialAbsorption α)
    (spatial : ConditionalSpatialDomain ν) (CP : ℝ)
    (poincare : ConditionalPoincare spatial CP) (κ τ : ℝ)
    (U : FieldState ν C.wx C.wy)
    (hU : StateCoercivityConstraints ν C spatial poincare κ τ U) :
    ‖U.v‖ ^ 2 ≤ 2 * CP ^ 2 * spatialBudget U := by
  have hpoincare := poincare.estimate ⟨U.v, hU.spatial.mem_domain⟩ hU.zeroTrace
  have hgradient := gradient_square_le_spatialBudget ν C spatial U hU.spatial
  have hscaled := mul_le_mul_of_nonneg_left hgradient (sq_nonneg CP)
  calc
    ‖U.v‖ ^ 2 ≤ CP ^ 2 *
        (‖spatial.componentX ⟨U.v, hU.spatial.mem_domain⟩‖ ^ 2 +
         ‖spatial.componentY ⟨U.v, hU.spatial.mem_domain⟩‖ ^ 2) := hpoincare
    _ ≤ CP ^ 2 * (2 * spatialBudget U) := hscaled
    _ = 2 * CP ^ 2 * spatialBudget U := by ring

/-- §8.1、§8.2 电块的点态 Young 估计。
b+ac 的界来自 (8.2)；这里导数槽 V 仅是瞬时数值，没有声称时间求导。
两个平方 (V±2cv)² 控制交叉项，供下方实际积分估计调用。 -/
theorem electric_energy_bounds_pointwise (ε a b c v V : ℝ)
    (hε : 0 ≤ ε) (he : 0 ≤ b + a*c ∧ b + a*c ≤ (9/16:ℝ)*c^2) :
    ε / 2 * V^2 - 2*ε*c^2*v^2 ≤ 2*electricEnergy ε a b c v V ∧
    2*electricEnergy ε a b c v V ≤ 2*ε*V^2 + 3*ε*c^2*v^2 := by
  have hdiag_lower : 0 ≤ ε * (b+a*c)*v^2 :=
    mul_nonneg (mul_nonneg hε he.1) (sq_nonneg v)
  have hdiag_upper := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right he.2 (sq_nonneg v)) hε
  have hyoung_lower : 0 ≤ ε * (V + 2*c*v)^2 := mul_nonneg hε (sq_nonneg _)
  have hyoung_upper : 0 ≤ ε * (V - 2*c*v)^2 := mul_nonneg hε (sq_nonneg _)
  unfold electricEnergy
  constructor <;> nlinarith [mul_nonneg hε (sq_nonneg V), mul_nonneg hε (sq_nonneg (c*v))]

/-- §8.1、§8.2 极化块的点态估计。先调用 (8.1) 消去 z，再使用 (8.2)。
κ>0 允许乘除 κ；B=1−aτ−bτ² 的 0≤B≤1 控制两个 Young 平方中的系数。
结果用于实际 L² 积分，不把它误称为独立分量上的正定性。 -/
theorem polar_energy_bounds_pointwise (a b c κ τ v R z : ℝ) (hκ : 0 < κ)
    (hcompat : z + τ*R = κ*v)
    (hAR : 3/4 ≤ polarCoeffAR a b c τ ∧ polarCoeffAR a b c τ ≤ 5/4)
    (hB : 0 ≤ 1-a*τ-b*τ^2 ∧ 1-a*τ-b*τ^2 ≤ 1)
    (hG : 0 ≤ polarCoeffG a b c τ ∧ polarCoeffG a b c τ ≤ (37/64:ℝ)*c^2) :
    1/(2*κ)*R^2 - 4*κ*c^2*v^2 ≤ 2*polarEnergy a b c κ τ R z ∧
    2*polarEnergy a b c κ τ R z ≤ 2/κ*R^2 + 3*κ*c^2*v^2 := by
  let B : ℝ := 1-a*τ-b*τ^2
  have hBsq : B^2 ≤ 1 := by dsimp [B]; nlinarith [hB.1, hB.2]
  have hBscaled := mul_le_mul_of_nonneg_left hBsq (sq_nonneg (κ*c*v))
  have hARlower := mul_le_mul_of_nonneg_right hAR.1 (sq_nonneg R)
  have hARupper := mul_le_mul_of_nonneg_right hAR.2 (sq_nonneg R)
  have hGlower : 0 ≤ κ^2 * polarCoeffG a b c τ * v^2 :=
    mul_nonneg (mul_nonneg (sq_nonneg κ) hG.1) (sq_nonneg v)
  have hGupper := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hG.2 (sq_nonneg v)) (sq_nonneg κ)
  have hyoungLower : 0 ≤ (R + 4*κ*c*B*v)^2 := sq_nonneg _
  have hyoungUpper : 0 ≤ (R - 2*κ*c*B*v)^2 := sq_nonneg _
  have hreduce := polarEnergy_eq_reduced a b c κ τ v R z hcompat
  have hscaled : κ * (2*polarEnergy a b c κ τ R z) =
      polarCoeffAR a b c τ * R^2 + 2*κ*c*B*v*R +
        κ^2*polarCoeffG a b c τ*v^2 := by
    rw [hreduce]
    dsimp [B]
    field_simp
  have hlower : 1/2*R^2 - 4*κ^2*c^2*v^2 ≤
      κ*(2*polarEnergy a b c κ τ R z) := by
    rw [hscaled]
    nlinarith only [hARlower, hGlower, hyoungLower, hBscaled]
  have hupper : κ*(2*polarEnergy a b c κ τ R z) ≤
      2*R^2 + 3*κ^2*c^2*v^2 := by
    rw [hscaled]
    nlinarith [sq_nonneg R, sq_nonneg (κ*c*v)]
  constructor
  · apply (mul_le_mul_iff_right₀ hκ).mp
    calc
      κ*(1/(2*κ)*R^2 - 4*κ*c^2*v^2) =
        1/2*R^2 - 4*κ^2*c^2*v^2 := by field_simp
      _ ≤ κ*(2*polarEnergy a b c κ τ R z) := hlower
  · apply (mul_le_mul_iff_right₀ hκ).mp
    calc
      κ*(2*polarEnergy a b c κ τ R z) ≤ 2*R^2 + 3*κ^2*c^2*v^2 := by
        nlinarith only [hupper]
      _ = κ*(2/κ*R^2 + 3*κ*c^2*v^2) := by field_simp

/-- (6.1) 在实际 L² 商类中的约束给出 a.e. 代表函数约束。
只在积分估计中使用这个几乎处处等式，不读取等价类在指定点的值。 -/
theorem polarConstraint_ae {ν : Measure α} {C : SpatialAbsorption α}
    (κ τ : ℝ) (U : FieldState ν C.wx C.wy) (hcompat : PolarConstraint κ τ U) :
    ∀ᵐ x ∂ν, U.z x + τ * U.R x = κ * U.v x := by
  filter_upwards [Lp.coeFn_add U.z (τ • U.R), Lp.coeFn_smul τ U.R,
    Lp.coeFn_smul κ U.v] with x hadd hR hv
  have heq := congrArg (fun f : ScalarL2 ν => f x) hcompat
  simpa only [hadd, hR, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using heq

/-- §8 电块 Young 估计的实际空间积分版本。
每个平方与旧块密度都先有可积性；随后积分序关系给出 L² 范数估计。 -/
theorem fieldElectric_bounds (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (U : FieldState ν C.wx C.wy) :
    ε/2*‖U.V‖^2 - 2*ε*C.c^2*‖U.v‖^2 ≤ 2*fieldElectric ν C ε U ∧
    2*fieldElectric ν C ε U ≤ 2*ε*‖U.V‖^2 + 3*ε*C.c^2*‖U.v‖^2 := by
  have hV := (Lp.memLp U.V).integrable_sq
  have hv := (Lp.memLp U.v).integrable_sq
  have henergy := (fieldElectric_integrable ν C ε U).const_mul 2
  have hpoint : ∀ x, ε/2*(U.V x)^2 - 2*ε*C.c^2*(U.v x)^2 ≤
        2*electricEnergy ε (C.a x) (C.b x) C.c (U.v x) (U.V x) ∧
      2*electricEnergy ε (C.a x) (C.b x) C.c (U.v x) (U.V x) ≤
        2*ε*(U.V x)^2 + 3*ε*C.c^2*(U.v x)^2 := by
    intro x
    have hcoeff := polar_coefficients_bounds_of_threshold ε κ τ μ CP
      (C.p x) (C.r x) C.S C.c hp.ε_pos hp.κ_pos hp.τ_pos hp.μ_pos hp.CP_pos
      C.c_pos hp.c_le_threshold (C.p_nonneg x) (C.r_nonneg x)
      (C.p_le_S x) (C.r_le_S x) C.S_le_quarter
    exact electric_energy_bounds_pointwise ε (C.a x) (C.b x) C.c (U.v x) (U.V x)
      hp.ε_pos.le hcoeff.2.2.2
  have hlower := integral_mono_ae
    ((hV.const_mul (ε/2)).sub (hv.const_mul (2*ε*C.c^2))) henergy
    (Filter.Eventually.of_forall (fun x => (hpoint x).1))
  have hupper := integral_mono_ae henergy
    ((hV.const_mul (2*ε)).add (hv.const_mul (3*ε*C.c^2)))
    (Filter.Eventually.of_forall (fun x => (hpoint x).2))
  simp only [Pi.sub_apply, Pi.add_apply] at hlower hupper
  rw [integral_sub (hV.const_mul (ε/2)) (hv.const_mul (2*ε*C.c^2)),
    integral_const_mul, integral_const_mul, integral_const_mul,
    ← norm_sq_eq_integral, ← norm_sq_eq_integral, ← fieldElectric_eq_integral] at hlower
  rw [integral_add (hV.const_mul (2*ε)) (hv.const_mul (3*ε*C.c^2)),
    integral_const_mul, integral_const_mul, integral_const_mul,
    ← norm_sq_eq_integral, ← norm_sq_eq_integral, ← fieldElectric_eq_integral] at hupper
  exact ⟨hlower, hupper⟩

/-- §8 极化块的实际积分估计。(8.1) 只需 a.e. 兼容，(8.2) 从原阈值推出。
这一步没有使用 Poincaré；其不利 v² 项将在主定理中由空间预算吸收。 -/
theorem fieldPolar_bounds (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (U : FieldState ν C.wx C.wy) (hcompat : PolarConstraint κ τ U) :
    1/(2*κ)*‖U.R‖^2 - 4*κ*C.c^2*‖U.v‖^2 ≤ 2*fieldPolar ν C κ τ U ∧
    2*fieldPolar ν C κ τ U ≤ 2/κ*‖U.R‖^2 + 3*κ*C.c^2*‖U.v‖^2 := by
  have hR := (Lp.memLp U.R).integrable_sq
  have hv := (Lp.memLp U.v).integrable_sq
  have henergy := (fieldPolar_integrable ν C κ τ U).const_mul 2
  have hpoint : ∀ᵐ x ∂ν,
      1/(2*κ)*(U.R x)^2 - 4*κ*C.c^2*(U.v x)^2 ≤
        2*polarEnergy (C.a x) (C.b x) C.c κ τ (U.R x) (U.z x) ∧
      2*polarEnergy (C.a x) (C.b x) C.c κ τ (U.R x) (U.z x) ≤
        2/κ*(U.R x)^2 + 3*κ*C.c^2*(U.v x)^2 := by
    filter_upwards [polarConstraint_ae κ τ U hcompat] with x hx
    have hcoeff := polar_coefficients_bounds_of_threshold ε κ τ μ CP
      (C.p x) (C.r x) C.S C.c hp.ε_pos hp.κ_pos hp.τ_pos hp.μ_pos hp.CP_pos
      C.c_pos hp.c_le_threshold (C.p_nonneg x) (C.r_nonneg x)
      (C.p_le_S x) (C.r_le_S x) C.S_le_quarter
    exact polar_energy_bounds_pointwise (C.a x) (C.b x) C.c κ τ (U.v x) (U.R x)
      (U.z x) hp.κ_pos hx hcoeff.1 hcoeff.2.1 hcoeff.2.2.1
  have hlower := integral_mono_ae
    ((hR.const_mul (1/(2*κ))).sub (hv.const_mul (4*κ*C.c^2))) henergy
    (hpoint.mono (fun _ hx => hx.1))
  have hupper := integral_mono_ae henergy
    ((hR.const_mul (2/κ)).add (hv.const_mul (3*κ*C.c^2)))
    (hpoint.mono (fun _ hx => hx.2))
  simp only [Pi.sub_apply, Pi.add_apply] at hlower hupper
  rw [integral_sub (hR.const_mul (1/(2*κ))) (hv.const_mul (4*κ*C.c^2)),
    integral_const_mul, integral_const_mul, integral_const_mul,
    ← norm_sq_eq_integral, ← norm_sq_eq_integral, ← fieldPolar_eq_integral] at hlower
  rw [integral_add (hR.const_mul (2/κ)) (hv.const_mul (3*κ*C.c^2)),
    integral_const_mul, integral_const_mul, integral_const_mul,
    ← norm_sq_eq_integral, ← norm_sq_eq_integral, ← fieldPolar_eq_integral] at hupper
  exact ⟨hlower, hupper⟩

/-- V7 (6.5) 的图平方非负，只需要材料正性；尚未使用空间约束。 -/
theorem graphSquare_nonneg {ν : Measure α} {C : SpatialAbsorption α}
    (ε κ μ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hμ : 0 ≤ μ)
    (U : FieldState ν C.wx C.wy) : 0 ≤ graphSquare ε κ μ U := by
  unfold graphSquare
  positivity

/-- B_sp 是图平方的一部分，其余两项由材料正性非负。 -/
theorem spatialBudget_le_graphSquare {ν : Measure α} {C : SpatialAbsorption α}
    (ε κ μ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hμ : 0 ≤ μ)
    (U : FieldState ν C.wx C.wy) : spatialBudget U ≤ graphSquare ε κ μ U := by
  have hv : 0 ≤ μ*ε*‖U.V‖^2 := by positivity
  have hR : 0 ≤ μ/κ*‖U.R‖^2 := by positivity
  unfold graphSquare spatialBudget
  linarith

/-- V7 §8.1、§8.2 主结论：同一受约束状态满足 N²/4≤F_c≤N²。
参数只输入原始正性与 c≤c_*；系数界来自旧定理，Young 项在上面逐块证明。
Poincaré 仅用于吸收 v²；因此本条是明确的条件性空间结论。 -/
theorem fieldEnergy_bounds_Conditional (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (spatial : ConditionalSpatialDomain ν) (poincare : ConditionalPoincare spatial CP)
    (U : FieldState ν C.wx C.wy)
    (hU : StateCoercivityConstraints ν C spatial poincare κ τ U) :
    graphSquare ε κ μ U / 4 ≤ fieldEnergy ν C ε κ τ μ U ∧
      fieldEnergy ν C ε κ τ μ U ≤ graphSquare ε κ μ U := by
  have hε_pos := hp.ε_pos
  have hκ_pos := hp.κ_pos
  have hμ_pos := hp.μ_pos
  have he := fieldElectric_bounds ν C ε κ τ μ CP hp U
  have hD := fieldPolar_bounds ν C ε κ τ μ CP hp U hU.polar
  have hv := state_norm_sq_le_spatialBudget ν C spatial CP poincare κ τ U hU
  have hB := spatialBudget_nonneg U
  have hthreshold := (le_threshold_iff_explicit ε κ τ μ CP C.c hp.ε_pos hp.κ_pos
    hp.τ_pos hp.μ_pos hp.CP_pos C.c_pos).mp hp.c_le_threshold
  have hsmall : C.c^2 * (8*μ*(ε+2*κ)*CP^2) ≤ 1 := hthreshold.1
  have hspatial : 2*fieldSpatial U = spatialBudget U := by
    unfold fieldSpatial spatialBudget
    ring
  -- 下界：2μAc²‖v‖²≤4μAc²CP²B_sp≤B_sp/2。
  have hbadLower := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ 2*μ*(ε+2*κ)*C.c^2 by positivity)
  have hsmallBudget := mul_le_mul_of_nonneg_right hsmall hB
  have habsorbLower : 2*μ*(ε+2*κ)*C.c^2*‖U.v‖^2 ≤ spatialBudget U / 2 := by
    nlinarith only [hbadLower, hsmallBudget]
  -- 上界只需 ≤B_sp。原文此处的严格 < 在 B_sp=0 时不成立，故不用严格号。
  have hbadUpper := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ 3*μ*(ε+κ)*C.c^2 by positivity)
  have hAcompare : 6*μ*(ε+κ)*CP^2*C.c^2*spatialBudget U ≤
      8*μ*(ε+2*κ)*CP^2*C.c^2*spatialBudget U := by
    have hgap : 0 ≤ (2*ε+10*κ)*μ*CP^2*C.c^2*spatialBudget U := by positivity
    nlinarith only [hgap]
  have habsorbUpper : 3*μ*(ε+κ)*C.c^2*‖U.v‖^2 ≤ spatialBudget U := by
    nlinarith only [hbadUpper, hAcompare, hsmallBudget]
  have heLower := mul_le_mul_of_nonneg_left he.1 hp.μ_pos.le
  have heUpper := mul_le_mul_of_nonneg_left he.2 hp.μ_pos.le
  have hDLower := mul_le_mul_of_nonneg_left hD.1 hp.μ_pos.le
  have hDUpper := mul_le_mul_of_nonneg_left hD.2 hp.μ_pos.le
  have hκ_ne : κ ≠ 0 := ne_of_gt hp.κ_pos
  have hhalf : 1/(2*κ) = (1/κ)/2 := by field_simp
  have htwo : 2/κ = 2*(1/κ) := by ring
  rw [hhalf] at hDLower
  rw [htwo] at hDUpper
  unfold graphSquare fieldEnergy
  simp only [div_eq_mul_inv] at *
  unfold spatialBudget at *
  constructor <;> nlinarith only [heLower, heUpper, hDLower, hDUpper,
    habsorbLower, habsorbUpper, hspatial]

/-- (6.7) 对同源路径的两层应用上一条，固定 K≥0 保持不等式方向。
这里只是能量/图平方估计；未使用也未证明两层耗散非负。 -/
theorem energy7_bounds_Conditional (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (spatial : ConditionalSpatialDomain ν) (poincare : ConditionalPoincare spatial CP)
    {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I) (t : ℝ)
    (hbase : StateCoercivityConstraints ν C spatial poincare κ τ (path.base t))
    (hfirst : StateCoercivityConstraints ν C spatial poincare κ τ (path.first t)) :
    graphSquare7 ν C ε κ μ CP path t / 4 ≤ energy7 ν C ε κ τ μ CP path t ∧
      energy7 ν C ε κ τ μ CP path t ≤ graphSquare7 ν C ε κ μ CP path t := by
  have hbase_bounds := fieldEnergy_bounds_Conditional ν C ε κ τ μ CP hp spatial poincare _ hbase
  have hfirst_bounds := fieldEnergy_bounds_Conditional ν C ε κ τ μ CP hp spatial poincare _ hfirst
  have hK : 0 ≤ scaleK ε κ μ CP :=
    (scaleK_pos ε κ μ CP hp.ε_pos hp.κ_pos hp.μ_pos hp.CP_pos).le
  have hlower := mul_le_mul_of_nonneg_left hfirst_bounds.1 hK
  have hupper := mul_le_mul_of_nonneg_left hfirst_bounds.2 hK
  unfold energy7 graphSquare7 twoLayerEnergy twoLayerGraphSquare
  constructor <;> linarith

/-- (6.7) 的零分离含义：八个实际场坐标均为零。
这只是命题定义，不为未经证明的图平方安装 Norm 实例。 -/
def FieldStateIsZero {ν : Measure α} {C : SpatialAbsorption α}
    (U : FieldState ν C.wx C.wy) : Prop :=
  U.v=0 ∧ U.V=0 ∧ U.R=0 ∧ U.z=0 ∧ U.ψx=0 ∧ U.ψy=0 ∧ U.Λx=0 ∧ U.Λy=0

/-- 由 (6.5)、(8.3) 及极化约束推出：图平方为零时所有受约束场坐标为零。
V、R、Λ、ψ 直接由正平方项消失；v 还需 Poincaré，z 还需极化兼容。 -/
theorem graphSquare_zero_Conditional (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (spatial : ConditionalSpatialDomain ν) (poincare : ConditionalPoincare spatial CP)
    (U : FieldState ν C.wx C.wy)
    (hU : StateCoercivityConstraints ν C spatial poincare κ τ U)
    (hzero : graphSquare ε κ μ U = 0) : FieldStateIsZero U := by
  have hvelocity_coeff : 0 < μ*ε := mul_pos hp.μ_pos hp.ε_pos
  have hpolar_coeff : 0 < μ/κ := div_pos hp.μ_pos hp.κ_pos
  have hvelocity_nonneg : 0 ≤ μ*ε*‖U.V‖^2 :=
    mul_nonneg hvelocity_coeff.le (sq_nonneg _)
  have hpolar_nonneg : 0 ≤ μ/κ*‖U.R‖^2 :=
    mul_nonneg hpolar_coeff.le (sq_nonneg _)
  have hcomponents : μ*ε*‖U.V‖^2 + μ/κ*‖U.R‖^2 +
      (‖U.Λx‖^2+‖U.Λy‖^2) + (‖U.ψx‖^2+‖U.ψy‖^2) = 0 := hzero
  have hV_sq : ‖U.V‖^2 = 0 := by
    nlinarith [sq_nonneg ‖U.V‖, sq_nonneg ‖U.Λx‖, sq_nonneg ‖U.Λy‖,
      sq_nonneg ‖U.ψx‖, sq_nonneg ‖U.ψy‖]
  have hR_sq : ‖U.R‖^2 = 0 := by
    nlinarith [sq_nonneg ‖U.R‖, sq_nonneg ‖U.Λx‖, sq_nonneg ‖U.Λy‖,
      sq_nonneg ‖U.ψx‖, sq_nonneg ‖U.ψy‖]
  have hΛx_sq : ‖U.Λx‖^2 = 0 := by
    nlinarith [sq_nonneg ‖U.Λx‖, sq_nonneg ‖U.Λy‖,
      sq_nonneg ‖U.ψx‖, sq_nonneg ‖U.ψy‖]
  have hΛy_sq : ‖U.Λy‖^2 = 0 := by
    nlinarith [sq_nonneg ‖U.Λx‖, sq_nonneg ‖U.Λy‖,
      sq_nonneg ‖U.ψx‖, sq_nonneg ‖U.ψy‖]
  have hψx_sq : ‖U.ψx‖^2 = 0 := by
    nlinarith [sq_nonneg ‖U.Λx‖, sq_nonneg ‖U.Λy‖,
      sq_nonneg ‖U.ψx‖, sq_nonneg ‖U.ψy‖]
  have hψy_sq : ‖U.ψy‖^2 = 0 := by
    nlinarith [sq_nonneg ‖U.Λx‖, sq_nonneg ‖U.Λy‖,
      sq_nonneg ‖U.ψx‖, sq_nonneg ‖U.ψy‖]
  have hV : U.V=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hV_sq)
  have hR : U.R=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hR_sq)
  have hΛx : U.Λx=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hΛx_sq)
  have hΛy : U.Λy=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hΛy_sq)
  have hψx : U.ψx=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hψx_sq)
  have hψy : U.ψy=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hψy_sq)
  have hv_bound := state_norm_sq_le_spatialBudget ν C spatial CP poincare κ τ U hU
  have hbudget : spatialBudget U = 0 := by
    simp only [spatialBudget, hΛx_sq, hΛy_sq, hψx_sq, hψy_sq, add_zero]
  rw [hbudget, mul_zero] at hv_bound
  have hv_sq : ‖U.v‖^2=0 := le_antisymm hv_bound (sq_nonneg _)
  have hv : U.v=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hv_sq)
  have hz : U.z=0 := by
    have hpolar : U.z + τ • U.R = κ • U.v := hU.polar
    simpa only [hR, hv, smul_zero, add_zero] using hpolar
  exact ⟨hv,hV,hR,hz,hψx,hψy,hΛx,hΛy⟩

/-- (6.7) 的单层能量零分离；先由下界得到图平方为零，再调用上述约束论证。
不要求耗散严格正，不排除零状态，也不是任意独立坐标上的矩阵正定性。 -/
theorem fieldEnergy_zero_Conditional (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (spatial : ConditionalSpatialDomain ν) (poincare : ConditionalPoincare spatial CP)
    (U : FieldState ν C.wx C.wy)
    (hU : StateCoercivityConstraints ν C spatial poincare κ τ U)
    (hzero : fieldEnergy ν C ε κ τ μ U = 0) : FieldStateIsZero U := by
  have hlower := (fieldEnergy_bounds_Conditional ν C ε κ τ μ CP hp spatial poincare U hU).1
  have hgraph_nonneg := graphSquare_nonneg ε κ μ hp.ε_pos.le hp.κ_pos.le hp.μ_pos.le U
  have hgraph_zero : graphSquare ε κ μ U=0 := by rw [hzero] at hlower; linarith
  exact graphSquare_zero_Conditional ν C ε κ τ μ CP hp spatial poincare U hU hgraph_zero


/-- (6.7) 的两层零分离：E₇=0 蕴含同源两层的全部约束坐标为零。
K>0 来自原材料条件；不是由任意两个独立状态的名称推断其同源性。 -/
theorem energy7_zero_Conditional (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (spatial : ConditionalSpatialDomain ν) (poincare : ConditionalPoincare spatial CP)
    {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I) (t : ℝ)
    (hbase : StateCoercivityConstraints ν C spatial poincare κ τ (path.base t))
    (hfirst : StateCoercivityConstraints ν C spatial poincare κ τ (path.first t))
    (hzero : energy7 ν C ε κ τ μ CP path t = 0) :
    FieldStateIsZero (path.base t) ∧ FieldStateIsZero (path.first t) := by
  have hlower := (energy7_bounds_Conditional ν C ε κ τ μ CP hp spatial poincare
    path t hbase hfirst).1
  have hbase_nonneg := graphSquare_nonneg ε κ μ hp.ε_pos.le hp.κ_pos.le hp.μ_pos.le (path.base t)
  have hfirst_nonneg := graphSquare_nonneg ε κ μ hp.ε_pos.le hp.κ_pos.le hp.μ_pos.le (path.first t)
  have hK_pos := scaleK_pos ε κ μ CP hp.ε_pos hp.κ_pos hp.μ_pos hp.CP_pos
  rw [hzero] at hlower
  unfold graphSquare7 twoLayerGraphSquare at hlower
  have hbase_zero : graphSquare ε κ μ (path.base t) = 0 := by
    have hweighted_nonneg := mul_nonneg hK_pos.le hfirst_nonneg
    linarith
  have hfirst_zero : graphSquare ε κ μ (path.first t) = 0 := by
    nlinarith only [hlower, hbase_zero, hfirst_nonneg, hK_pos]
  exact ⟨graphSquare_zero_Conditional ν C ε κ τ μ CP hp spatial poincare _ hbase hbase_zero,
    graphSquare_zero_Conditional ν C ε κ τ μ CP hp spatial poincare _ hfirst hfirst_zero⟩

/-- 将 Poincaré 的零迹子域明确取为本阶段 Green 迹算子的核。
estimate 仍是尚待矩形实例证明的一般 Poincaré 假设；这个构造只统一两个接口，
绝不从 Green 公式本身推导 Poincaré。 -/
def ConditionalPoincare.ofGreenTrace {ν : Measure α} {Boundary : Type*}
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (CP : ℝ)
    (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
      ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
        (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2)) :
    ConditionalPoincare G.spatial CP where
  zeroTrace := LinearMap.ker G.trace
  estimate f hf := estimate f hf

/-- Green/Poincaré 共用迹的状态入口。零迹输入是 G.trace v=0；
ofGreenTrace 将它直接解释为同一个零迹域成员，而非另一套无关边界条件。 -/
theorem stateCoercivityConstraints_of_GreenTrace {ν : Measure α}
    {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (C : SpatialAbsorption α) (G : ConditionalGreenDomain ν Boundary) (CP κ τ : ℝ)
    (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
      ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
        (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2))
    (U : FieldState ν C.wx C.wy)
    (hsp : FieldSpatialConstraint ν C G.spatial U)
    (htrace : G.trace ⟨U.v, hsp.mem_domain⟩ = 0)
    (hpolar : PolarConstraint κ τ U) :
    StateCoercivityConstraints ν C G.spatial
      (ConditionalPoincare.ofGreenTrace G CP estimate) κ τ U :=
  ⟨hsp, htrace, hpolar⟩

/-- 同源路径原层的零迹与上述 Poincaré 核一致。这里只接收已在空间路径接口
明确列出的 u 零迹；原层空间兼容和极化兼容仍分别输入，不从路径名字推断。 -/
theorem base_coercivityConstraints_of_GreenTrace {ν : Measure α}
    {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (C : SpatialAbsorption α) (G : ConditionalGreenDomain ν Boundary) (CP κ τ : ℝ)
    (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
      ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
        (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2))
    {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I)
    (regular : ConditionalSpatialPath G C path) {t : ℝ} (ht : t ∈ I)
    (hsp : FieldSpatialConstraint ν C G.spatial (path.base t))
    (hpolar : PolarConstraint κ τ (path.base t)) :
    StateCoercivityConstraints ν C G.spatial
      (ConditionalPoincare.ofGreenTrace G CP estimate) κ τ (path.base t) := by
  apply stateCoercivityConstraints_of_GreenTrace C G CP κ τ estimate _ hsp _ hpolar
  have hdomain : (⟨(path.base t).v, hsp.mem_domain⟩ : G.spatial.domain) =
      regular.base_v t := Subtype.ext (regular.base_v_eq t ht).symm
  rw [hdomain]
  exact regular.trace_base_v t ht

/-- 导数层同样使用空间路径明确列出的 E 零迹；本条桥接不能替代能量律中
另外需要的 E_t 零迹。两种用途在 BalanceAbstract 与本文件中分开。 -/
theorem first_coercivityConstraints_of_GreenTrace {ν : Measure α}
    {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (C : SpatialAbsorption α) (G : ConditionalGreenDomain ν Boundary) (CP κ τ : ℝ)
    (estimate : ∀ f : G.spatial.domain, G.trace f = 0 →
      ‖(f : ScalarL2 ν)‖^2 ≤ CP^2 *
        (‖G.spatial.componentX f‖^2 + ‖G.spatial.componentY f‖^2))
    {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I)
    (regular : ConditionalSpatialPath G C path) {t : ℝ} (ht : t ∈ I)
    (hsp : FieldSpatialConstraint ν C G.spatial (path.first t))
    (hpolar : PolarConstraint κ τ (path.first t)) :
    StateCoercivityConstraints ν C G.spatial
      (ConditionalPoincare.ofGreenTrace G CP estimate) κ τ (path.first t) := by
  apply stateCoercivityConstraints_of_GreenTrace C G CP κ τ estimate _ hsp _ hpolar
  have hdomain : (⟨(path.first t).v, hsp.mem_domain⟩ : G.spatial.domain) =
      regular.first_v t := Subtype.ext (regular.first_v_eq t ht).symm
  rw [hdomain]
  exact regular.trace_first_v t ht

end LeanPML.PML

