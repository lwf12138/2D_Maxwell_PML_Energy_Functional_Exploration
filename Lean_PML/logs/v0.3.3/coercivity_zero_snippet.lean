import LeanPML.PML.Coercivity

noncomputable section
open MeasureTheory
open LeanPML.Analysis
namespace LeanPML.PML
variable {α : Type*} [MeasurableSpace α]

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

end LeanPML.PML
