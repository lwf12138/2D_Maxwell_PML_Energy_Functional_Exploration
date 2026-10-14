import LeanPML.PML.WeakLiftCompatibility
import LeanPML.PML.Obstructions.UnrestrictedData

/-!
# 弱兼容入口排除原增长族

复用 V7 命题 2.2 的已验证非零紧支 ψ。原增长解的初态 Q=∇ψ
作为实际 L² 场；全零吸收下任何合法提升必须 Q=0，故它不能误入新兼容类。
增长解的全八式、真实导数和 t² 积分增长沿用旧模块，不重新声称存在性。
-/
noncomputable section
open MeasureTheory
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
open LeanPML.PML LeanPML.PML.Weak LeanPML.PML.Obstructions
open LeanPML.Examples.FullDomain
namespace LeanPML.Examples.WeakRegression

/-- 旧实际增长族在 t=0 的八个 L² 场；μ=1，Qx/Qy 为真实空间偏导的 L² 表示。 -/
def growthInitial : OriginalState unitSquare where
  E := 0
  Hx := 0
  Hy := 0
  P := 0
  Z1 := 0
  Z2 := 0
  Qx := SmoothField.toL2 unitSquare physicalBump.derivativeX
  Qy := SmoothField.toL2 unitSquare physicalBump.derivativeY

/-- 不是仅检查一个名字：两个 Q 分量平方和正性来自旧非零紧支函数的真实 L² 梯度证书。 -/
theorem growthInitial_auxiliary_positive :
    0 < ‖growthInitial.Qx‖^2 + ‖growthInitial.Qy‖^2 :=
  fullProfile_unrestricted_gradient_positive.2

/-- 全零吸收的任意合法弱提升都强制 Qx=Qy=0。
此结论使用实际重构字段，不假设目标“初值不兼容”。 -/
theorem zeroAbsorption_auxiliary_zero (D : Rect) (ε κ τ μ : ℝ)
    (F : OriginalState D) (L : CompatibleLift D liftExampleAbsorption ε κ τ μ F) :
    F.Qx = 0 ∧ F.Qy = 0 := by
  have hp (g : ScalarL2 D.measure) : liftExampleAbsorption.pCoeff.operator D.measure g = 0 := by
    change (BoundedCoefficient.const 0).operator D.measure g = 0
    rw [BoundedCoefficient.operator_const, zero_smul]
  have hr (g : ScalarL2 D.measure) : liftExampleAbsorption.rCoeff.operator D.measure g = 0 := by
    change (BoundedCoefficient.const 0).operator D.measure g = 0
    rw [BoundedCoefficient.operator_const, zero_smul]
  exact ⟨L.auxiliaryX.trans (hp _), by rw [L.auxiliaryY, hr, neg_zero]⟩

/-- 原增长初态不能成为新弱主定理的兼容初态：不存在任何合法提升，
而非只排除 u₀=q₀=0 的某个选择。没有增加磁场约束来排除该族。 -/
theorem growthInitial_no_weak_compatible_lift (ε κ τ μ : ℝ) :
    ¬ Nonempty (CompatibleLift unitSquare liftExampleAbsorption ε κ τ μ growthInitial) := by
  rintro ⟨L⟩
  have hQ := zeroAbsorption_auxiliary_zero unitSquare ε κ τ μ growthInitial L
  have hpositive := growthInitial_auxiliary_positive
  rw [hQ.1, hQ.2] at hpositive
  norm_num at hpositive

/-- 单层失败回归仍沿用精确指定候选；不扩张为任意单层能量的不可能性。 -/
theorem single_layer_scope_preserved :
    LeanPML.PML.Obstructions.initialDissipation 1 1 1 1 smallC 0 0 1 < 0 := by
  exact singleLayer_candidate_failure_regression

end LeanPML.Examples.WeakRegression
