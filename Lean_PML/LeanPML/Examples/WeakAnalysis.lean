import LeanPML.Rectangle.WeakPaths
import LeanPML.Examples.WeakSpaces
import LeanPML.PML.AuxiliaryMemory

/-!
# 新弱分析结论的非零调用

复用 v0.5 的物理区紧支 bump，实际调用弱 Green、弱 Poincaré、图路径求导。
这些是空间和时间接口的回归，不是尚未合成的弱 PML 主定理调用。
辅助 ODE 另用非零指数路径核验；不冒称完整 PDE 解。
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
namespace LeanPML.Examples.WeakAnalysis

/-- 真实非零 H₀¹ 成员：函数和弱梯度同时由旧 bump 的光滑图给出。 -/
def nonzeroTest : zeroBoundaryGraph unitSquare :=
  ⟨smoothToWeakH1 unitSquare WeakSpaces.physicalTest.field,
    test_mem_zeroBoundaryGraph unitSquare WeakSpaces.physicalTest⟩

/-- 非零弱场上的真实积分 Green；通量取 bump 的真实梯度，具有弱散度。
本调用没有传入 Green 或边界消失公式。 -/
theorem nonzero_green :
    ⟪nonzeroTest.val.val 1,
      SmoothField.toL2 unitSquare WeakSpaces.physicalTest.field.derivativeX⟫_ℝ +
    ⟪nonzeroTest.val.val 2,
      SmoothField.toL2 unitSquare WeakSpaces.physicalTest.field.derivativeY⟫_ℝ =
    -⟪nonzeroTest.val.val 0,
      SmoothField.toL2 unitSquare WeakSpaces.physicalTest.field.derivativeX.derivativeX +
      SmoothField.toL2 unitSquare WeakSpaces.physicalTest.field.derivativeY.derivativeY⟫_ℝ :=
  weak_green unitSquare nonzeroTest
    (smoothToWeakHDiv unitSquare WeakSpaces.physicalTest.field.derivativeX
      WeakSpaces.physicalTest.field.derivativeY)

/-- 弱 Poincaré 的非零调用，CP 由实际 unitSquare 得到 4，故平方系数 16。 -/
theorem nonzero_poincare :
    nonzeroTest.val.val 0 ≠ 0 ∧
    ‖nonzeroTest.val.val 0‖ ^ 2 ≤ 16 *
      (‖nonzeroTest.val.val 1‖ ^ 2 + ‖nonzeroTest.val.val 2‖ ^ 2) := by
  refine ⟨WeakSpaces.physicalTest_nonzero_member.2, ?_⟩
  have hestimate := weak_poincare unitSquare nonzeroTest
  norm_num [poincareConstant, unitSquare, Rect.Lx] at hestimate ⊢
  exact hestimate

/-- 非恒定 H¹ 图路径 s↦s·bump 的真实导数；空间弱梯度的导数由连续投影推出。
空间成员来自非零紧支函数，不从普通 L² 逐点求导跳过图拓扑。 -/
theorem nonzero_graph_path_derivative (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => (s • nonzeroTest.val).val i) (nonzeroTest.val.val i) t := by
  have hgraph : HasDerivAt (fun s : ℝ => s • nonzeroTest.val) nonzeroTest.val t := by
    simpa using (hasDerivAt_id t).smul_const nonzeroTest.val
  exact hasDerivAt_weakH1_coordinate unitSquare i hgraph

/-- (5.7) 真实非零路径调用：σ=1、ρ=0、g=0、φ=exp(−t)。
结论有实际时间积分；σ/ρ 不对称，避免把方向差误作永远为零。 -/
theorem exponential_memory (T t : ℝ) (ht : t ∈ Icc 0 T) :
    Real.exp (-t) = Real.exp (-t) * Real.exp 0 +
      (0 - 1 : ℝ) * ∫ s in 0..t, Real.exp (-(t - s)) * (0 : ℝ) := by
  have hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt (fun t : ℝ => Real.exp (-t))
        (-(1 : ℝ) * Real.exp (-s) + (0 - 1) * 0) s := by
    intro s hs
    simpa using ((hasDerivAt_id s).neg.exp)
  simpa only [neg_mul, one_mul, neg_zero] using LeanPML.PML.auxiliary_memory_formula 1 0 T
    (fun s => Real.exp (-s)) (fun _ => 0)
    (Real.continuous_exp.comp continuous_neg).continuousOn continuousOn_const hODE ht

end LeanPML.Examples.WeakAnalysis
