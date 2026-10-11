import LeanPML.PML.Weights
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
namespace LeanPML.PML
noncomputable def spatialDecayPath (t : ℝ) : ℝ := Real.exp (-t)

/-- 指数路径的真实导数。由 mathlib 的恒等函数、取负和 exp 求导规则构造；
ring 只把链式法则产生的 exp(-t)·(-1) 整理为 -exp(-t)。 -/
theorem hasDerivAt_spatialDecayPath (t : ℝ) :
    HasDerivAt spatialDecayPath (-spatialDecayPath t) t := by
  have h_exponent : HasDerivAt (fun s : ℝ => -s) (-1) t :=
    (hasDerivAt_id t).neg
  have h_exp := h_exponent.exp
  exact h_exp.congr_deriv (by dsimp [spatialDecayPath]; ring)

def spatialLinearPath (t : ℝ) : ℝ := t + 1

/-- 上述零区路径的真实导数为 1。mathlib 的 add_const 表达常数项导数为零，
保留原来的恒等函数导数；后面用它验证两个方向的辅助演化。 -/
theorem hasDerivAt_spatialLinearPath (t : ℝ) :
    HasDerivAt spatialLinearPath 1 t := by
  exact (hasDerivAt_id t).add_const 1


end LeanPML.PML
