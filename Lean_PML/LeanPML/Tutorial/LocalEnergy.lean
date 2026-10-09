-- 幂函数求导：提供下面使用的 HasDerivAt.pow。
import Mathlib.Analysis.Calculus.Deriv.Pow
-- 除以常数的求导：提供 HasDerivAt.div_const。
import Mathlib.Analysis.Calculus.Deriv.Mul
-- 整理求导所得的实数多项式表达式。
import Mathlib.Tactic.Ring

/-!
# 一个时刻的标量能量导数

这是 v0.0.3 的最小真实导数例子，用于检查项目导入、构建及公理依赖。
它只证明：如果 u 在 t 的导数为 -σ * u(t)，那么 u(t)² / 2 的导数为
-σ * u(t)²。这里没有证明能量非负、导数非正或区间单调性，也不涉及 PML。

自然语言到 Lean 的对应：
* `(u : ℝ → ℝ)`：u 是从实数到实数的函数。
* `(σ t : ℝ)`：σ 和 t 是实数；本条求导恒等式不要求 σ 非负。
* `HasDerivAt u (-σ * u t) t`：u 在 t 可导，并且导数值为 -σ * u(t)。
  这比只给某个名为 ut 的实数更强，因为它记录了真实的函数导数关系。
* `energy u`：固定 u 后得到的时间函数，输入时刻 s，输出能量。

这里只假设 t 处的方程，没有假设所有时刻都满足方程，也无需求显式解。
使用的是 mathlib 的普通点导数；有限区间的端点及单调性留给后续阶段。
-/

namespace LeanPML.Tutorial

/-- 定义能量：把时间 s 映到 u(s) 的平方除以 2。 -/
-- `u s` 表示 u(s)；空格表示函数应用，`*` 才表示乘法。
-- `:=` 给出定义的内容。noncomputable 允许使用不可直接执行的实数运算，
-- 并不免除后面定理的证明检查。
noncomputable def energy (u : ℝ → ℝ) (s : ℝ) : ℝ :=
  (u s) ^ 2 / 2

/-- 从 t 处的真实方程 u'(t) = -σ u(t)，推出该点的能量导数。 -/
-- theorem 的冒号之前列对象和假设，之后给出待证结论；`by` 开始证明。
-- hu 已把微分方程的右端代入导数值，不需要再次把方程作为结论假设。
-- 结论仍用 HasDerivAt，因此同时给出能量的可导性和具体导数值。
theorem hasDerivAt_energy (u : ℝ → ℝ) (σ t : ℝ)
    (hu : HasDerivAt u (-σ * u t) t) :
    HasDerivAt (energy u) (-σ * (u t) ^ 2) t := by
  -- hu.pow 2 使用已证明的幂函数求导规则：
  --   对 s ↦ (u s)² 求导，得到 2 * (u t)^(2 - 1) * (-σ * u t)。
  -- .div_const 2 再把函数和导数值都除以常数 2。
  -- have h := ... 为所得的真实导数证据命名，供下一行使用。
  have h := (hu.pow 2).div_const 2
  -- congr_deriv 不改变函数和求导点，只用等式替换导数值。
  -- ring 检查这里的代数恒等式，把导数值整理为 -σ * (u t)²。
  -- Lean 展开 energy 后，识别出 h 中的函数与目标中的 energy u 相同。
  -- 因而核心分析来自 pow 和 div_const；ring 只负责最后的代数整理。
  exact h.congr_deriv (by ring)

end LeanPML.Tutorial
