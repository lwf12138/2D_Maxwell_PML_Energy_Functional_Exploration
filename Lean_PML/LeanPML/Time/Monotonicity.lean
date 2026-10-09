import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# 从导数符号到有限闭区间上的单调不增

这一文件只整理可复用的时间分析接口，不假设具体的微分方程或能量公式。
证明调用 mathlib 已有的中值定理推论，不重新建立微积分基础。

* `Set.Icc a b` 是闭区间 `[a,b]`，成员条件是 `a ≤ t ∧ t ≤ b`。
* `Set.Ioo a b` 是开区间 `(a,b)`，成员条件是 `a < t ∧ t < b`。
* `ContinuousOn f (Set.Icc a b)` 表示 `f` 在闭区间内连续，包含端点的区间内连续性。
* `HasDerivAt f (f' t) t` 同时给出真实导数存在的证据和导数值 `f' t`。
  此处 `f' : ℝ → ℝ` 是候选导数函数，只有配合这个证据，才能把它当作导数使用。
* `AntitoneOn f (Set.Icc a b)` 表示：任取区间内的 `x ≤ y`，都有 `f y ≤ f x`。
  也就是较晚时刻的函数值不大于较早时刻，并不要求严格下降。
-/

namespace LeanPML.Time

/--
闭区间上连续、内部实际可导且导数非正，推出整个闭区间上的单调不增。

`hcont` 用于中值定理的闭区间连续性条件；`hderiv` 给出内部导数存在及其值；
`hnonpos` 单独控制这个值的符号。三个条件承担不同作用。

端点比较由 mathlib 的中值定理推论处理：比较两个区间内时刻时，只需两者之间
的开区间内可导，加上包含这两个时刻的闭区间上的连续性。因此无需假设 `a`、`b`
处存在普通双侧导数，也无需在 `[a,b]` 外增加微分方程。

这里不要求 `a < b`：单点区间及空区间同样满足结论。
-/
theorem antitoneOn_Icc_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt f (f' t) t)
    (hnonpos : ∀ t ∈ Set.Ioo a b, f' t ≤ 0) :
    AntitoneOn f (Set.Icc a b) := by
  -- `apply` 把目标交给 mathlib 的一般凸集定理，并留下两个内部条件需要证明。
  -- 实区间是凸集，`convex_Icc a b` 给出这一事实；连续性直接使用 `hcont`。
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc a b) hcont
  · -- `intro` 取一个位于闭区间内部的任意时刻。
    intro t ht
    -- `simpa only` 只使用“闭区间的内部就是开区间”这个集合恒等式。
    have ht' : t ∈ Set.Ioo a b := by
      simpa only [interior_Icc] using ht
    -- 普通导数证据可以限制为内部集合上的导数证据；这里没有增加假设。
    exact (hderiv t ht').hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioo a b := by
      simpa only [interior_Icc] using ht
    -- `exact` 提供与当前目标完全吻合的非正性证明。
    exact hnonpos t ht'

/--
退化闭区间 `[a,a]` 只有一个点，任何函数在这个集合上都单调不增。
这个声明不需要连续性、可导性或任何微分方程；取 `a = 0` 就覆盖 `T = 0`。
-/
theorem antitoneOn_Icc_self (f : ℝ → ℝ) (a : ℝ) :
    AntitoneOn f (Set.Icc a a) := by
  -- 展开单调不增的目标，任取区间内的两个点；它们的先后关系不会再被使用。
  intro x hx y hy _hxy
  -- `hx` 给出 `a ≤ x` 和 `x ≤ a`；序的反对称性推出 `x = a`，同理 `y = a`。
  have hx' : x = a := le_antisymm hx.2 hx.1
  have hy' : y = a := le_antisymm hy.2 hy.1
  -- 两点都替换成 `a` 后，只剩下反身不等式 `f a ≤ f a`。
  simpa only [hx', hy'] using (le_refl (f a))

end LeanPML.Time
