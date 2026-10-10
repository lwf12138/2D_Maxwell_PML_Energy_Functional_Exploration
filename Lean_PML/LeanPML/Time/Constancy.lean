import LeanPML.Time.Monotonicity

/-!
# 从真实零导数到闭区间内保持初值

`F : ℝ → ℝ` 是实际时间函数。`HasDerivAt F 0 t` 既断言导数存在，也断言其值为零；
只给出一个普通实数等于零，并不能替代这个证据。在某一个时刻导数为零，也不能
单独推出一段时间内恒定：这里要求每个内部时刻都有零导数证据。

* `ContinuousOn F (Set.Icc 0 T)`：`F` 在闭区间 `[0,T]` 上连续，包含端点。
* `∀ t ∈ Set.Ioo 0 T, HasDerivAt F 0 t`：导数条件只在开区间 `(0,T)` 内成立。
* 结论允许 `t = 0` 或 `t = T`，无需这两个端点的普通双侧导数。

本文件复用已有时间单调性引理：零导数使 `F` 和 `-F` 都单调不增，两方向比较
合在一起给出相等。这是一般分析接口；具体模型仍必须从原方程证明零导数。
-/

namespace LeanPML.Time

/--
`T = 0` 时 `[0,0]` 只有初始时刻。任意函数都保持初值，不需要连续性或导数条件。
-/
theorem eq_initial_on_Icc_zero (F : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc 0 0) : F t = F 0 := by
  -- `ht.1 : 0 ≤ t` 与 `ht.2 : t ≤ 0` 用序的反对称性给出 `t = 0`。
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  -- `rw` 用这个等式替换时刻，剩下同一函数值等于自身。
  rw [ht0]

/--
闭区间连续、内部真实导数为零，则区间内每个函数值都等于初值。

`hT` 确保初始时刻 `0` 属于 `[0,T]`；`hcont` 和 `hderiv` 用在一般时间单调性
引理中。端点比较由该引理所依赖的中值定理推论承担，不扩大导数假设的时间范围。
先单独处理 `T = 0`，明确该分支根本不需要使用分析假设。
-/
theorem eq_initial_of_hasDerivAt_zero (F : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn F (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt F 0 t)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : F t = F 0 := by
  -- `by_cases` 分开退化区间和非退化区间；前一个分支仅用集合成员条件。
  by_cases hTzero : T = 0
  · subst T
    exact eq_initial_on_Icc_zero F ht
  · -- 零导数当然非正，先得到 `F` 的单调不增。
    have hanti : AntitoneOn F (Set.Icc 0 T) :=
      antitoneOn_Icc_of_hasDerivAt_nonpos (f' := fun _ => 0)
        hcont hderiv (fun _ _ => le_refl 0)
    -- 对 `-F` 使用同一引理。取负的求导规则把零导数变成 `-0`，
    -- `congr_deriv` 用 `neg_zero` 将导数值替换为 `0`；这里仍是真实求导。
    have hanti_neg : AntitoneOn (fun s => -F s) (Set.Icc 0 T) := by
      apply antitoneOn_Icc_of_hasDerivAt_nonpos (f' := fun _ => 0) hcont.neg
      · intro s hs
        exact (hderiv s hs).neg.congr_deriv (neg_zero : -(0 : ℝ) = 0)
      · intro _ _
        exact le_refl 0
    -- `⟨le_refl 0, hT⟩` 给出初始时刻的区间成员证据。
    -- `ht.1` 是 `0 ≤ t`，因此可以比较初始时刻与时刻 `t`。
    have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_refl 0, hT⟩
    have hle : F t ≤ F 0 := hanti h0 ht ht.1
    have hneg_le : -F t ≤ -F 0 := hanti_neg h0 ht ht.1
    -- 负数不等式反向：第二条比较给出 `F 0 ≤ F t`。
    -- `le_antisymm` 将两个相反方向的不等式组合成函数值相等。
    exact le_antisymm hle (neg_le_neg_iff.mp hneg_le)

end LeanPML.Time
