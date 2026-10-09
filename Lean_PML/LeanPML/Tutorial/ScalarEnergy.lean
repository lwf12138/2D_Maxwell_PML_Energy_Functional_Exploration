import LeanPML.Tutorial.LocalEnergy
import LeanPML.Time.Monotonicity
-- exp 对照例所需的真实导数规则。
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
-- norm_num 只验证 exp 0 = 1 化简后的数值等式与不等式。
import Mathlib.Tactic.NormNum

/-!
# 标量平方能量在有限时间区间上单调不增

沿用 LocalEnergy 的 energy，不重新定义能量。
ContinuousOn u (Set.Icc 0 T) 表示 u 在闭区间 [0,T] 上连续。
Set.Ioo 0 T 是开区间 (0,T)，下面的微分方程只在这个集合内要求成立。
HasDerivAt u d t 同时给出 t 处导数存在以及导数值 d，绝非普通数值占位符。

证明分四层：函数可导 → 导数公式 → 导数非正 → 时间单调不增。
AntitoneOn (energy u) (Set.Icc 0 T) 的含义是：
若 0 ≤ s ≤ t ≤ T，则 energy u t ≤ energy u s。
它允许相等；没有断言严格递减，也没有证明解的存在或唯一性。
-/

namespace LeanPML.Tutorial

/-- 平方能量非负：对任意函数、任意时刻成立，无需方程或耗散参数。 -/
theorem energy_nonneg (u : ℝ → ℝ) (t : ℝ) : 0 ≤ energy u t := by
  -- unfold 展开已有定义；平方非负，除数 2 为正（因此也非负）。
  unfold energy
  exact div_nonneg (sq_nonneg (u t)) (by norm_num)

/-- 原函数在集合 s 上连续，就能把连续性传递给平方能量。 -/
theorem continuousOn_energy {u : ℝ → ℝ} {s : Set ℝ}
    (hcont : ContinuousOn u s) : ContinuousOn (energy u) s := by
  -- .pow 与 .div_const 在这里是连续性规则，不是导数规则。
  -- change 把目标中的 energy 显式展开成同一定义的函数表达式。
  change ContinuousOn (fun t => (u t) ^ 2 / 2) s
  exact (hcont.pow 2).div_const 2

/-- 在开区间内逐点应用上一阶段的求导引理；不要求 σ 非负。 -/
theorem hasDerivAt_energy_on_Ioo (u : ℝ → ℝ) (σ T : ℝ)
    (hode : ∀ t ∈ Set.Ioo 0 T, HasDerivAt u (-σ * u t) t) :
    ∀ t ∈ Set.Ioo 0 T, HasDerivAt (energy u) (-σ * (u t) ^ 2) t := by
  -- intro 引入任意内部时刻 t 及其区间证据 ht。
  intro t ht
  exact hasDerivAt_energy u σ t (hode t ht)

/-- 真实导数的符号估计：此处才需要 σ ≥ 0。 -/
theorem energy_deriv_nonpos (u : ℝ → ℝ) (σ t : ℝ)
    (hσ : 0 ≤ σ) (hu : HasDerivAt u (-σ * u t) t) :
    deriv (energy u) t ≤ 0 := by
  -- .deriv 从 HasDerivAt 证据取得 mathlib 的 deriv 值等式。
  -- rw 用已证公式替换目标中的导数，随后只剩实数符号估计。
  rw [(hasDerivAt_energy u σ t hu).deriv]
  -- -σ ≤ 0，平方 ≥ 0，所以乘积 ≤ 0。
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ) (sq_nonneg (u t))

/-- T = 0 的独立结论：任意能量函数在 [0,0] 上都单调不增。 -/
theorem antitoneOn_energy_zero (u : ℝ → ℝ) :
    AntitoneOn (energy u) (Set.Icc 0 0) := by
  -- 无需连续性、方程、σ，甚至无需用到能量定义。
  exact LeanPML.Time.antitoneOn_Icc_self (energy u) 0

/-- 主定理：输入只有参数条件、原函数的闭区间连续性和内部微分方程。 -/
theorem antitoneOn_energy (u : ℝ → ℝ) (σ T : ℝ)
    (hσ : 0 ≤ σ) (hT : 0 ≤ T)
    (hcont : ContinuousOn u (Set.Icc 0 T))
    (hode : ∀ t ∈ Set.Ioo 0 T, HasDerivAt u (-σ * u t) t) :
    AntitoneOn (energy u) (Set.Icc 0 T) := by
  -- rcases 把 T ≥ 0 分为 T = 0 和 T > 0。前一支不调用 hode。
  -- 一般时间引理本身不要求区间长度为正，所以后一支无需再使用 _hpos。
  rcases eq_or_lt_of_le hT with hzero | _hpos
  · -- hzero : 0 = T；← 表示从右向左替换，把 T 换成 0。
    rw [← hzero]
    exact antitoneOn_energy_zero u
  · -- 把已证明的能量连续性及内部导数公式交给通用时间引理。
    -- apply 后仅剩“各内部时刻的导数值 ≤ 0”这一目标。
    apply LeanPML.Time.antitoneOn_Icc_of_hasDerivAt_nonpos
      (continuousOn_energy hcont) (hasDerivAt_energy_on_Ioo u σ T hode)
    intro t ht
    -- 这里从原方程证明符号条件，未把它加进主定理的输入。
    have hsign := energy_deriv_nonpos u σ t hσ (hode t ht)
    -- 将真实导数的非正结论改写为导数公式右端的非正结论。
    rw [(hasDerivAt_energy u σ t (hode t ht)).deriv] at hsign
    exact hsign

/-- 初值界：闭区间任意时刻的能量介于 0 和初始能量之间。 -/
theorem energy_bounds (u : ℝ → ℝ) (σ T : ℝ)
    (hσ : 0 ≤ σ) (hT : 0 ≤ T)
    (hcont : ContinuousOn u (Set.Icc 0 T))
    (hode : ∀ t ∈ Set.Ioo 0 T, HasDerivAt u (-σ * u t) t)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    0 ≤ energy u t ∧ energy u t ≤ energy u 0 := by
  -- constructor 把“且”拆成下界和上界两个目标。
  constructor
  · exact energy_nonneg u t
  · have hmono := antitoneOn_energy u σ T hσ hT hcont hode
    -- AntitoneOn 依次接受：早时刻 0 在区间内、晚时刻 t 在区间内、0 ≤ t。
    -- hT 用于证明 0 本身属于 [0,T]；ht.1 正是 0 ≤ t。
    exact hmono ⟨le_rfl, hT⟩ ht ht.1

/-- 参数练习：σ = -1 时，exp 仍满足同一形式的微分方程。 -/
theorem exp_solves_negative_damping (t : ℝ) :
    HasDerivAt Real.exp (-(-1 : ℝ) * Real.exp t) t := by
  -- mathlib 给出 exp'(t) = exp(t)；simp 整理 -(-1) * exp(t)。
  simpa using Real.hasDerivAt_exp t

/-- 对照例：方程与连续性仍成立，但 t = 0 的能量导数等于 1，严格大于 0。 -/
theorem negative_damping_counterexample :
    Continuous Real.exp ∧
      (∀ t : ℝ, HasDerivAt Real.exp (-(-1 : ℝ) * Real.exp t) t) ∧
      HasDerivAt (energy Real.exp) 1 0 ∧
      0 < deriv (energy Real.exp) 0 := by
  -- 求导引理完全不需要 σ ≥ 0，因此 σ = -1 仍可合法代入。
  have henergy : HasDerivAt (energy Real.exp) 1 0 := by
    have h := hasDerivAt_energy Real.exp (-1) 0 (exp_solves_negative_damping 0)
    -- norm_num 用 exp(0) = 1，算出 -(-1) * 1² = 1。
    norm_num at h ⊢
    exact h
  -- refine 给出合取的前三项，留下最后一个数值不等式作为待证目标。
  refine ⟨Real.continuous_exp, exp_solves_negative_damping, henergy, ?_⟩
  rw [henergy.deriv]
  norm_num

end LeanPML.Tutorial
