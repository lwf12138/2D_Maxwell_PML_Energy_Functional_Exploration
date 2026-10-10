import LeanPML.Time.Monotonicity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Debye 时间子系统：从真实导数到耗散与有限区间单调性

E、P : ℝ → ℝ 分别是电场和极化的时间函数；ε、κ、τ : ℝ 是时间不变材料常数。
本文件研究 ε E' = -P'、τ P' + P = κ E，没有空间、磁场或 PML 辅助变量。
namespace LeanPML.Debye 使本能量与 Tutorial.energy 分开命名。

dE、dP 是某时刻的导数值，必须有 HasDerivAt E dE t、HasDerivAt P dP t 证据。
仅将一个实数叫作 dP，并不表示已经证明它是 P 的导数。
主定理只输入参数、原函数连续性和内部两条方程；不输入能量律或单调性。

ContinuousOn f (Set.Icc 0 T) 是闭区间 [0,T] 内连续；
Set.Ioo 0 T 是开区间 (0,T)，只有这里需要方程及普通导数。
AntitoneOn 表示较晚时刻的能量不大于较早时刻，允许相等。
-/

namespace LeanPML.Debye

/-- Debye 能量：ε E² 与 P²/κ 两项之和的一半。 -/
noncomputable def energy (ε κ : ℝ) (E P : ℝ → ℝ) (t : ℝ) : ℝ :=
  (ε * (E t) ^ 2 + (P t) ^ 2 / κ) / 2

/-- 耗散只是一个具体函数表达式，定义不附带非负假设。 -/
noncomputable def dissipation (κ τ : ℝ) (E P : ℝ → ℝ) (t : ℝ) : ℝ :=
  (κ * E t - P t) ^ 2 / (κ * τ)

/-- 能量非负只用 ε、κ 正及平方非负，不需要方程或 τ。 -/
theorem energy_nonneg (ε κ : ℝ) (E P : ℝ → ℝ) (t : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) : 0 ≤ energy ε κ E P t := by
  unfold energy
  exact div_nonneg
    (add_nonneg (mul_nonneg hε.le (sq_nonneg (E t)))
      (div_nonneg (sq_nonneg (P t)) hκ.le)) (by norm_num)

/-- 在任意集合 s 上，将 E、P 的连续性传给能量；不需要方程或参数符号。 -/
theorem continuousOn_energy (ε κ : ℝ) {E P : ℝ → ℝ} {s : Set ℝ}
    (hE : ContinuousOn E s) (hP : ContinuousOn P s) :
    ContinuousOn (energy ε κ E P) s := by
  -- change 只展开定义；pow、const_mul、div_const、add 在这里是连续性规则。
  change ContinuousOn (fun t => (ε * (E t) ^ 2 + (P t) ^ 2 / κ) / 2) s
  exact (((hE.pow 2).const_mul ε).add ((hP.pow 2).div_const κ)).div_const 2

/-- 纯求导阶段：尚未代入 Debye 方程，也不需要参数为正。 -/
theorem hasDerivAt_energy_of_hasDerivAt (ε κ : ℝ) (E P : ℝ → ℝ)
    (t dE dP : ℝ) (hE : HasDerivAt E dE t) (hP : HasDerivAt P dP t) :
    HasDerivAt (energy ε κ E P) (ε * E t * dE + (P t / κ) * dP) t := by
  -- 平方求导 → 乘/除常数 → 两项相加 → 除以 2。
  have h := (((hE.pow 2).const_mul ε).add ((hP.pow 2).div_const κ)).div_const 2
  -- congr_deriv 用代数等式替换导数值；ring 只整理多项式，不建立导数证据。
  exact h.congr_deriv (by ring)

/-- 代入原方程，得到路线图 §3.1 的真实导数公式 -(τ/κ) dP²。 -/
theorem hasDerivAt_energy_rate (ε κ τ : ℝ) (E P : ℝ → ℝ)
    (t dE dP : ℝ) (hκ : κ ≠ 0)
    (hE : HasDerivAt E dE t) (hP : HasDerivAt P dP t)
    (hMaxwell : ε * dE = -dP) (hDebye : τ * dP + P t = κ * E t) :
    HasDerivAt (energy ε κ E P) (-(τ / κ) * dP ^ 2) t := by
  -- κ ≠ 0 允许除以 κ；本条恒等式无需 ε、τ 正，也没有除以 ε。
  have hEvalue : E t = (τ * dP + P t) / κ := by
    apply (eq_div_iff hκ).2
    calc
      E t * κ = κ * E t := mul_comm _ _
      _ = τ * dP + P t := hDebye.symm
  apply (hasDerivAt_energy_of_hasDerivAt ε κ E P t dE dP hE hP).congr_deriv
  calc
    ε * E t * dE + (P t / κ) * dP
        = E t * (ε * dE) + (P t / κ) * dP := by ring
    _ = -E t * dP + (P t / κ) * dP := by rw [hMaxwell]; ring
    -- -E dP + (P/κ)dP 中的极化项结合，再用第二方程得负平方。
    _ = -(τ / κ) * dP ^ 2 := by rw [hEvalue]; ring

/-- 两种耗散表达式的代数连接；由 τ dP + P = κ E 消去 dP。 -/
theorem dissipation_eq_rate (κ τ : ℝ) (E P : ℝ → ℝ) (t dP : ℝ)
    (hκ : κ ≠ 0) (hτ : τ ≠ 0) (hDebye : τ * dP + P t = κ * E t) :
    dissipation κ τ E P t = (τ / κ) * dP ^ 2 := by
  -- 这只是代数引理；实际导数含义由调用者的 HasDerivAt 提供。
  have hresidual : κ * E t - P t = τ * dP := by
    rw [← hDebye]
    ring
  unfold dissipation
  rw [hresidual]
  -- field_simp 必须取得 κ、τ 的非零证据，才能合法消去分母。
  field_simp [hκ, hτ]

/-- 消去 dP 后的真实能量导数为 -dissipation，即 -(κ E-P)²/(κ τ)。 -/
theorem hasDerivAt_energy_dissipation (ε κ τ : ℝ) (E P : ℝ → ℝ)
    (t dE dP : ℝ) (hκ : κ ≠ 0) (hτ : τ ≠ 0)
    (hE : HasDerivAt E dE t) (hP : HasDerivAt P dP t)
    (hMaxwell : ε * dE = -dP) (hDebye : τ * dP + P t = κ * E t) :
    HasDerivAt (energy ε κ E P) (-dissipation κ τ E P t) t := by
  have h := hasDerivAt_energy_rate ε κ τ E P t dE dP hκ hE hP hMaxwell hDebye
  apply h.congr_deriv
  rw [dissipation_eq_rate κ τ E P t dP hκ hτ hDebye]
  ring

/-- κ、τ 正保证分母正，故耗散非负；这一步无需微分方程。 -/
theorem dissipation_nonneg (κ τ : ℝ) (E P : ℝ → ℝ) (t : ℝ)
    (hκ : 0 < κ) (hτ : 0 < τ) : 0 ≤ dissipation κ τ E P t := by
  unfold dissipation
  exact div_nonneg (sq_nonneg (κ * E t - P t)) (mul_pos hκ hτ).le

/-- 真实导数非正：先证明导数存在与公式，再使用耗散的符号。 -/
theorem energy_deriv_nonpos (ε κ τ : ℝ) (E P : ℝ → ℝ)
    (t dE dP : ℝ) (hκ : 0 < κ) (hτ : 0 < τ)
    (hE : HasDerivAt E dE t) (hP : HasDerivAt P dP t)
    (hMaxwell : ε * dE = -dP) (hDebye : τ * dP + P t = κ * E t) :
    deriv (energy ε κ E P) t ≤ 0 := by
  -- ne' 从正性取得非零证据；.deriv 从 HasDerivAt 取得实际导数等式。
  rw [(hasDerivAt_energy_dissipation ε κ τ E P t dE dP
    hκ.ne' hτ.ne' hE hP hMaxwell hDebye).deriv]
  exact neg_nonpos.mpr (dissipation_nonneg κ τ E P t hκ hτ)

/-- 内部逐点拆开原方程的存在量词，导出能量真实导数。 -/
theorem hasDerivAt_energy_on_Ioo (ε κ τ T : ℝ) (E P : ℝ → ℝ)
    (hκ : κ ≠ 0) (hτ : τ ≠ 0)
    (hODE : ∀ t ∈ Set.Ioo 0 T, ∃ dE dP : ℝ,
      HasDerivAt E dE t ∧ HasDerivAt P dP t ∧
      ε * dE = -dP ∧ τ * dP + P t = κ * E t) :
    ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (energy ε κ E P) (-dissipation κ τ E P t) t := by
  intro t ht
  -- rcases 同时取出导数值、真实求导证据和两条原方程。
  rcases hODE t ht with ⟨dE, dP, hE, hP, hMaxwell, hDebye⟩
  exact hasDerivAt_energy_dissipation ε κ τ E P t dE dP
    hκ hτ hE hP hMaxwell hDebye

/-- T=0 的单独声明不要求参数正、连续性或任何内部导数。 -/
theorem antitoneOn_energy_zero (ε κ : ℝ) (E P : ℝ → ℝ) :
    AntitoneOn (energy ε κ E P) (Set.Icc 0 0) :=
  LeanPML.Time.antitoneOn_Icc_self (energy ε κ E P) 0

/-- 主定理：材料参数、原函数连续性及内部原方程推出闭区间能量单调不增。 -/
theorem antitoneOn_energy (ε κ τ T : ℝ) (E P : ℝ → ℝ)
    (_hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hT : 0 ≤ T)
    (hEcont : ContinuousOn E (Set.Icc 0 T))
    (hPcont : ContinuousOn P (Set.Icc 0 T))
    (hODE : ∀ t ∈ Set.Ioo 0 T, ∃ dE dP : ℝ,
      HasDerivAt E dE t ∧ HasDerivAt P dP t ∧
      ε * dE = -dP ∧ τ * dP + P t = κ * E t) :
    AntitoneOn (energy ε κ E P) (Set.Icc 0 T) := by
  -- _hε 保留物理参数范围；单调性不使用其符号，能量非负与初值界会使用。
  rcases eq_or_lt_of_le hT with hzero | _hpos
  · rw [← hzero]
    exact antitoneOn_energy_zero ε κ E P
  · -- 重用 v0.1.1 的中值定理接口，不增加端点双侧导数或区间外方程。
    apply LeanPML.Time.antitoneOn_Icc_of_hasDerivAt_nonpos
      (continuousOn_energy ε κ hEcont hPcont)
      (hasDerivAt_energy_on_Ioo ε κ τ T E P hκ.ne' hτ.ne' hODE)
    intro t _ht
    -- apply 剩下的是导数值的符号；由定义和材料正性证明它。
    exact neg_nonpos.mpr (dissipation_nonneg κ τ E P t hκ hτ)

/-- 初值界：同一组原始假设下，闭区间内能量介于 0 和初始值之间。 -/
theorem energy_bounds (ε κ τ T : ℝ) (E P : ℝ → ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hT : 0 ≤ T)
    (hEcont : ContinuousOn E (Set.Icc 0 T))
    (hPcont : ContinuousOn P (Set.Icc 0 T))
    (hODE : ∀ t ∈ Set.Ioo 0 T, ∃ dE dP : ℝ,
      HasDerivAt E dE t ∧ HasDerivAt P dP t ∧
      ε * dE = -dP ∧ τ * dP + P t = κ * E t)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    0 ≤ energy ε κ E P t ∧ energy ε κ E P t ≤ energy ε κ E P 0 := by
  constructor
  · exact energy_nonneg ε κ E P t hε hκ
  · have hmono := antitoneOn_energy ε κ τ T E P hε hκ hτ hT hEcont hPcont hODE
    -- 早时刻 0 在区间内、晚时刻 t 在区间内、0 ≤ t，依次传给 AntitoneOn。
    exact hmono ⟨le_rfl, hT⟩ ht ht.1

/-! ## 非零显式实例：ε=κ=τ=1，E=exp(-2t)，P=-exp(-2t) -/

/-- 显式电场时间函数。 -/
noncomputable def exampleE (t : ℝ) : ℝ := Real.exp (-2 * t)

/-- 显式极化时间函数。 -/
noncomputable def exampleP (t : ℝ) : ℝ := -exampleE t

/-- 用链式法则证明 E 的真实导数，不以普通代数变量代替导数。 -/
theorem hasDerivAt_exampleE (t : ℝ) :
    HasDerivAt exampleE (-2 * exampleE t) t := by
  have h : HasDerivAt (fun s : ℝ => -2 * s) (-2) t := by
    -- id 的导数为 1，乘常数 -2 后导数为 -2。
    simpa using (hasDerivAt_id t).const_mul (-2 : ℝ)
  -- 显式展开函数目标；.exp 使用链式法则，得到 exp(-2t) * (-2)。
  change HasDerivAt (fun s => Real.exp (-2 * s)) (-2 * Real.exp (-2 * t)) t
  exact h.exp.congr_deriv (by ring)

/-- P=-E，所以 P 的导数是 E 导数的相反数。 -/
theorem hasDerivAt_exampleP (t : ℝ) :
    HasDerivAt exampleP (2 * exampleE t) t := by
  change HasDerivAt (fun s => -exampleE s) (2 * exampleE t) t
  exact (hasDerivAt_exampleE t).neg.congr_deriv (by ring)

/-- 全轴可导推出 E 连续；此强性质只用于显式实例。 -/
theorem continuous_exampleE : Continuous exampleE :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exampleE t).continuousAt)

/-- 同理得到 P 连续，随后可限制到任意闭区间。 -/
theorem continuous_exampleP : Continuous exampleP :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exampleP t).continuousAt)

/-- 实例满足两条原方程，存在量词携带真实导数证据。 -/
theorem example_ode (t : ℝ) :
    ∃ dE dP : ℝ,
      HasDerivAt exampleE dE t ∧ HasDerivAt exampleP dP t ∧
      (1 : ℝ) * dE = -dP ∧
      (1 : ℝ) * dP + exampleP t = (1 : ℝ) * exampleE t := by
  refine ⟨-2 * exampleE t, 2 * exampleE t,
    hasDerivAt_exampleE t, hasDerivAt_exampleP t, ?_, ?_⟩
  · ring
  · dsimp only [exampleP]
    ring

/-- 非零初值与初始能量：exp(0)=1，得到 E(0)=1、P(0)=-1、能量=1。 -/
theorem example_initial :
    exampleE 0 = 1 ∧ exampleP 0 = -1 ∧ energy 1 1 exampleE exampleP 0 = 1 := by
  norm_num [exampleE, exampleP, energy]

/-- 实例通过一般主定理得到任意有限闭区间的单调不增。 -/
theorem example_energy_antitone (T : ℝ) (hT : 0 ≤ T) :
    AntitoneOn (energy 1 1 exampleE exampleP) (Set.Icc 0 T) := by
  apply antitoneOn_energy 1 1 1 T exampleE exampleP
    (by norm_num) (by norm_num) (by norm_num) hT
    continuous_exampleE.continuousOn continuous_exampleP.continuousOn
  -- 全轴实例方程限制到开区间；一般主定理的假设范围并未扩张。
  intro t _ht
  exact example_ode t

/-- 实例通过一般初值界定理得到 0 ≤ 能量 ≤ 1，而非仅作数值验证。 -/
theorem example_energy_bounds (T : ℝ) (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    0 ≤ energy 1 1 exampleE exampleP t ∧ energy 1 1 exampleE exampleP t ≤ 1 := by
  have h := energy_bounds 1 1 1 T exampleE exampleP
    (by norm_num) (by norm_num) (by norm_num) hT
    continuous_exampleE.continuousOn continuous_exampleP.continuousOn
    (fun s _hs => example_ode s) ht
  -- 使用已证明的初值等式，将一般上界 energy ... 0 改写成 1。
  simpa only [example_initial.2.2] using h

end LeanPML.Debye
