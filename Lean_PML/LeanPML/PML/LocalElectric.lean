import LeanPML.PML.TimeInvariants

/-!
# 电块：代数展开与真实时间求导

来源：`../results/V7_Maxwell_Debye_PML/V7_global_energy.md` 的 (6.2)、(7.3)。
本文件先检查某时刻数值的多项式恒等式，再对实际函数 `v : ℝ → ℝ` 求导。
`ε a b c : ℝ` 都是不依赖时间的参数；`a,b` 可以是空间变系数在固定点的值。
`vDot,vDDot` 在代数引理里只是实数；在求导定理里分别由
`HasDerivAt v vDot t` 和 `HasDerivAt (deriv v) vDDot t` 连接到真实导数。

建议阅读顺序：`electricEnergy` → `electric_rate_identity` →
`hasDerivAt_electricEnergyAlong` → 非零路径实例。
这些等式不需要材料正性或吸收正下界，因此也覆盖 `a=b=0`。
完整能量 (6.2) 的电部分还要把本文件的局部能量乘以 `μ` 并作空间积分。
这里没有空间积分、PEC、正定性或单调性结论；余项也不保证非负。
-/

namespace LeanPML.PML

/-- V7 (7.3) 的局部电块 `F_e`，包含 `ε/2`，不包含 (6.2) 外加的 `μ`。
输入 `v,vDot` 是某时刻的数值；定义本身不赋予 `vDot` 导数含义。
后面的 `electricEnergyAlong` 才用真实函数 `deriv v` 填入第二个槽。 -/
noncomputable def electricEnergy (ε a b c v vDot : ℝ) : ℝ :=
  ε / 2 * (vDot ^ 2 + 2 * c * v * vDot + (b + a * c) * v ^ 2)

/-- V7 (7.3) 的余项 `D_e`。参数任意时 `a-c` 可能为负；
因此这个名字只标记恒等式中的余项，不宣称其非负。
它用于代数恒等式和真实求导定理。 -/
noncomputable def electricRemainder (ε a b c v vDot : ℝ) : ℝ :=
  ε * ((a - c) * vDot ^ 2 + b * c * v ^ 2)

/-- 把 V7 (7.3) 的电块变成实际时间函数：时间 `s` 对应
`electricEnergy ε a b c (v s) (deriv v s)`。
mathlib 的 `deriv` 是实际函数的导数算子；在可导性未证时，单用该符号还不够，
所以后面的定理另外输入一阶、二阶的 `HasDerivAt` 证据。 -/
noncomputable def electricEnergyAlong (ε a b c : ℝ) (v : ℝ → ℝ) (s : ℝ) : ℝ :=
  electricEnergy ε a b c (v s) (deriv v s)

/-- V7 (7.3) 的代数辅助引理：二次型按形式求导得到的数值，
等于乘积 `ε(vDDot+a*vDot+b*v)(vDot+c*v)` 减去余项。
这里所有输入都只是实数，没有证明任何函数可导。
输出等式由下方真实求导定理调用，把微积分规则产生的导数值整理为论文形式。 -/
theorem electric_rate_identity (ε a b c v vDot vDDot : ℝ) :
    ε / 2 * (2 * vDot * vDDot +
      2 * c * (vDot * vDot + v * vDDot) + (b + a * c) * (2 * v * vDot)) =
    ε * (vDDot + a * vDot + b * v) * (vDot + c * v) -
      electricRemainder ε a b c v vDot := by
  -- 展开余项后，两边都是同一实数多项式；ring 不承担任何求导工作。
  unfold electricRemainder
  ring

/-- V7 (7.3) 的真实时间版本。
`h_v : HasDerivAt v vDot t` 同时表达 v 在 t 可导及其导数值为 vDot；
`h_deriv_v : HasDerivAt (deriv v) vDDot t` 表达对真实导数函数再次求导。
因此这里没有用“任意速度函数在单点等于 v'”来冒充二阶导数。
输出 `HasDerivAt` 同时给出电块可导性和论文规定的导数值。
参数均随时间不变，无需符号假设；未来空间能量恒等式将调用此局部结论。 -/
theorem hasDerivAt_electricEnergyAlong (ε a b c : ℝ) (v : ℝ → ℝ)
    (t vDot vDDot : ℝ)
    (h_v : HasDerivAt v vDot t)
    (h_deriv_v : HasDerivAt (deriv v) vDDot t) :
    HasDerivAt (electricEnergyAlong ε a b c v)
      (ε * (vDDot + a * vDot + b * v t) * (vDot + c * v t) -
        electricRemainder ε a b c (v t) vDot) t := by
  -- 第一步：从真实导数证据读取 deriv v t 的数值。
  have h_velocity_value : deriv v t = vDot := h_v.deriv

  -- 第二步：平方求导。pow 来自 mathlib；congr_deriv 只整理其导数值。
  have h_velocity_square : HasDerivAt (fun s => (deriv v s) ^ 2)
      (2 * vDot * vDDot) t := by
    apply (h_deriv_v.pow 2).congr_deriv
    rw [h_velocity_value]
    ring
  have h_position_square : HasDerivAt (fun s => (v s) ^ 2)
      (2 * v t * vDot) t := by
    exact (h_v.pow 2).congr_deriv (by ring)

  -- 第三步：交叉项使用乘积法则，系数 2c 只做常数乘法。
  have h_cross_product : HasDerivAt (fun s => 2 * c * v s * deriv v s)
      (2 * c * (vDot * vDot + v t * vDDot)) t := by
    have h_product_rule := (h_v.const_mul (2 * c)).mul h_deriv_v
    apply h_product_rule.congr_deriv
    -- 这里已完成真实乘积求导；ring 仅整理得到的导数值。
    rw [h_velocity_value]
    ring

  -- 第四步：先乘常数 (b+ac)，再按定义相加，最后乘 ε/2。
  have h_weighted_position : HasDerivAt (fun s => (b + a * c) * (v s) ^ 2)
      ((b + a * c) * (2 * v t * vDot)) t :=
    h_position_square.const_mul (b + a * c)
  have h_quadratic : HasDerivAt
      (fun s => (deriv v s) ^ 2 + 2 * c * v s * deriv v s +
        (b + a * c) * (v s) ^ 2)
      (2 * vDot * vDDot + 2 * c * (vDot * vDot + v t * vDDot) +
        (b + a * c) * (2 * v t * vDot)) t :=
    (h_velocity_square.add h_cross_product).add h_weighted_position
  have h_energy_rule := h_quadratic.const_mul (ε / 2)

  -- 第五步：调用上面的代数辅助引理，替换导数值，得到 (7.3)。
  -- congr_deriv 不替换函数，也不新增求导假设。
  exact h_energy_rule.congr_deriv
    (electric_rate_identity ε a b c (v t) vDot vDDot)

/-- 非零光滑路径的导数函数相等：复用 v0.1.3 的
`exampleU(t)=(1-exp(-2t))/2` 和其每个时刻的真实导数证据。
`funext` 把函数等式化成任意时刻的等式；不是只检查一个时刻。
此结果使下一个引理可以对整个 `deriv exampleU` 求导。 -/
theorem deriv_exampleU : deriv exampleU = Debye.exampleE := by
  funext t
  exact (hasDerivAt_exampleU t).deriv

/-- 对非零路径的真实导数函数再次求导。
先利用上一条全函数等式，再复用 v0.1.2 的指数函数求导证据；
因此 `-2*exp(-2t)` 确实是 exampleU 的二阶导数值。 -/
theorem hasDerivAt_deriv_exampleU (t : ℝ) :
    HasDerivAt (deriv exampleU) (-2 * Debye.exampleE t) t := by
  rw [deriv_exampleU]
  exact Debye.hasDerivAt_exampleE t

/-- 正式时间路径实例：把前两条真实导数证据传给一般电块求导定理。
参数仍可任意，因此零吸收、单向吸收和双向吸收均可代入。
这验证的是固定空间点的局部时间路径，不宣称它满足完整二维 PDE。 -/
theorem hasDerivAt_electricEnergyAlong_exampleU (ε a b c t : ℝ) :
    HasDerivAt (electricEnergyAlong ε a b c exampleU)
      (ε * (-2 * Debye.exampleE t + a * Debye.exampleE t + b * exampleU t) *
          (Debye.exampleE t + c * exampleU t) -
        electricRemainder ε a b c (exampleU t) (Debye.exampleE t)) t := by
  exact hasDerivAt_electricEnergyAlong ε a b c exampleU t
    (Debye.exampleE t) (-2 * Debye.exampleE t)
    (hasDerivAt_exampleU t) (hasDerivAt_deriv_exampleU t)

/-- 该路径确实不是零函数：在 t=0，它的真实一阶导数为 1。
此非零性配合上面的实际求导调用，避免把仅有零函数的检查当作正式实例。 -/
theorem deriv_exampleU_zero : deriv exampleU 0 = 1 := by
  rw [deriv_exampleU]
  norm_num [Debye.exampleE]

end LeanPML.PML
