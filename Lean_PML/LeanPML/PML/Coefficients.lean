import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# V7 的系数条件与精确小量条件

本文件形式化 `../results/V7_Maxwell_Debye_PML/V7_global_energy.md` 第 5.1 节
(5.2)–(5.4) 的实数代数。`p`、`r` 是固定空间点的吸收系数值，可以来自
随空间变化的场；把它们写成实数不表示全域系数为常数。

`a = p+r`、`b = p*r`；`ε,κ,τ,μ` 是材料参数，`CP` 是给定的正数。
`CP` 将来要由 Poincaré 不等式兑现，本阶段没有证明该空间不等式。
建议依次阅读 `absorptionSum_eq_zero_iff`、`le_inv_sqrt_iff`、
`le_threshold_iff_explicit`，再阅读 (5.4) 的直接推论。

本文件的假设均在定理参数中明列，没有把待证的系数性质放进参数结构。
这里不构造加权空间、不对场求导、不证明 PDE 能量恒等式。
-/

namespace LeanPML.PML

/-- V7 第 1 节的 `a=p+r`，在第 5.1 节 (5.4) 使用。
输入为固定空间点的两项吸收值，输出为吸收和；后续权重以它作分母。 -/
def absorptionSum (p r : ℝ) : ℝ := p + r

/-- V7 第 1 节的 `b=pr`，在 (5.4) 使用。
不要求正吸收，允许任一项为零；后续检验 `ac-b` 的符号。 -/
def absorptionProduct (p r : ℝ) : ℝ := p * r

/-- V7 (5.2)：`A=ε+2κ`。材料正性在下面单独证明，不包含在定义中。 -/
def materialA (ε κ : ℝ) : ℝ := ε + 2 * κ

/-- V7 (5.2)：`K=8μAC_P²`。`CP` 只是输入的正参数，尚未连接 Poincaré 定理。 -/
def scaleK (ε κ μ CP : ℝ) : ℝ := 8 * μ * materialA ε κ * CP ^ 2

/-- V7 (5.2) 的精确阈值 `c_*`。
`1 / Real.sqrt K` 是论文正数 `K` 上的 `K^(-1/2)`；嵌套 `min` 表示三项最小值。
它是实数总函数，正式物理解释和正性只在后续正参数假设下使用。 -/
noncomputable def threshold (ε κ τ μ CP : ℝ) : ℝ :=
  min (1 / Real.sqrt (scaleK ε κ μ CP))
    (min (κ * τ / (8 * materialA ε κ * scaleK ε κ μ CP))
      (κ / (8 * materialA ε κ * τ)))

/-- 由 V7 (5.2) 推出 `A>0`：使用 `ε>0,κ>0`；后续用于分母符号。 -/
theorem materialA_pos (ε κ : ℝ) (hε_pos : 0 < ε) (hκ_pos : 0 < κ) :
    0 < materialA ε κ := by
  dsimp [materialA]
  positivity

/-- 由 V7 (5.2) 推出 `K>0`。`μ>0,CP>0` 确保乘积与平方严格为正；
`τ` 未参与 `K`，因此不作假设。此结论用于平方根和分母消去。 -/
theorem scaleK_pos (ε κ μ CP : ℝ)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ)
    (hμ_pos : 0 < μ) (hCP_pos : 0 < CP) :
    0 < scaleK ε κ μ CP := by
  have hA_pos : 0 < materialA ε κ := materialA_pos ε κ hε_pos hκ_pos
  dsimp [scaleK]
  positivity

/-- V7 (5.2) 中 `c_*>0`：三项都严格为正，最小值也严格为正。
五个材料/域参数的正性仅用于各分子、分母及平方根的符号；后续可选取 `c=c_*`。 -/
theorem threshold_pos (ε κ τ μ CP : ℝ)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ) (hτ_pos : 0 < τ)
    (hμ_pos : 0 < μ) (hCP_pos : 0 < CP) :
    0 < threshold ε κ τ μ CP := by
  have hA_pos : 0 < materialA ε κ := materialA_pos ε κ hε_pos hκ_pos
  have hK_pos : 0 < scaleK ε κ μ CP := scaleK_pos ε κ μ CP hε_pos hκ_pos hμ_pos hCP_pos
  have hroot_pos : 0 < Real.sqrt (scaleK ε κ μ CP) := Real.sqrt_pos.mpr hK_pos
  have hfirst_pos : 0 < 1 / Real.sqrt (scaleK ε κ μ CP) := div_pos zero_lt_one hroot_pos
  have hsecond_pos : 0 < κ * τ / (8 * materialA ε κ * scaleK ε κ μ CP) := by
    positivity
  have hthird_pos : 0 < κ / (8 * materialA ε κ * τ) := by positivity
  -- `lt_min_iff` 把最小值的严格正性拆成各项的严格正性。
  exact lt_min hfirst_pos (lt_min hsecond_pos hthird_pos)

/-- 由 V7 (5.2) 的第一项推出的辅助等价：对 `c≥0,K>0`，
`c≤1/√K` 当且仅当 `c²K≤1`。这是平方根条件连接多项式条件的桥梁，
不是另一个论文编号；后续主等价定理在 `c>0` 下调用它。 -/
theorem le_inv_sqrt_iff (c K : ℝ) (hc_nonneg : 0 ≤ c) (hK_pos : 0 < K) :
    c ≤ 1 / Real.sqrt K ↔ c ^ 2 * K ≤ 1 := by
  have hroot_pos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK_pos
  have hproduct_nonneg : 0 ≤ c * Real.sqrt K := mul_nonneg hc_nonneg hroot_pos.le
  have hsquare : (c * Real.sqrt K) ^ 2 = c ^ 2 * K := by
    -- 展开乘积平方，再用正数的平方根平方等于原数。
    rw [mul_pow, Real.sq_sqrt hK_pos.le]
  -- 当前分母 `√K` 已知严格为正，乘过不等号时方向不变。
  rw [le_div_iff₀ hroot_pos]
  constructor
  · intro hproduct_le_one
    have hsquare_le_one : (c * Real.sqrt K) ^ 2 ≤ 1 := by
      -- 在非负半轴上平方保持顺序；`nlinarith` 完成这个二次序关系。
      nlinarith only [hproduct_nonneg, hproduct_le_one]
    simpa only [hsquare] using hsquare_le_one
  · intro hsmall_square
    have hsquare_le_one : (c * Real.sqrt K) ^ 2 ≤ 1 := by
      simpa only [hsquare] using hsmall_square
    nlinarith only [hsquare_le_one]

/-- V7 (5.2)–(5.3) 与显式多项式小量条件的双向等价。
正材料参数保证三个分母为正，`c>0` 允许使用平方根桥梁。
结论的三个不等式是后续能量代数的实际入口，不以它们为额外独立假设。 -/
theorem le_threshold_iff_explicit (ε κ τ μ CP c : ℝ)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ) (hτ_pos : 0 < τ)
    (hμ_pos : 0 < μ) (hCP_pos : 0 < CP) (hc_pos : 0 < c) :
    c ≤ threshold ε κ τ μ CP ↔
      c ^ 2 * scaleK ε κ μ CP ≤ 1 ∧
      8 * c * materialA ε κ * scaleK ε κ μ CP ≤ κ * τ ∧
      8 * c * materialA ε κ * τ ≤ κ := by
  have hA_pos : 0 < materialA ε κ := materialA_pos ε κ hε_pos hκ_pos
  have hK_pos : 0 < scaleK ε κ μ CP := scaleK_pos ε κ μ CP hε_pos hκ_pos hμ_pos hCP_pos
  have hdenom_two_pos : 0 < 8 * materialA ε κ * scaleK ε κ μ CP := by positivity
  have hdenom_three_pos : 0 < 8 * materialA ε κ * τ := by positivity
  -- 三项最小值条件等价于三个分量条件。
  unfold threshold
  rw [le_min_iff, le_min_iff, le_inv_sqrt_iff c (scaleK ε κ μ CP) hc_pos.le hK_pos,
    le_div_iff₀ hdenom_two_pos, le_div_iff₀ hdenom_three_pos]
  -- 此时只差乘法括号/次序；`ring` 检验两个表达式相等，双向逻辑未丢失。
  have hsecond_reorder : c * (8 * materialA ε κ * scaleK ε κ μ CP) =
      8 * c * materialA ε κ * scaleK ε κ μ CP := by ring
  have hthird_reorder : c * (8 * materialA ε κ * τ) = 8 * c * materialA ε κ * τ := by ring
  rw [hsecond_reorder, hthird_reorder]

/-- 由 `a=p+r` 推出非负性，仅需 `p,r≥0`；供零/正吸收分支判断使用。 -/
theorem absorptionSum_nonneg (p r : ℝ) (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r) :
    0 ≤ absorptionSum p r := add_nonneg hp_nonneg hr_nonneg

/-- 由 `b=pr` 推出非负性，仅需 `p,r≥0`；供耗散系数符号使用。 -/
theorem absorptionProduct_nonneg (p r : ℝ) (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r) :
    0 ≤ absorptionProduct p r := mul_nonneg hp_nonneg hr_nonneg

/-- V7 第 1 节零吸收区 `Z={a=0}` 的代数依据：在非负吸收下，
`a=0` 当且仅当 `p=r=0`。两个非负假设排除了正负抵消；用于分支权重。 -/
theorem absorptionSum_eq_zero_iff (p r : ℝ) (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r) :
    absorptionSum p r = 0 ↔ p = 0 ∧ r = 0 := by
  constructor
  · intro hsum_zero
    change p + r = 0 at hsum_zero
    -- 和为零且两项非负，因此两项均不能严格为正。
    have hp_zero : p = 0 := by linarith
    have hr_zero : r = 0 := by linarith
    exact ⟨hp_zero, hr_zero⟩
  · rintro ⟨hp_zero, hr_zero⟩
    simp [absorptionSum, hp_zero, hr_zero]

/-- 由 V7 (5.3) 推出 (5.4) 的 `a≤c/2`。
只使用 `p≤S,r≤S,S≤c/4`，这项纯加法估计无需额外正性假设。 -/
theorem absorptionSum_le_half (p r S c : ℝ)
    (hp_le_S : p ≤ S) (hr_le_S : r ≤ S) (hS_le : S ≤ c / 4) :
    absorptionSum p r ≤ c / 2 := by
  dsimp [absorptionSum]
  linarith

/-- V7 (5.4) 后文字使用的 `b≤a²/4`，由 `(p-r)²≥0` 推出。
它对任意实数 `p,r` 成立，不需要非负吸收假设；供 `ac-b` 的符号证明使用。 -/
theorem absorptionProduct_le_sum_sq_quarter (p r : ℝ) :
    absorptionProduct p r ≤ (absorptionSum p r) ^ 2 / 4 := by
  dsimp [absorptionProduct, absorptionSum]
  nlinarith only [sq_nonneg (p - r)]

/-- 由 V7 (5.3) 推出 (5.4) 的 `b≤c²/16`。
非负吸收及各自的幅度界允许相乘；没有假设吸收具有正下界。 -/
theorem absorptionProduct_le_c_sq_sixteenth (p r S c : ℝ)
    (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (hp_le_S : p ≤ S) (hr_le_S : r ≤ S) (hS_le : S ≤ c / 4) :
    absorptionProduct p r ≤ c ^ 2 / 16 := by
  have hp_le_quarter : p ≤ c / 4 := hp_le_S.trans hS_le
  have hr_le_quarter : r ≤ c / 4 := hr_le_S.trans hS_le
  have hquarter_nonneg : 0 ≤ c / 4 := hp_nonneg.trans hp_le_quarter
  have hproduct_le : p * r ≤ (c / 4) * (c / 4) :=
    mul_le_mul hp_le_quarter hr_le_quarter hr_nonneg hquarter_nonneg
  dsimp [absorptionProduct]
  nlinarith only [hproduct_le]

/-- V7 (5.4) 的 `ac-b≥0`：只需非负吸收及已推导的 `a≤c/2`。
先用 `(p-r)²≥0` 控制 `b`，再乘非负的 `a`；后续电块的系数正性将使用它。 -/
theorem absorptionSum_mul_sub_product_nonneg (p r c : ℝ)
    (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (ha_le_half : absorptionSum p r ≤ c / 2) :
    0 ≤ absorptionSum p r * c - absorptionProduct p r := by
  have ha_nonneg : 0 ≤ absorptionSum p r := absorptionSum_nonneg p r hp_nonneg hr_nonneg
  have hb_le : absorptionProduct p r ≤ (absorptionSum p r) ^ 2 / 4 :=
    absorptionProduct_le_sum_sq_quarter p r
  have hgap_nonneg : 0 ≤ c / 2 - absorptionSum p r := sub_nonneg.mpr ha_le_half
  have hscaled_gap_nonneg : 0 ≤ absorptionSum p r * (c / 2 - absorptionSum p r) :=
    mul_nonneg ha_nonneg hgap_nonneg
  nlinarith only [hb_le, hscaled_gap_nonneg, sq_nonneg (absorptionSum p r)]

/-- 由 V7 (5.2) 的第三个显式小量条件推出 (5.4) 的 `cτ≤κ/(8A)`。
局部引理只要求 `A>0` 和该显式条件；无需额外 `τ>0`，因为不除以 `τ`。 -/
theorem c_mul_tau_le_material_bound (ε κ τ c : ℝ)
    (hA_pos : 0 < materialA ε κ)
    (hsmall_tau : 8 * c * materialA ε κ * τ ≤ κ) :
    c * τ ≤ κ / (8 * materialA ε κ) := by
  have hdenom_pos : 0 < 8 * materialA ε κ := by positivity
  -- 仅在已经知道 `8A>0` 后消去分母。
  apply (le_div_iff₀ hdenom_pos).2
  calc
    c * τ * (8 * materialA ε κ) = 8 * c * materialA ε κ * τ := by ring
    _ ≤ κ := hsmall_tau

/-- V7 (5.4) 的严格材料界 `κ/(8A)<1/16`。
`ε>0` 给出 `A>2κ`，而 `κ>0` 保证所用物理分母为正；供宽界 `cτ≤1/4` 使用。 -/
theorem material_bound_lt_sixteenth (ε κ : ℝ) (hε_pos : 0 < ε) (hκ_pos : 0 < κ) :
    κ / (8 * materialA ε κ) < 1 / 16 := by
  have hA_pos : 0 < materialA ε κ := materialA_pos ε κ hε_pos hκ_pos
  have hdenom_pos : 0 < 8 * materialA ε κ := by positivity
  apply (div_lt_iff₀ hdenom_pos).2
  dsimp [materialA]
  linarith

/-- 汇总 V7 (5.4) 的时间尺度界：从论文阈值条件得到
`cτ≤κ/(8A)<1/16<1/4`，并单独输出后续常用的宽界 `cτ≤1/4`。
与双向等价定理连接，避免把论文应推出的条件直接作为额外输入。 -/
theorem c_mul_tau_bounds (ε κ τ μ CP c : ℝ)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ) (hτ_pos : 0 < τ)
    (hμ_pos : 0 < μ) (hCP_pos : 0 < CP) (hc_pos : 0 < c)
    (hc_le_threshold : c ≤ threshold ε κ τ μ CP) :
    c * τ ≤ κ / (8 * materialA ε κ) ∧
      κ / (8 * materialA ε κ) < 1 / 16 ∧
      (1 : ℝ) / 16 < 1 / 4 ∧ c * τ ≤ 1 / 4 := by
  have hsmall_tau : 8 * c * materialA ε κ * τ ≤ κ :=
    ((le_threshold_iff_explicit ε κ τ μ CP c hε_pos hκ_pos hτ_pos hμ_pos hCP_pos hc_pos).mp
      hc_le_threshold).2.2
  have hfirst : c * τ ≤ κ / (8 * materialA ε κ) :=
    c_mul_tau_le_material_bound ε κ τ c (materialA_pos ε κ hε_pos hκ_pos) hsmall_tau
  have hsecond : κ / (8 * materialA ε κ) < 1 / 16 :=
    material_bound_lt_sixteenth ε κ hε_pos hκ_pos
  have hthird : (1 : ℝ) / 16 < 1 / 4 := by norm_num
  exact ⟨hfirst, hsecond, hthird, (hfirst.trans_lt (hsecond.trans hthird)).le⟩

/-- 由 V7 (5.3)–(5.4) 推出的辅助界 `KS²≤1/16`，不是新的论文公式。
`S≥0,S≤c/4,c²K≤1,K≥0` 足够；供后续小量吸收估计复用。 -/
theorem scale_mul_amplitude_sq_le_sixteenth (K S c : ℝ)
    (hK_nonneg : 0 ≤ K) (hS_nonneg : 0 ≤ S)
    (hS_le : S ≤ c / 4) (hsmall_square : c ^ 2 * K ≤ 1) :
    K * S ^ 2 ≤ 1 / 16 := by
  have hquarter_nonneg : 0 ≤ c / 4 := hS_nonneg.trans hS_le
  have hS_square_le : S ^ 2 ≤ (c / 4) ^ 2 := by
    nlinarith only [hS_nonneg, hquarter_nonneg, hS_le]
  have hscaled_le : K * S ^ 2 ≤ K * (c / 4) ^ 2 :=
    mul_le_mul_of_nonneg_left hS_square_le hK_nonneg
  nlinarith only [hscaled_le, hsmall_square]

/-- V7 (5.2)–(5.3) 的一个具体参数证书（本项目构造的例子，不是论文编号）。
取 `ε=κ=τ=μ=CP=1`，于是 `A=3,K=24`；选择 `c=1/576`。
先验证所有参数为正，再调用已证双向等价并核验三个有理数不等式。
它说明阈值条件确实可满足；没有借此宣称 `CP=1` 已对应某个域的 Poincaré 常数。 -/
theorem unit_material_smallness_example :
    0 < (1 : ℝ) / 576 ∧ (1 : ℝ) / 576 ≤ threshold 1 1 1 1 1 := by
  have hone_pos : (0 : ℝ) < 1 := by norm_num
  have hc_pos : (0 : ℝ) < 1 / 576 := by norm_num
  refine ⟨hc_pos, ?_⟩
  -- 不直接计算平方根最小值；把论文条件交给已经验证的多项式接口。
  apply (le_threshold_iff_explicit 1 1 1 1 1 (1 / 576)
    hone_pos hone_pos hone_pos hone_pos hone_pos hc_pos).mpr
  norm_num [materialA, scaleK]

end LeanPML.PML
