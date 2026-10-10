import LeanPML.PML.Coefficients
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# V7 的点态分支权重：能量、分配与耗散

来源：../results/V7_Maxwell_Debye_PML/V7_global_energy.md
§5.1 (5.5) 定义能量权重 w；§7.1 (7.2) 给出耗散分式；
§9.2 (9.2) 使用另一组分配权重 θ。三者不能因为都有分母 a 就混同。

p、r 是某空间点的吸收值，可以来自变系数场；a=p+r。c 是正移位参数，
S 是吸收幅度上界。此处不假设 p、r 或 a 有统一正下界。

建议阅读：weights_of_sum_zero → energyWeights_lower_bound → theta_partition，
再读耗散界、四分支实例与趋零吸收族。小量条件的材料部分见 Coefficients。
总函数用 if 0<a then ... else ...；物理假设 p,r≥0 保证 else 恰是 a=0。
对物理范围以外的 a<0，else 的取值仅是实现约定，不作物理解释。

本文件只做系数代数。没有构造 L²_w、证明 Poincaré、可测性、空间积分或 PDE
能量恒等式。(7.2) 在零区仍有独立的 c|∇v|²，不能被分式的零值替代。
-/

namespace LeanPML.PML

/-- V7 (5.5)：x 能量权重；正分支分子是 c-r，零区为 0。供能量下界使用。 -/
noncomputable def energyWeightX (c p r : ℝ) : ℝ :=
  if 0 < absorptionSum p r then (c - r) / absorptionSum p r else 0

/-- V7 (5.5)：y 能量权重；正分支分子是 c-p，零区为 0。 -/
noncomputable def energyWeightY (c p r : ℝ) : ℝ :=
  if 0 < absorptionSum p r then (c - p) / absorptionSum p r else 0

/-- V7 §9.2、(9.2) 前：θx=p/a 于正分支，零区取 1/2，用于分配空间估计。 -/
noncomputable def thetaX (p r : ℝ) : ℝ :=
  if 0 < absorptionSum p r then p / absorptionSum p r else 1 / 2

/-- V7 §9.2、(9.2) 前：θy=r/a 于正分支，零区取 1/2，保证两权重和为 1。 -/
noncomputable def thetaY (p r : ℝ) : ℝ :=
  if 0 < absorptionSum p r then r / absorptionSum p r else 1 / 2

/-- V7 (7.2) 的 σi(c+σi)/a，其中 s=σi、t=σj。
这是一个分式系数，不是完整耗散密度。Lean 的除零总定义不替代零区耗散项。 -/
noncomputable def dissipationPlus (c s t : ℝ) : ℝ :=
  s * (c + s) / absorptionSum s t

/-- V7 (7.2) 的 σj(c-σj)/a；使用时取 s=σj、t=σi。
正分支的非负和上界将在下方证明，不作为定义字段。 -/
noncomputable def dissipationMinus (c s t : ℝ) : ℝ :=
  s * (c - s) / absorptionSum s t

/-- 由 V7 (5.5)、§9.2 的定义：a=0 时 w=(0,0)，θ=(1/2,1/2)。
输入只需分支等式，不需除法或正参数；供零区实例和分支分析使用。 -/
theorem weights_of_sum_zero (c p r : ℝ) (ha_zero : absorptionSum p r = 0) :
    energyWeightX c p r = 0 ∧ energyWeightY c p r = 0 ∧
    thetaX p r = 1 / 2 ∧ thetaY p r = 1 / 2 := by
  -- 把条件中的 a 改写成 0，if 的正分支不成立；此处没有除以 a。
  simp [energyWeightX, energyWeightY, thetaX, thetaY, ha_zero]

/-- 由 V7 (5.3)、(5.5) 推出：a>0 时两个能量权重至少为 3/2。
幅度条件给出 a≤c/2、p,r≤c/4；ha_pos 使乘分母保持不等号方向。
不要求 p、r 分别为正。后续可用于加权能量的点态下界。 -/
theorem energyWeights_lower_bound (c p r S : ℝ)
    (ha_pos : 0 < absorptionSum p r)
    (hp_le_S : p ≤ S) (hr_le_S : r ≤ S) (hS_le : S ≤ c / 4) :
    (3 / 2 : ℝ) ≤ energyWeightX c p r ∧
    (3 / 2 : ℝ) ≤ energyWeightY c p r := by
  have ha_le : absorptionSum p r ≤ c / 2 :=
    absorptionSum_le_half p r S c hp_le_S hr_le_S hS_le
  have hp_le_quarter : p ≤ c / 4 := hp_le_S.trans hS_le
  have hr_le_quarter : r ≤ c / 4 := hr_le_S.trans hS_le
  constructor
  · -- 正分母允许把 3/2 ≤ (c-r)/a 变成 (3/2)*a ≤ c-r。
    rw [energyWeightX, if_pos ha_pos]
    apply (le_div_iff₀ ha_pos).2
    linarith
  · rw [energyWeightY, if_pos ha_pos]
    apply (le_div_iff₀ ha_pos).2
    linarith

/-- V7 §9.2 的点态分配性质：非负 p,r 给出 0≤θi≤1 且 θx+θy=1。
正区利用 p,r≤a；零区使用 1/2 分配，不使用 V6 的零延拓比值。
后续 J(U) 的估计需要这个分配恒等式，但此处没有定义空间积分 J。 -/
theorem theta_partition (p r : ℝ)
    (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r) :
    (0 ≤ thetaX p r ∧ thetaX p r ≤ 1) ∧
    (0 ≤ thetaY p r ∧ thetaY p r ≤ 1) ∧
    thetaX p r + thetaY p r = 1 := by
  by_cases ha_pos : 0 < absorptionSum p r
  · have ha_ne : absorptionSum p r ≠ 0 := ne_of_gt ha_pos
    have hp_le_a : p ≤ absorptionSum p r := by
      dsimp [absorptionSum]
      linarith
    have hr_le_a : r ≤ absorptionSum p r := by
      dsimp [absorptionSum]
      linarith
    have hx_nonneg : 0 ≤ p / absorptionSum p r := div_nonneg hp_nonneg ha_pos.le
    have hy_nonneg : 0 ≤ r / absorptionSum p r := div_nonneg hr_nonneg ha_pos.le
    have hx_le : p / absorptionSum p r ≤ 1 :=
      (div_le_iff₀ ha_pos).2 (by simpa using hp_le_a)
    have hy_le : r / absorptionSum p r ≤ 1 :=
      (div_le_iff₀ ha_pos).2 (by simpa using hr_le_a)
    have hsum : p / absorptionSum p r + r / absorptionSum p r = 1 := by
      -- 合并同分母，再用 a≠0 约分；分母非零证据来自当前正区分支。
      calc
        p / absorptionSum p r + r / absorptionSum p r =
            (p + r) / absorptionSum p r := (add_div _ _ _).symm
        _ = 1 := div_self ha_ne
    simpa only [thetaX, thetaY, if_pos ha_pos] using
      And.intro (And.intro hx_nonneg hx_le) (And.intro (And.intro hy_nonneg hy_le) hsum)
  · -- 在物理非负范围，非正分支实际等于零，而非一个负吸收区。
    have ha_zero : absorptionSum p r = 0 :=
      le_antisymm (le_of_not_gt ha_pos) (absorptionSum_nonneg p r hp_nonneg hr_nonneg)
    have hzero_values := weights_of_sum_zero 0 p r ha_zero
    rw [hzero_values.2.2.1, hzero_values.2.2.2]
    norm_num

/-- 由 V7 (7.2) 推出正分式的显式界 0≤s(c+s)/(s+t)≤c+S。
c,s,t 非负且 a>0；只用 s≤S，不要求吸收正下界。供耗散有界性使用。 -/
theorem dissipationPlus_bounds (c s t S : ℝ)
    (hc_nonneg : 0 ≤ c) (hs_nonneg : 0 ≤ s) (ht_nonneg : 0 ≤ t)
    (ha_pos : 0 < absorptionSum s t) (hs_le_S : s ≤ S) :
    0 ≤ dissipationPlus c s t ∧ dissipationPlus c s t ≤ c + S := by
  have hs_le_a : s ≤ absorptionSum s t := by
    dsimp [absorptionSum]
    linarith
  have hratio_le : s / absorptionSum s t ≤ 1 :=
    (div_le_iff₀ ha_pos).2 (by simpa using hs_le_a)
  have hfactor_nonneg : 0 ≤ c + s := add_nonneg hc_nonneg hs_nonneg
  constructor
  · exact div_nonneg (mul_nonneg hs_nonneg hfactor_nonneg) ha_pos.le
  · calc
      dissipationPlus c s t = (s / absorptionSum s t) * (c + s) := by
        dsimp [dissipationPlus]
        ring
      _ ≤ 1 * (c + s) := mul_le_mul_of_nonneg_right hratio_le hfactor_nonneg
      _ ≤ c + S := by linarith

/-- 由 (5.3)、(7.2) 推出更统一的上界 5c/4；分母可任意接近零。
先调用 c+S 界，再使用 S≤c/4；不是额外假设系数有界。 -/
theorem dissipationPlus_le_five_quarters (c s t S : ℝ)
    (hc_nonneg : 0 ≤ c) (hs_nonneg : 0 ≤ s) (ht_nonneg : 0 ≤ t)
    (ha_pos : 0 < absorptionSum s t) (hs_le_S : s ≤ S) (hS_le : S ≤ c / 4) :
    dissipationPlus c s t ≤ 5 * c / 4 := by
  have hbound : dissipationPlus c s t ≤ c + S :=
    (dissipationPlus_bounds c s t S hc_nonneg hs_nonneg ht_nonneg ha_pos hs_le_S).2
  linarith

/-- 由 V7 (7.2) 推出 0≤s(c-s)/(s+t)≤c。
只需 0≤s≤c、t≥0 和 a>0；正式幅度条件 s≤S≤c/4 蕴含 s≤c。
先证 c-s 非负才乘不等式，后续用于交叉方向的耗散系数。 -/
theorem dissipationMinus_bounds (c s t : ℝ)
    (hs_nonneg : 0 ≤ s) (ht_nonneg : 0 ≤ t) (hs_le_c : s ≤ c)
    (ha_pos : 0 < absorptionSum s t) :
    0 ≤ dissipationMinus c s t ∧ dissipationMinus c s t ≤ c := by
  have hs_le_a : s ≤ absorptionSum s t := by
    dsimp [absorptionSum]
    linarith
  have hratio_le : s / absorptionSum s t ≤ 1 :=
    (div_le_iff₀ ha_pos).2 (by simpa using hs_le_a)
  have hfactor_nonneg : 0 ≤ c - s := sub_nonneg.mpr hs_le_c
  constructor
  · exact div_nonneg (mul_nonneg hs_nonneg hfactor_nonneg) ha_pos.le
  · calc
      dissipationMinus c s t = (s / absorptionSum s t) * (c - s) := by
        dsimp [dissipationMinus]
        ring
      _ ≤ 1 * (c - s) := mul_le_mul_of_nonneg_right hratio_le hfactor_nonneg
      _ ≤ c := by linarith

/-!
## 四种吸收分支的精确实例

取 c=4、S=1，各吸收取 0 或 1。norm_num 验证所用幅度假设，随后调用一般定理。
这些实例仅展示本文件的幅度/权重性质；不宣称 c=4 对任意材料满足 (5.2)。
完整材料小量参数的证书见 Coefficients 文件中的实例。
-/

/-- V7 (5.5)、(9.2) 的零区实例：p=r=0 满足 0≤p,r≤S=1=c/4。
调用一般零分支定理，保留 w=0 与 θ=1/2 的区别。 -/
theorem zero_absorption_example :
    (0 : ℝ) ≤ 1 ∧ energyWeightX 4 0 0 = 0 ∧ energyWeightY 4 0 0 = 0 ∧
    thetaX 0 0 = 1 / 2 ∧ thetaY 0 0 = 1 / 2 := by
  have ha_zero : absorptionSum 0 0 = 0 := by norm_num [absorptionSum]
  exact ⟨by norm_num, weights_of_sum_zero 4 0 0 ha_zero⟩

/-- 由 (5.3)、(5.5)、(9.2) 得到 x 边层实例：p=1>0,r=0,c=4,S=1。
先验证幅度与正分支条件并调用一般下界，再精确计算权重。 -/
theorem x_layer_example :
    ((3 / 2 : ℝ) ≤ energyWeightX 4 1 0 ∧ (3 / 2 : ℝ) ≤ energyWeightY 4 1 0) ∧
    energyWeightX 4 1 0 = 4 ∧ energyWeightY 4 1 0 = 3 ∧
    thetaX 1 0 = 1 ∧ thetaY 1 0 = 0 := by
  have hbounds := energyWeights_lower_bound 4 1 0 1
    (by norm_num [absorptionSum]) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hbounds, ?_⟩
  norm_num [energyWeightX, energyWeightY, thetaX, thetaY, absorptionSum]

/-- 与 x 边层对称的 y 边层实例：p=0,r=1>0，同样调用一般定理。
来源与用途同上，验证代码没有漏掉另一个单轴退化方向。 -/
theorem y_layer_example :
    ((3 / 2 : ℝ) ≤ energyWeightX 4 0 1 ∧ (3 / 2 : ℝ) ≤ energyWeightY 4 0 1) ∧
    energyWeightX 4 0 1 = 3 ∧ energyWeightY 4 0 1 = 4 ∧
    thetaX 0 1 = 0 ∧ thetaY 0 1 = 1 := by
  have hbounds := energyWeights_lower_bound 4 0 1 1
    (by norm_num [absorptionSum]) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hbounds, ?_⟩
  norm_num [energyWeightX, energyWeightY, thetaX, thetaY, absorptionSum]

/-- V7 (5.3)、(5.5) 的角层实例：p=r=1>0,c=4,S=1。
能量权重恰好达到 3/2 下界，θ 均为 1/2；一般下界在此被实际调用。 -/
theorem corner_example :
    ((3 / 2 : ℝ) ≤ energyWeightX 4 1 1 ∧ (3 / 2 : ℝ) ≤ energyWeightY 4 1 1) ∧
    energyWeightX 4 1 1 = 3 / 2 ∧ energyWeightY 4 1 1 = 3 / 2 ∧
    thetaX 1 1 = 1 / 2 ∧ thetaY 1 1 = 1 / 2 := by
  have hbounds := energyWeights_lower_bound 4 1 1 1
    (by norm_num [absorptionSum]) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hbounds, ?_⟩
  norm_num [energyWeightX, energyWeightY, thetaX, thetaY, absorptionSum]

/-- 为 V7 (5.5) 后“w 可无界”的说明构造的参数族，不是论文编号公式。
固定 c>0，令 r=0、p_n=c/(n+4)，幅度界统一取 S=c/4。 -/
noncomputable def vanishingAbsorption (c : ℝ) (n : ℕ) : ℝ :=
  c / ((n : ℝ) + 4)

/-- 上述参数族分母严格为正；自然数转实数仍非负。
这是合法除法与后续约分的公共证据，由参数族定义推出。 -/
theorem family_denominator_pos (n : ℕ) : 0 < (n : ℝ) + 4 := by
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- 由参数族定义推出 0<p_n≤c/4；c>0 用于正性和乘法保序。
因此所有 n 都符合 V7 (5.3) 的点态幅度限制，供无界性实例使用。 -/
theorem vanishingAbsorption_bounds (c : ℝ) (hc_pos : 0 < c) (n : ℕ) :
    0 < vanishingAbsorption c n ∧ vanishingAbsorption c n ≤ c / 4 := by
  have hden_pos : 0 < (n : ℝ) + 4 := family_denominator_pos n
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  constructor
  · exact div_pos hc_pos hden_pos
  · change c / ((n : ℝ) + 4) ≤ c / 4
    -- 两个分母正，交叉相乘合法；目标变成 4c≤c(n+4)。
    apply (div_le_div_iff₀ hden_pos (by norm_num : (0 : ℝ) < 4)).2
    nlinarith [mul_nonneg hc_pos.le hn_nonneg]

/-- 参数族确实趋近零的 ε-N 形式：任意 δ>0，充分大 n 都有 p_n<δ。
由阿基米德性质与代数推出，无需预先建立极限或函数空间框架。 -/
theorem vanishingAbsorption_eventually_small (c : ℝ) (hc_pos : 0 < c)
    (δ : ℝ) (hδ_pos : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < vanishingAbsorption c n ∧
      vanishingAbsorption c n < δ := by
  obtain ⟨N, hN_large⟩ := exists_nat_gt (c / δ)
  refine ⟨N, ?_⟩
  intro n hn_ge
  have hN_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hc_lt_Nδ : c < (N : ℝ) * δ := (div_lt_iff₀ hδ_pos).1 hN_large
  have hden_pos : 0 < (n : ℝ) + 4 := family_denominator_pos n
  refine ⟨(vanishingAbsorption_bounds c hc_pos n).1, ?_⟩
  change c / ((n : ℝ) + 4) < δ
  apply (div_lt_iff₀ hden_pos).2
  -- N≤n 与 δ>0 给出 Nδ≤nδ；加上 4δ 后得到所需的严格不等式。
  nlinarith [mul_nonneg (sub_nonneg.mpr hN_le_n) hδ_pos.le]

/-- 参数族上 (5.5) 的精确权重是 wx=n+4、wy=n+3。
先确认 a=p_n>0 再展开正分支；field_simp 只使用已展示的非零分母证据。 -/
theorem energyWeights_on_family (c : ℝ) (hc_pos : 0 < c) (n : ℕ) :
    energyWeightX c (vanishingAbsorption c n) 0 = (n : ℝ) + 4 ∧
    energyWeightY c (vanishingAbsorption c n) 0 = (n : ℝ) + 3 := by
  have hp_pos : 0 < vanishingAbsorption c n := (vanishingAbsorption_bounds c hc_pos n).1
  have ha_pos : 0 < absorptionSum (vanishingAbsorption c n) 0 := by
    simpa only [absorptionSum, add_zero] using hp_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hden_ne : (n : ℝ) + 4 ≠ 0 := ne_of_gt (family_denominator_pos n)
  constructor
  · rw [energyWeightX, if_pos ha_pos]
    dsimp [absorptionSum, vanishingAbsorption]
    field_simp [hc_ne, hden_ne]
    -- 消分母后仅剩含 0 的多项式等式，用 ring 收尾。
    ring
  · rw [energyWeightY, if_pos ha_pos]
    dsimp [absorptionSum, vanishingAbsorption]
    field_simp [hc_ne, hden_ne]
    ring

/-- V7 (5.5) 后“能量权重可无界”的正式见证：固定任意 c>0，
任何实数 M 都被同族某项的两个能量权重严格超过，故不存在统一有限上界。
这是由参数族计算和阿基米德性质推出的结论，不声称每个吸收场都无界。 -/
theorem energyWeights_unbounded (c : ℝ) (hc_pos : 0 < c) :
    ∀ M : ℝ, ∃ n : ℕ,
      M < energyWeightX c (vanishingAbsorption c n) 0 ∧
      M < energyWeightY c (vanishingAbsorption c n) 0 := by
  intro M
  obtain ⟨n, hn_large⟩ := exists_nat_gt M
  have hweights := energyWeights_on_family c hc_pos n
  refine ⟨n, ?_, ?_⟩
  · rw [hweights.1]
    linarith
  · rw [hweights.2]
    linarith

end LeanPML.PML
