import LeanPML.PML.Coefficients
import LeanPML.PML.TimeInvariants

/-!
# V7 极化块：代数、真实求导、约束消元分层

来源：../results/V7_Maxwell_Debye_PML/V7_global_energy.md 的 (6.1)、(6.2)、
(7.4)、(8.1)–(8.2)。本文件在固定空间点研究时间路径 v、R、z : ℝ → ℝ；
a、b、c、κ、τ 是时间常参数，不要求 a、b 在整个空间为常数。
vDot、RDot 仅表示某时刻的数值；只有配合 HasDerivAt 才表示真实导数。

Q 是未除系数的二次型，F_D=Q/(2κ)，余项 D_D 的分母是 κ。
完整能量 (6.2) 的极化密度是 μ*F_D，还要进行空间积分。
D_D 含可能为负的 a-c 等系数，本文件不宣称它单独非负或能量单调。
这也不是 v0.1.2 的教学 Debye 能量：这里只用 z'=R 和 primitive 兼容关系，
不额外输入 εE'=-P'。

建议顺序：定义 → 邻域兼容关系的真实求导 → Q 的逐项求导 →
(7.4) → (8.1) → (8.2) 系数界 → 非零实例。后续空间积分、Green 公式和全域正定性仍未实现。
-/

open scoped Topology

namespace LeanPML.PML

/-- V7 (6.2)、(7.4)：未带前置因子的极化二次型 Q；R、z 在此是实数值。
参数不需要正性。后续先对实际路径上的 Q 求导，再除以 2κ。 -/
noncomputable def polarQuadratic (a b c τ R z : ℝ) : ℝ :=
  (1 + (a + c) * τ) * R ^ 2 +
    2 * (c + b * τ) * R * z +
    (a * c + b * (1 + c * τ)) * z ^ 2

/-- V7 (7.4)：局部极化能量 F_D=Q/(2κ)，尚未乘 (6.2) 中的 μ。
κ≠0 不是定义的附带条件，必要时由后续定理显式输入。 -/
noncomputable def polarEnergy (a b c κ τ R z : ℝ) : ℝ :=
  polarQuadratic a b c τ R z / (2 * κ)

/-- V7 (7.4)：局部余项 D_D。名称不预设其非负性；
RDot 在此只是数值，真实时间定理会将它与 R 的导数绑定。 -/
noncomputable def polarRemainder (a b c κ τ R z RDot : ℝ) : ℝ :=
  (τ * RDot ^ 2 + (a - c + τ * (a * c - b)) * R ^ 2 + b * c * z ^ 2) / κ

/-- V7 (8.1)：消元后的 R² 系数 A_R，与材料常数 A=ε+2κ 不是同一对象。
此定义供约束消元和后续 (8.2) 的界使用，不预设正性。 -/
noncomputable def polarCoeffAR (a b c τ : ℝ) : ℝ :=
  1 + (a - c) * τ + (a * c - b) * τ ^ 2 + b * c * τ ^ 3

/-- V7 (8.1)：消元后的 v² 系数中出现的 G，完整系数是 κ²G。
参数在此为任意实数；符号与上界需要另证。 -/
noncomputable def polarCoeffG (a b c τ : ℝ) : ℝ :=
  a * c + b * (1 + c * τ)

/-- 将 (7.4) 的数值表达式变成真实函数 t↦F_D(R(t),z(t))。
此定义本身不附带求导、兼容或耗散条件。 -/
noncomputable def polarEnergyAlong (a b c κ τ : ℝ) (R z : ℝ → ℝ) (t : ℝ) : ℝ :=
  polarEnergy a b c κ τ (R t) (z t)

/-- 由 V7 (6.1) 推出的导数约束：κv'=R+τR'。
hcompat 要求兼容关系在 t 的某邻域成立；单点相等不足以求导。
hv、hR、hz 分别绑定真实 v'、R'、z'=R；参数不需正性。
输出供 (7.4) 的移位约束使用，不需要教学方程 εE'=-P'。 -/
theorem polar_constraint_derivative (κ τ : ℝ) (v R z : ℝ → ℝ)
    (t vDot RDot : ℝ)
    (hv : HasDerivAt v vDot t)
    (hR : HasDerivAt R RDot t)
    (hz : HasDerivAt z (R t) t)
    (hcompat : ∀ᶠ s in 𝓝 t, z s + τ * R s = κ * v s) :
    κ * vDot = R t + τ * RDot := by
  -- 左侧路径 z+τR 与右侧路径 κv 各自有真实求导证据。
  have hleft : HasDerivAt (fun s => z s + τ * R s)
      (R t + τ * RDot) t :=
    hz.add (hR.const_mul τ)
  have hright : HasDerivAt (fun s => κ * v s) (κ * vDot) t :=
    hv.const_mul κ
  -- congr_of_eventuallyEq 把邻域相同的函数换成同一函数，才可使用导数唯一性。
  have hleft_on_right : HasDerivAt (fun s => κ * v s)
      (R t + τ * RDot) t :=
    hleft.congr_of_eventuallyEq (Filter.EventuallyEq.symm hcompat)
  exact hright.unique hleft_on_right

/-- 由 V7 (6.1) 推出 (7.4) 前的移位约束。
先调用真实导数约束，再使用邻域兼容在 t 处的取值；输出是乘子 κ(v'+cv)。 -/
theorem polar_shifted_constraint (c κ τ : ℝ) (v R z : ℝ → ℝ)
    (t vDot RDot : ℝ)
    (hv : HasDerivAt v vDot t)
    (hR : HasDerivAt R RDot t)
    (hz : HasDerivAt z (R t) t)
    (hcompat : ∀ᶠ s in 𝓝 t, z s + τ * R s = κ * v s) :
    κ * (vDot + c * v t) =
      τ * RDot + (1 + c * τ) * R t + c * z t := by
  have hderived : κ * vDot = R t + τ * RDot :=
    polar_constraint_derivative κ τ v R z t vDot RDot hv hR hz hcompat
  have hvalue : z t + τ * R t = κ * v t := Filter.EventuallyEq.eq_of_nhds hcompat
  calc
    κ * (vDot + c * v t) = κ * vDot + c * (κ * v t) := by ring
    _ = (R t + τ * RDot) + c * (z t + τ * R t) := by rw [hderived, ← hvalue]
    _ = τ * RDot + (1 + c * τ) * R t + c * z t := by ring

/-- V7 (7.4) 的低层代数核验。RDot、vDot 在本条中只是实数，
hshift 是已求导约束的数值形式；本条不独立宣称能量可导。
κ≠0 使除法合法；上层 HasDerivAt 定理负责推导 hshift 并调用本条。 -/
theorem polar_rate_algebra (a b c κ τ v R z vDot RDot : ℝ)
    (hκ_ne : κ ≠ 0)
    (hshift : κ * (vDot + c * v) = τ * RDot + (1 + c * τ) * R + c * z) :
    (2 * (1 + (a + c) * τ) * R * RDot +
      2 * (c + b * τ) * (RDot * z + R ^ 2) +
      2 * (a * c + b * (1 + c * τ)) * z * R) / (2 * κ) =
    (RDot + a * R + b * z) * (vDot + c * v) -
      polarRemainder a b c κ τ R z RDot := by
  -- 先把唯一出现 vDot+cv 的因子写成已知约束除以 κ。
  have hmultiplier : vDot + c * v =
      (τ * RDot + (1 + c * τ) * R + c * z) / κ := by
    apply (eq_div_iff hκ_ne).2
    calc
      (vDot + c * v) * κ = κ * (vDot + c * v) := mul_comm _ _
      _ = τ * RDot + (1 + c * τ) * R + c * z := hshift
  rw [hmultiplier]
  unfold polarRemainder
  -- hκ_ne 已给出；field_simp 清除 2κ、κ，ring 仅展开剩下的多项式恒等式。
  field_simp [hκ_ne]
  ring

/-- V7 (7.4) 二次型的真实逐项求导，尚未代入兼容关系。
hR、hz 给出 R' 和 z'=R；平方规则、乘积规则、常数规则共同得到 Q'。
本条无需 κ 或参数符号，供 F_D 的求导定理使用。 -/
theorem hasDerivAt_polarQuadratic (a b c τ : ℝ) (R z : ℝ → ℝ)
    (t RDot : ℝ) (hR : HasDerivAt R RDot t) (hz : HasDerivAt z (R t) t) :
    HasDerivAt (fun s => polarQuadratic a b c τ (R s) (z s))
      (2 * (1 + (a + c) * τ) * R t * RDot +
        2 * (c + b * τ) * (RDot * z t + (R t) ^ 2) +
        2 * (a * c + b * (1 + c * τ)) * z t * R t) t := by
  -- 第一、第三项用平方求导；中间交叉项用 (Rz)'=R'z+Rz'。
  have hR_square : HasDerivAt
      (fun s => (1 + (a + c) * τ) * (R s) ^ 2)
      ((1 + (a + c) * τ) * (2 * R t * RDot)) t := by
    exact ((hR.pow 2).const_mul (1 + (a + c) * τ)).congr_deriv (by ring)
  have hcross : HasDerivAt
      (fun s => (2 * (c + b * τ)) * (R s * z s))
      ((2 * (c + b * τ)) * (RDot * z t + R t * R t)) t :=
    (hR.mul hz).const_mul (2 * (c + b * τ))
  have hz_square : HasDerivAt
      (fun s => (a * c + b * (1 + c * τ)) * (z s) ^ 2)
      ((a * c + b * (1 + c * τ)) * (2 * z t * R t)) t := by
    exact ((hz.pow 2).const_mul (a * c + b * (1 + c * τ))).congr_deriv (by ring)
  have hsum : HasDerivAt
      (fun s => (1 + (a + c) * τ) * (R s) ^ 2 +
        (2 * (c + b * τ)) * (R s * z s) +
        (a * c + b * (1 + c * τ)) * (z s) ^ 2)
      ((1 + (a + c) * τ) * (2 * R t * RDot) +
        (2 * (c + b * τ)) * (RDot * z t + R t * R t) +
        (a * c + b * (1 + c * τ)) * (2 * z t * R t)) t :=
    (hR_square.add hcross).add hz_square
  -- 函数层：仅统一交叉项括号；逐点相等因而在 t 的邻域相等。
  have hQ : HasDerivAt (fun s => polarQuadratic a b c τ (R s) (z s))
      ((1 + (a + c) * τ) * (2 * R t * RDot) +
        (2 * (c + b * τ)) * (RDot * z t + R t * R t) +
        (a * c + b * (1 + c * τ)) * (2 * z t * R t)) t := by
    apply hsum.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s => by
      dsimp [polarQuadratic]
      ring)
  -- 导数值层：ring 只将 R*R 写为 R²、整理乘法顺序，没有新增可导假设。
  exact hQ.congr_deriv (by ring)

/-- V7 (7.4) 的真实求导定理：F_D'=(R'+aR+bz)(v'+cv)-D_D。
函数和导数值由三份 HasDerivAt 证据连接；邻域兼容产生所需约束。
仅除以 κ，故只需 κ≠0；物理 κ>0 可用 hκ_pos.ne' 提供该证据。
本结论是局部恒等式，未证明各块单独非负或单调。 -/
theorem hasDerivAt_polarEnergy (a b c κ τ : ℝ) (v R z : ℝ → ℝ)
    (t vDot RDot : ℝ) (hκ_ne : κ ≠ 0)
    (hv : HasDerivAt v vDot t)
    (hR : HasDerivAt R RDot t)
    (hz : HasDerivAt z (R t) t)
    (hcompat : ∀ᶠ s in 𝓝 t, z s + τ * R s = κ * v s) :
    HasDerivAt (polarEnergyAlong a b c κ τ R z)
      ((RDot + a * R t + b * z t) * (vDot + c * v t) -
        polarRemainder a b c κ τ (R t) (z t) RDot) t := by
  have hshift : κ * (vDot + c * v t) =
      τ * RDot + (1 + c * τ) * R t + c * z t :=
    polar_shifted_constraint c κ τ v R z t vDot RDot hv hR hz hcompat
  -- div_const 把 Q' 变成 F_D'=Q'/(2κ)，不把任何目标导数当作假设。
  have henergy : HasDerivAt (polarEnergyAlong a b c κ τ R z)
      ((2 * (1 + (a + c) * τ) * R t * RDot +
        2 * (c + b * τ) * (RDot * z t + (R t) ^ 2) +
        2 * (a * c + b * (1 + c * τ)) * z t * R t) / (2 * κ)) t :=
    (hasDerivAt_polarQuadratic a b c τ R z t RDot hR hz).div_const (2 * κ)
  apply henergy.congr_deriv
  exact polar_rate_algebra a b c κ τ (v t) (R t) (z t) vDot RDot hκ_ne hshift

/-- (7.4) 的开区间入口：兼容关系仅在 (0,T) 成立便足够。
t 在开区间内部，所以该区间是 t 的邻域；不需要端点普通导数或区间外兼容。
后续可将 v0.1.3 的兼容保持结果限制到此开区间。 -/
theorem hasDerivAt_polarEnergy_on_Ioo (a b c κ τ T : ℝ) (v R z : ℝ → ℝ)
    (t vDot RDot : ℝ) (hκ_ne : κ ≠ 0) (ht : t ∈ Set.Ioo 0 T)
    (hv : HasDerivAt v vDot t)
    (hR : HasDerivAt R RDot t)
    (hz : HasDerivAt z (R t) t)
    (hcompat : ∀ s ∈ Set.Ioo 0 T, z s + τ * R s = κ * v s) :
    HasDerivAt (polarEnergyAlong a b c κ τ R z)
      ((RDot + a * R t + b * z t) * (vDot + c * v t) -
        polarRemainder a b c κ τ (R t) (z t) RDot) t := by
  have hcompat_near : ∀ᶠ s in 𝓝 t, z s + τ * R s = κ * v s :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) hcompat
  exact hasDerivAt_polarEnergy a b c κ τ v R z t vDot RDot hκ_ne hv hR hz hcompat_near

/-- V7 (8.1)：用单点约束 z+τR=κv 消去 z，精确重写 Q。
这里没有求导，所以单点等式已经足够，也无需任何参数正性或非零条件。
输出供 polarEnergy_eq_reduced 调用；不能据此直接宣称全域正定性。 -/
theorem polarQuadratic_eq_reduced (a b c κ τ v R z : ℝ)
    (hcompat : z + τ * R = κ * v) :
    polarQuadratic a b c τ R z =
      polarCoeffAR a b c τ * R ^ 2 +
        2 * κ * c * (1 - a * τ - b * τ ^ 2) * v * R +
        κ ^ 2 * polarCoeffG a b c τ * v ^ 2 := by
  have hz_value : z = κ * v - τ * R := eq_sub_of_add_eq hcompat
  -- 代入是等式改写；ring 核验所有交叉项和 A_R、G 的精确系数。
  rw [hz_value]
  unfold polarQuadratic polarCoeffAR polarCoeffG
  ring

/-- 由 V7 (8.1) 推出的 F_D 约束表达式。对 Q 的消元后仍须除以 2κ；
完整 (6.2) 还要乘 μ 并积分。本条是消元引理的实际调用者。 -/
theorem polarEnergy_eq_reduced (a b c κ τ v R z : ℝ)
    (hcompat : z + τ * R = κ * v) :
    polarEnergy a b c κ τ R z =
      (polarCoeffAR a b c τ * R ^ 2 +
        2 * κ * c * (1 - a * τ - b * τ ^ 2) * v * R +
        κ ^ 2 * polarCoeffG a b c τ * v ^ 2) / (2 * κ) := by
  unfold polarEnergy
  rw [polarQuadratic_eq_reduced a b c κ τ v R z hcompat]

/-- V7 第 8 节 (8.2) 的全部四组点态系数界。
这里先使用 (5.4) 给出的中间条件：非负吸收、幅度上界、`ac-b≥0` 和
`cτ≤1/4`。它们在后续 `polar_coefficients_bounds_of_threshold` 中由原参数推导，
不是最终入口额外要求的结论。正性允许对不等式乘以 `c,τ` 而不反向；
没有除以 `a` 或 `b`，所以包括零吸收。
输出仅是实数系数上下界；尚未证明整个二次型或空间能量的正定性。 -/
theorem polar_coefficients_bounds_of_local_conditions (a b c τ : ℝ)
    (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b)
    (hc_pos : 0 < c) (hτ_pos : 0 < τ)
    (ha_le_half : a ≤ c / 2) (hb_le_sixteenth : b ≤ c ^ 2 / 16)
    (hac_sub_b_nonneg : 0 ≤ a * c - b)
    (hcτ_le_quarter : c * τ ≤ 1 / 4) :
    (3 / 4 ≤ polarCoeffAR a b c τ ∧ polarCoeffAR a b c τ ≤ 5 / 4) ∧
      (0 ≤ 1 - a * τ - b * τ ^ 2 ∧ 1 - a * τ - b * τ ^ 2 ≤ 1) ∧
      (0 ≤ polarCoeffG a b c τ ∧ polarCoeffG a b c τ ≤ (37 / 64) * c ^ 2) ∧
      (0 ≤ b + a * c ∧ b + a * c ≤ (9 / 16) * c ^ 2) := by
  -- 先把时间尺度归一化：x=cτ∈[0,1/4]。下面不引入隐藏的参数结构。
  have hcτ_nonneg : 0 ≤ c * τ := mul_nonneg hc_pos.le hτ_pos.le
  have hcτ_sq_le : (c * τ) ^ 2 ≤ (1 : ℝ) / 16 := by
    -- 非负的 x≤1/4 蕴含 x²≤1/16。
    nlinarith only [hcτ_nonneg, hcτ_le_quarter]
  have haτ_nonneg : 0 ≤ a * τ := mul_nonneg ha_nonneg hτ_pos.le
  have haτ_le : a * τ ≤ (1 : ℝ) / 8 := by
    have haτ_le_half_cτ : a * τ ≤ (c / 2) * τ :=
      mul_le_mul_of_nonneg_right ha_le_half hτ_pos.le
    nlinarith only [haτ_le_half_cτ, hcτ_le_quarter]
  have hbτ_sq_nonneg : 0 ≤ b * τ ^ 2 := mul_nonneg hb_nonneg (sq_nonneg τ)
  have hbτ_sq_le : b * τ ^ 2 ≤ (1 : ℝ) / 256 := by
    have hbτ_sq_le_scaled : b * τ ^ 2 ≤ (c ^ 2 / 16) * τ ^ 2 :=
      mul_le_mul_of_nonneg_right hb_le_sixteenth (sq_nonneg τ)
    nlinarith only [hbτ_sq_le_scaled, hcτ_sq_le]
  have hacτ_sq_le : a * c * τ ^ 2 ≤ (1 : ℝ) / 32 := by
    -- acτ²=(aτ)(cτ)，用已经得到的两个非负上界相乘。
    have hproduct_le : (a * τ) * (c * τ) ≤ (1 / 8 : ℝ) * (1 / 4) :=
      mul_le_mul haτ_le hcτ_le_quarter hcτ_nonneg (by norm_num)
    nlinarith only [hproduct_le]
  have hbcτ_cube_nonneg : 0 ≤ b * c * τ ^ 3 := by positivity
  have hbcτ_cube_le : b * c * τ ^ 3 ≤ (1 : ℝ) / 1024 := by
    have hproduct_le : (b * τ ^ 2) * (c * τ) ≤ (1 / 256 : ℝ) * (1 / 4) :=
      mul_le_mul hbτ_sq_le hcτ_le_quarter hcτ_nonneg (by norm_num)
    nlinarith only [hproduct_le]

  -- A_R 下界保留 1-cτ；其余 aτ、(ac-b)τ²、bcτ³ 均非负。
  have hpositive_gap_scaled : 0 ≤ (a * c - b) * τ ^ 2 :=
    mul_nonneg hac_sub_b_nonneg (sq_nonneg τ)
  have hAR_lower : (3 : ℝ) / 4 ≤ polarCoeffAR a b c τ := by
    dsimp [polarCoeffAR]
    nlinarith only [haτ_nonneg, hpositive_gap_scaled, hbcτ_cube_nonneg, hcτ_le_quarter]
  have ha_sub_c_scaled_nonpos : (a - c) * τ ≤ 0 := by
    have ha_sub_c_nonpos : a - c ≤ 0 := by linarith only [ha_le_half, hc_pos]
    exact mul_nonpos_of_nonpos_of_nonneg ha_sub_c_nonpos hτ_pos.le
  have hAR_upper : polarCoeffAR a b c τ ≤ (5 : ℝ) / 4 := by
    dsimp [polarCoeffAR]
    -- 丢弃非正的 (a-c)τ 与 -bτ²，再用 1+1/32+1/1024≤5/4。
    nlinarith only [ha_sub_c_scaled_nonpos, hbτ_sq_nonneg, hacτ_sq_le, hbcτ_cube_le]

  have hcross_lower : 0 ≤ 1 - a * τ - b * τ ^ 2 := by
    nlinarith only [haτ_le, hbτ_sq_le]
  have hcross_upper : 1 - a * τ - b * τ ^ 2 ≤ 1 := by
    nlinarith only [haτ_nonneg, hbτ_sq_nonneg]

  -- G 和 b+ac 的估计回到未归一化的 c²；不需要吸收的正下界。
  have hac_nonneg : 0 ≤ a * c := mul_nonneg ha_nonneg hc_pos.le
  have hac_le : a * c ≤ c ^ 2 / 2 := by
    have hscaled_half : a * c ≤ (c / 2) * c :=
      mul_le_mul_of_nonneg_right ha_le_half hc_pos.le
    nlinarith only [hscaled_half]
  have hone_add_cτ_nonneg : 0 ≤ 1 + c * τ := by linarith only [hcτ_nonneg]
  have hone_add_cτ_le : 1 + c * τ ≤ (5 : ℝ) / 4 := by
    linarith only [hcτ_le_quarter]
  have hb_factor_le : b * (1 + c * τ) ≤ (c ^ 2 / 16) * (5 / 4) :=
    mul_le_mul hb_le_sixteenth hone_add_cτ_le hone_add_cτ_nonneg
      (div_nonneg (sq_nonneg c) (by norm_num))
  have hG_lower : 0 ≤ polarCoeffG a b c τ := by
    exact add_nonneg hac_nonneg (mul_nonneg hb_nonneg hone_add_cτ_nonneg)
  have hG_upper : polarCoeffG a b c τ ≤ (37 / 64 : ℝ) * c ^ 2 := by
    dsimp [polarCoeffG]
    -- c²/2+(c²/16)(5/4)=(37/64)c²，保留论文的精确常数。
    nlinarith only [hac_le, hb_factor_le]
  have hpotential_lower : 0 ≤ b + a * c := add_nonneg hb_nonneg hac_nonneg
  have hpotential_upper : b + a * c ≤ (9 / 16 : ℝ) * c ^ 2 := by
    nlinarith only [hb_le_sixteenth, hac_le]
  exact ⟨⟨hAR_lower, hAR_upper⟩, ⟨hcross_lower, hcross_upper⟩,
    ⟨hG_lower, hG_upper⟩, ⟨hpotential_lower, hpotential_upper⟩⟩

/-- 从 V7 (5.2)–(5.3) 的原始参数条件推出 (8.2) 全部四组系数界。
材料正参数保证阈值与时间尺度界可用；吸收只要求非负、各自不超过 S，
且 S≤c/4，保留 p=r=0、单向和双向吸收。
本入口调用 v0.2.1 的阈值等价及 (5.4) 推论，而不把 (8.2) 当作独立假设。
CP 在此仍只是正参数，尚未兑现空间 Poincaré 不等式；
本定理的输出将供后续二次型/空间能量估计使用。 -/
theorem polar_coefficients_bounds_of_threshold (ε κ τ μ CP p r S c : ℝ)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ) (hτ_pos : 0 < τ)
    (hμ_pos : 0 < μ) (hCP_pos : 0 < CP) (hc_pos : 0 < c)
    (hc_le_threshold : c ≤ threshold ε κ τ μ CP)
    (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (hp_le_S : p ≤ S) (hr_le_S : r ≤ S) (hS_le : S ≤ c / 4) :
    (3 / 4 ≤ polarCoeffAR (absorptionSum p r) (absorptionProduct p r) c τ ∧
      polarCoeffAR (absorptionSum p r) (absorptionProduct p r) c τ ≤ 5 / 4) ∧
      (0 ≤ 1 - absorptionSum p r * τ - absorptionProduct p r * τ ^ 2 ∧
        1 - absorptionSum p r * τ - absorptionProduct p r * τ ^ 2 ≤ 1) ∧
      (0 ≤ polarCoeffG (absorptionSum p r) (absorptionProduct p r) c τ ∧
        polarCoeffG (absorptionSum p r) (absorptionProduct p r) c τ ≤ (37 / 64) * c ^ 2) ∧
      (0 ≤ absorptionProduct p r + absorptionSum p r * c ∧
        absorptionProduct p r + absorptionSum p r * c ≤ (9 / 16) * c ^ 2) := by
  have ha_nonneg : 0 ≤ absorptionSum p r :=
    absorptionSum_nonneg p r hp_nonneg hr_nonneg
  have hb_nonneg : 0 ≤ absorptionProduct p r :=
    absorptionProduct_nonneg p r hp_nonneg hr_nonneg
  have ha_le_half : absorptionSum p r ≤ c / 2 :=
    absorptionSum_le_half p r S c hp_le_S hr_le_S hS_le
  have hb_le_sixteenth : absorptionProduct p r ≤ c ^ 2 / 16 :=
    absorptionProduct_le_c_sq_sixteenth p r S c hp_nonneg hr_nonneg hp_le_S hr_le_S hS_le
  have hac_sub_b_nonneg : 0 ≤ absorptionSum p r * c - absorptionProduct p r :=
    absorptionSum_mul_sub_product_nonneg p r c hp_nonneg hr_nonneg ha_le_half
  -- c_mul_tau_bounds 内部调用 le_threshold_iff_explicit，将论文阈值
  -- 转为 8cAτ≤κ，再推出 cτ≤κ/(8A)<1/16<1/4。
  have hcτ_le_quarter : c * τ ≤ (1 : ℝ) / 4 :=
    (c_mul_tau_bounds ε κ τ μ CP c
      hε_pos hκ_pos hτ_pos hμ_pos hCP_pos hc_pos hc_le_threshold).2.2.2
  exact polar_coefficients_bounds_of_local_conditions
    (absorptionSum p r) (absorptionProduct p r) c τ
    ha_nonneg hb_nonneg hc_pos hτ_pos ha_le_half hb_le_sixteenth
    hac_sub_b_nonneg hcτ_le_quarter

/-- 非零路径的全轴兼容：v=exampleU、R=exampleP、z=exampleQ，κ=τ=1。
复用 v0.1.3 的实际指数函数定义；这里只建立路径条件，随后调用一般求导定理。
这不是完整二维 PDE 解的声明。 -/
theorem example_polar_path_compatible (t : ℝ) :
    exampleQ t + (1 : ℝ) * LeanPML.Debye.exampleP t = (1 : ℝ) * exampleU t := by
  unfold exampleQ exampleU LeanPML.Debye.exampleP
  ring

/-- (7.4) 的非零光滑时间路径实例，a、b、c 任意，特别包含零、单向、双向吸收。
真实导数复用 v0.1.2、v0.1.3 的证据，再调用本文件的一般求导定理；
κ=τ=1，R(0)=-1，所以不是仅检验零函数。 -/
theorem hasDerivAt_example_polarEnergy (a b c t : ℝ) :
    HasDerivAt (polarEnergyAlong a b c 1 1 LeanPML.Debye.exampleP exampleQ)
      ((2 * LeanPML.Debye.exampleE t + a * LeanPML.Debye.exampleP t + b * exampleQ t) *
          (LeanPML.Debye.exampleE t + c * exampleU t) -
        polarRemainder a b c 1 1 (LeanPML.Debye.exampleP t) (exampleQ t)
          (2 * LeanPML.Debye.exampleE t)) t := by
  have hcompat_near :
      ∀ᶠ s in 𝓝 t, exampleQ s + (1 : ℝ) * LeanPML.Debye.exampleP s =
        (1 : ℝ) * exampleU s :=
    Filter.Eventually.of_forall example_polar_path_compatible
  exact hasDerivAt_polarEnergy a b c 1 1 exampleU LeanPML.Debye.exampleP exampleQ
    t (LeanPML.Debye.exampleE t) (2 * LeanPML.Debye.exampleE t)
    (by norm_num) (hasDerivAt_exampleU t) (LeanPML.Debye.hasDerivAt_exampleP t)
    (hasDerivAt_exampleQ t) hcompat_near

end LeanPML.PML
