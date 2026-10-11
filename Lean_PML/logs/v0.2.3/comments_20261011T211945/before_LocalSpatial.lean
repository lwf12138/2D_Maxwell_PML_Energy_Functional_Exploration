import LeanPML.PML.Weights
import LeanPML.Time.Constancy
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# V7 空间块的时间路径版本：正吸收与退化零区

来源：../results/V7_Maxwell_Debye_PML/V7_global_energy.md，(5.5)、(6.1)–(6.2)、
§7.1 的 (7.1)、紧接其后的未编号零区公式及 (7.2) 的点态被积式。

固定空间点和方向 i 后，si=σᵢ、sj=σⱼ、c 是时间不变的实数。
h、l 是真实时间函数，f 定义为 l-h；V 是某时刻由 HasDerivAt h V t 绑定的导数值。
纸面对应 h=∂ᵢv、l=Λᵢ、f=ψᵢ；本文件没有构造空间梯度或证明时间/空间微分交换。
x 方向取 (si,sj)=(p,r)，y 方向取 (r,p)，尤其 l²、h² 的耗散系数次序不同。

建议顺序：spatial_weight_balance → spatial_rate_identity →
hasDerivAt_spatialEnergy_pos → 零区兼容与零区公式 → 两分支合并及二维结论。
代数恒等式与真实求导分开：ring 仅整理导数值，不证明函数可导。
零区独立保留 c*h²；p=r=0 不自动给出 f=0，兼容必须另有证据。
本轮不作空间积分、Green/PEC、加权函数空间链式法则，也不删除 (V+c*h)*l。
-/

namespace LeanPML.PML

/-- V7 (7.1) 的单方向局部空间能量，含 1/2，不含空间积分。
用 (5.5) 已有的分支权重，f 直接定义为 l-h，避免独立辅助函数的兼容负担。
参数 c,si,sj 在时间上恒定；此定义没有断言 h 是真实空间梯度。 -/
noncomputable def spatialEnergy (c si sj : ℝ) (h l : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((l t) ^ 2 + energyWeightX c si sj * (l t - h t) ^ 2) / 2

/-- V7 (7.2) 的单方向点态耗散。
正区 l² 前取 si(c+si)/a，h² 前取 sj(c-sj)/a；后者调用时必须交换 si,sj。
零区独立取 c*h²，不能用分式的除零值替代。
物理范围 si,sj≥0 时 else 就是 a=0；范围外 a<0 的值仅是总函数约定。 -/
noncomputable def spatialDissipation (c si sj h l : ℝ) : ℝ :=
  if 0 < absorptionSum si sj then
    dissipationPlus c si sj * l ^ 2 + dissipationMinus c sj si * h ^ 2
  else c * h ^ 2

/-- V7 (6.2)、(7.1) 空间部分的两个时间分量之和。
x,y 分别显式使用已有 energyWeightX、energyWeightY；不包含空间积分。
后面的分解引理把它连接到交换 p,r 的两个单方向表达式。 -/
noncomputable def spatialEnergy2D (c p r : ℝ)
    (hx hy lx ly : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((lx t) ^ 2 + (ly t) ^ 2 +
    energyWeightX c p r * (lx t - hx t) ^ 2 +
    energyWeightY c p r * (ly t - hy t) ^ 2) / 2

/-- V7 (7.2) 的二维点态密度；这里只相加两个方向，不构造积分算子。
零区时该定义保留 c*(hx²+hy²)，其正式等式见下方零区定理。 -/
noncomputable def spatialDissipation2D (c p r hx hy lx ly : ℝ) : ℝ :=
  spatialDissipation c p r hx lx + spatialDissipation c r p hy ly

/-- V7 (7.1) 所用的权重平衡 sj+a*w=c。
这里只需 a>0；没有除以 si 或 sj。分母非零由正分支给出。
输出将用于空间块的代数恒等式。 -/
theorem spatial_weight_balance (c si sj : ℝ)
    (ha_pos : 0 < absorptionSum si sj) :
    sj + absorptionSum si sj * energyWeightX c si sj = c := by
  have ha_ne : absorptionSum si sj ≠ 0 := ne_of_gt ha_pos
  rw [energyWeightX, if_pos ha_pos]
  -- 分母 a 已证非零；约分后只需展开加减。
  field_simp [ha_ne]
  ring

/-- V7 (7.1) 第二行的实数代数恒等式。
h,l,V 在这里仅是数值；该引理不承担求导。a>0 使分母合法。
下方真实时间定理将调用它整理由乘积/平方法则得到的导数。 -/
theorem spatial_rate_identity (c si sj h l V : ℝ)
    (ha_pos : 0 < absorptionSum si sj) :
    l * V + (l + energyWeightX c si sj * (l - h)) * (sj * h - si * l) =
      (V + c * h) * l -
        (dissipationPlus c si sj * l ^ 2 + dissipationMinus c sj si * h ^ 2) := by
  have hbalance : sj + absorptionSum si sj * energyWeightX c si sj = c :=
    spatial_weight_balance c si sj ha_pos
  have ha_ne : absorptionSum si sj ≠ 0 := ne_of_gt ha_pos
  have ha_swapped : absorptionSum sj si = absorptionSum si sj := by
    simp only [absorptionSum, add_comm]
  have hweight_value :
      energyWeightX c si sj = (c - sj) / absorptionSum si sj := by
    -- 用前面已经证明的平衡式解出 w；乘分母的合法性来自 a≠0。
    apply (eq_div_iff ha_ne).2
    nlinarith [hbalance]
  rw [hweight_value]
  dsimp [dissipationPlus, dissipationMinus]
  rw [ha_swapped]
  -- 两个分式同分母 a≠0；消去分母后是普通多项式恒等式。
  field_simp [ha_ne]
  dsimp [absorptionSum]
  ring

/-- 由 V7 §7.1 辅助演化推出 f=l-h 的真实导数。
hh 绑定 h'=V，hl 绑定 l'=V+sj*h-si*l；相减后 V 抵消。
没有把 f' 当作独立输入。此结果供空间能量求导及零区保持使用。 -/
theorem hasDerivAt_spatialAuxiliary (si sj : ℝ) (h l : ℝ → ℝ) (t V : ℝ)
    (hh : HasDerivAt h V t)
    (hl : HasDerivAt l (V + sj * h t - si * l t) t) :
    HasDerivAt (fun s => l s - h s) (sj * h t - si * l t) t := by
  -- sub 是 mathlib 的真实差函数求导规则；ring 仅消去导数值中的 V。
  exact (hl.sub hh).congr_deriv (by ring)

/-- V7 (7.1) 正吸收分支的真实时间求导。
ha_pos 只用于权重与分式代数；hh、hl 是原始真实导数输入。
先由 f=l-h 求 f'，再平方求导、常数乘法、相加并除以 2。
输出保留 (V+c*h)*l，尚未使用任何空间积分或边界条件。 -/
theorem hasDerivAt_spatialEnergy_pos (c si sj : ℝ)
    (h l : ℝ → ℝ) (t V : ℝ)
    (ha_pos : 0 < absorptionSum si sj)
    (hh : HasDerivAt h V t)
    (hl : HasDerivAt l (V + sj * h t - si * l t) t) :
    HasDerivAt (spatialEnergy c si sj h l)
      ((V + c * h t) * l t -
        (dissipationPlus c si sj * (l t) ^ 2 +
          dissipationMinus c sj si * (h t) ^ 2)) t := by
  have hf : HasDerivAt (fun s => l s - h s) (sj * h t - si * l t) t :=
    hasDerivAt_spatialAuxiliary si sj h l t V hh hl
  have hl_square : HasDerivAt (fun s => (l s) ^ 2)
      (2 * l t * (V + sj * h t - si * l t)) t := by
    exact (hl.pow 2).congr_deriv (by ring)
  have hf_square : HasDerivAt (fun s => (l s - h s) ^ 2)
      (2 * (l t - h t) * (sj * h t - si * l t)) t := by
    exact (hf.pow 2).congr_deriv (by ring)
  have hweighted_square : HasDerivAt
      (fun s => energyWeightX c si sj * (l s - h s) ^ 2)
      (energyWeightX c si sj * (2 * (l t - h t) * (sj * h t - si * l t))) t :=
    hf_square.const_mul (energyWeightX c si sj)
  have henergy_rule : HasDerivAt (spatialEnergy c si sj h l)
      ((2 * l t * (V + sj * h t - si * l t) +
        energyWeightX c si sj * (2 * (l t - h t) * (sj * h t - si * l t))) / 2) t :=
    (hl_square.add hweighted_square).div_const 2
  apply henergy_rule.congr_deriv
  -- 微积分已完成；现在先整理为 (7.1) 第一行，再调用代数层。
  calc
    (2 * l t * (V + sj * h t - si * l t) +
        energyWeightX c si sj * (2 * (l t - h t) * (sj * h t - si * l t))) / 2 =
        l t * V + (l t + energyWeightX c si sj * (l t - h t)) *
          (sj * h t - si * l t) := by ring
    _ = _ := spatial_rate_identity c si sj (h t) (l t) V ha_pos

/-- V7 (7.1) 后零区公式的单方向时间分量版本。
只需真实 h'=V；直接平方求导得到 h*V，再写成 (V+c*h)*h-c*h²。
此时 c*h² 不能因吸收为零而删掉；这仍不声称 h 已是空间梯度。 -/
theorem hasDerivAt_zeroSpatialComponent (c : ℝ) (h : ℝ → ℝ) (t V : ℝ)
    (hh : HasDerivAt h V t) :
    HasDerivAt (fun s => (h s) ^ 2 / 2)
      ((V + c * h t) * h t - c * (h t) ^ 2) t := by
  -- pow 和 div_const 给出真实导数；ring 只改写为论文中的平衡形式。
  exact ((hh.pow 2).div_const 2).congr_deriv (by ring)

/-- V7 (7.1) 后未编号零区公式的二维时间版本。
输入两个方向真实 hᵢ'=Vᵢ，不要求端点或空间微分；相加后保留 c*(hx²+hy²)。
下游将把 hᵢ 与实际空间梯度连接，目前这个接口仍未兑现。 -/
theorem hasDerivAt_zeroSpatial2D (c : ℝ) (hx hy : ℝ → ℝ)
    (t Vx Vy : ℝ)
    (hhx : HasDerivAt hx Vx t) (hhy : HasDerivAt hy Vy t) :
    HasDerivAt (fun s => ((hx s) ^ 2 + (hy s) ^ 2) / 2)
      ((Vx + c * hx t) * hx t + (Vy + c * hy t) * hy t -
        c * ((hx t) ^ 2 + (hy t) ^ 2)) t := by
  have hx_energy := hasDerivAt_zeroSpatialComponent c hx t Vx hhx
  have hy_energy := hasDerivAt_zeroSpatialComponent c hy t Vy hhy
  have hsum : HasDerivAt (fun s => (hx s) ^ 2 / 2 + (hy s) ^ 2 / 2)
      (((Vx + c * hx t) * hx t - c * (hx t) ^ 2) +
        ((Vy + c * hy t) * hy t - c * (hy t) ^ 2)) t :=
    hx_energy.add hy_energy
  -- 函数上把两项 /2 合并；导数值的相加用 ring 整理。
  have hfunction : (fun s => (hx s) ^ 2 / 2 + (hy s) ^ 2 / 2) =
      (fun s => ((hx s) ^ 2 + (hy s) ^ 2) / 2) := by
    funext s
    ring
  change HasDerivAt (fun s => (hx s) ^ 2 / 2 + (hy s) ^ 2 / 2) _ t at hsum
  rw [hfunction] at hsum
  exact hsum.congr_deriv (by ring)

/-- V7 零区兼容 l=h 的时间保持；这是 §7.1 使用 f=0 的一种点态时间证书。
非负 si,sj 与 a=0 先推出 si=sj=0；真实演化给出 (l-h)'=0。
闭区间连续及内部导数足以保持初值，包括 T=0；只输入初始 l(0)=h(0)，
而不是预设整个区间已经相等。不涉及磁不变量或原 PDE 的提升构造。 -/
theorem zeroSpatial_compatibility_preserved (si sj T : ℝ) (h l : ℝ → ℝ)
    (hsi_nonneg : 0 ≤ si) (hsj_nonneg : 0 ≤ sj)
    (ha_zero : absorptionSum si sj = 0) (hT_nonneg : 0 ≤ T)
    (hh_cont : ContinuousOn h (Set.Icc 0 T))
    (hl_cont : ContinuousOn l (Set.Icc 0 T))
    (hODE : ∀ t ∈ Set.Ioo 0 T, ∃ V : ℝ,
      HasDerivAt h V t ∧ HasDerivAt l (V + sj * h t - si * l t) t)
    (hinitial : l 0 = h 0) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    l t = h t := by
  have habsorption_zero : si = 0 ∧ sj = 0 :=
    (absorptionSum_eq_zero_iff si sj hsi_nonneg hsj_nonneg).mp ha_zero
  have hf_cont : ContinuousOn (fun s => l s - h s) (Set.Icc 0 T) :=
    hl_cont.sub hh_cont
  have hf_deriv : ∀ s ∈ Set.Ioo 0 T, HasDerivAt (fun s => l s - h s) 0 s := by
    intro s hs
    obtain ⟨V, hh, hl⟩ := hODE s hs
    have hf := hasDerivAt_spatialAuxiliary si sj h l s V hh hl
    simpa only [habsorption_zero.1, habsorption_zero.2, zero_mul, sub_self] using hf
  have hf_initial : l t - h t = l 0 - h 0 :=
    Time.eq_initial_of_hasDerivAt_zero (fun s => l s - h s) T hT_nonneg
      hf_cont hf_deriv ht
  -- 初始兼容在这里才使用；先验 a=0 单独不足以推出 f=0。
  rw [hinitial, sub_self] at hf_initial
  exact sub_eq_zero.mp hf_initial

/-- V7 零区局部空间密度的真实时间求导：从非负吸收与 a=0 推出 si=sj=0，
并显式输入当前时刻的兼容 l(t)=h(t)。权重在整个时间路径上恒为零，
所以只需对 l²/2 求导；没有对单点兼容等式求导。
未来若需区间兼容，应调用上面的保持定理或完整 PDE 的兼容保持。 -/
theorem hasDerivAt_spatialEnergy_zero (c si sj : ℝ)
    (h l : ℝ → ℝ) (t V : ℝ)
    (hsi_nonneg : 0 ≤ si) (hsj_nonneg : 0 ≤ sj)
    (ha_zero : absorptionSum si sj = 0)
    (hl : HasDerivAt l (V + sj * h t - si * l t) t)
    (hcompat : l t = h t) :
    HasDerivAt (spatialEnergy c si sj h l)
      ((V + c * h t) * l t - c * (h t) ^ 2) t := by
  have habsorption_zero : si = 0 ∧ sj = 0 :=
    (absorptionSum_eq_zero_iff si sj hsi_nonneg hsj_nonneg).mp ha_zero
  have hl_deriv : HasDerivAt l V t := by
    simpa only [habsorption_zero.1, habsorption_zero.2, zero_mul, add_zero, sub_zero] using hl
  have hzero_weight : energyWeightX c si sj = 0 :=
    (weights_of_sum_zero c si sj ha_zero).1
  have hl_energy := hasDerivAt_zeroSpatialComponent c l t V hl_deriv
  have hfunction : spatialEnergy c si sj h l = (fun s => (l s) ^ 2 / 2) := by
    funext s
    simp only [spatialEnergy, hzero_weight, zero_mul, add_zero]
  rw [hfunction]
  apply hl_energy.congr_deriv
  rw [hcompat]

/-- V7 (7.1) 的两分支统一真实时间版本。
物理非负性使 a≤0 分支实际为 a=0；正分支无须零区兼容。
零分支的 hzero 明确记录 l=h 的来源要求，不能从 p=r=0 自动推定。
输出完整保留耦合项；不声称本块能量已经单调。 -/
theorem hasDerivAt_spatialEnergy (c si sj : ℝ) (h l : ℝ → ℝ) (t V : ℝ)
    (hsi_nonneg : 0 ≤ si) (hsj_nonneg : 0 ≤ sj)
    (hh : HasDerivAt h V t)
    (hl : HasDerivAt l (V + sj * h t - si * l t) t)
    (hzero : absorptionSum si sj = 0 → l t = h t) :
    HasDerivAt (spatialEnergy c si sj h l)
      ((V + c * h t) * l t - spatialDissipation c si sj (h t) (l t)) t := by
  by_cases ha_pos : 0 < absorptionSum si sj
  · -- 正区调用真实求导定理，再展开耗散的正分支。
    simpa only [spatialDissipation, if_pos ha_pos] using
      hasDerivAt_spatialEnergy_pos c si sj h l t V ha_pos hh hl
  · have ha_zero : absorptionSum si sj = 0 :=
      le_antisymm (le_of_not_gt ha_pos)
        (absorptionSum_nonneg si sj hsi_nonneg hsj_nonneg)
    have hcompat : l t = h t := hzero ha_zero
    simpa only [spatialDissipation, if_neg ha_pos] using
      hasDerivAt_spatialEnergy_zero c si sj h l t V
        hsi_nonneg hsj_nonneg ha_zero hl hcompat

/-- V7 (7.2) 的单方向点态耗散非负，由 (5.3) 幅度限制推出。
c>0 和非负吸收用于符号；si,sj≤S≤c/4 保证交叉系数 c-sj≥0。
调用 v0.2.1 已证分式系数界，而不是把耗散非负写成输入。
该结论仅为点态密度性质，没有证明可测、可积或积分能量定理。 -/
theorem spatialDissipation_nonneg (c si sj S h l : ℝ)
    (hc_pos : 0 < c) (hsi_nonneg : 0 ≤ si) (hsj_nonneg : 0 ≤ sj)
    (hsi_le_S : si ≤ S) (hsj_le_S : sj ≤ S) (hS_le : S ≤ c / 4) :
    0 ≤ spatialDissipation c si sj h l := by
  by_cases ha_pos : 0 < absorptionSum si sj
  · have ha_swapped_pos : 0 < absorptionSum sj si := by
      simpa only [absorptionSum, add_comm] using ha_pos
    have hsj_le_c : sj ≤ c := by
      have hsj_le_quarter : sj ≤ c / 4 := hsj_le_S.trans hS_le
      linarith
    have hplus_nonneg : 0 ≤ dissipationPlus c si sj :=
      (dissipationPlus_bounds c si sj S hc_pos.le hsi_nonneg hsj_nonneg
        ha_pos hsi_le_S).1
    have hminus_nonneg : 0 ≤ dissipationMinus c sj si :=
      (dissipationMinus_bounds c sj si hsj_nonneg hsi_nonneg
        hsj_le_c ha_swapped_pos).1
    rw [spatialDissipation, if_pos ha_pos]
    exact add_nonneg (mul_nonneg hplus_nonneg (sq_nonneg l))
      (mul_nonneg hminus_nonneg (sq_nonneg h))
  · -- 独立零区密度 c*h² 也非负，不能用分式的零值取代。
    rw [spatialDissipation, if_neg ha_pos]
    exact mul_nonneg hc_pos.le (sq_nonneg h)

/-- V7 (7.2) 的二维点态耗散非负。
y 分量调用单方向定理时交换 p,r 及其假设，从而保留正确的系数次序。
空间积分的非负性仍需可测性、可积性等后续接口。 -/
theorem spatialDissipation2D_nonneg (c p r S hx hy lx ly : ℝ)
    (hc_pos : 0 < c) (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (hp_le_S : p ≤ S) (hr_le_S : r ≤ S) (hS_le : S ≤ c / 4) :
    0 ≤ spatialDissipation2D c p r hx hy lx ly := by
  have hx_nonneg : 0 ≤ spatialDissipation c p r hx lx :=
    spatialDissipation_nonneg c p r S hx lx
      hc_pos hp_nonneg hr_nonneg hp_le_S hr_le_S hS_le
  have hy_nonneg : 0 ≤ spatialDissipation c r p hy ly :=
    spatialDissipation_nonneg c r p S hy ly
      hc_pos hr_nonneg hp_nonneg hr_le_S hp_le_S hS_le
  exact add_nonneg hx_nonneg hy_nonneg

/-- V7 (7.2) 零区的二维点态密度恰为 c*(hx²+hy²)。
只需分支等式 a=0；这里没有约分，c 可以是任意实数。
这是零区实例和以后积分分区需要的明确公式。 -/
theorem spatialDissipation2D_of_sum_zero (c p r hx hy lx ly : ℝ)
    (ha_zero : absorptionSum p r = 0) :
    spatialDissipation2D c p r hx hy lx ly = c * (hx ^ 2 + hy ^ 2) := by
  have ha_swapped_zero : absorptionSum r p = 0 := by
    simpa only [absorptionSum, add_comm] using ha_zero
  simp only [spatialDissipation2D, spatialDissipation, ha_zero, ha_swapped_zero,
    lt_self_iff_false, ↓reduceIte]
  ring

/-- 由 V7 (5.5) 推出的方向映射：交换 p,r 的 x 权重就是原来的 y 权重。
两分支同时成立；这里不是新增权重定义。下方二维能量分解实际调用此等式。 -/
theorem energyWeightX_swap (c p r : ℝ) :
    energyWeightX c r p = energyWeightY c p r := by
  simp only [energyWeightX, energyWeightY, absorptionSum, add_comm]

/-- V7 (6.2) 空间密度的方向分解：二维能量等于 x 分量加交换 p,r 的 y 分量。
用上一条权重映射核对方向，再由 ring 合并 1/2 因子；不涉及求导。
下方二维真实时间定理通过此函数等式复用单方向求导。 -/
theorem spatialEnergy2D_eq_sum (c p r : ℝ) (hx hy lx ly : ℝ → ℝ) :
    spatialEnergy2D c p r hx hy lx ly =
      (fun t => spatialEnergy c p r hx lx t + spatialEnergy c r p hy ly t) := by
  funext t
  dsimp [spatialEnergy2D, spatialEnergy]
  rw [energyWeightX_swap c p r]
  ring

/-- V7 (7.1) 的二维两分支真实时间结论，同时覆盖零区、两种边层和角层。
四个 HasDerivAt 把 Vx,Vy 及辅助演化绑定到实际函数；参数只需非负吸收。
hzero 仅在 a=0 时要求当前兼容，不预设完整区间兼容。
输出保留两个 (Vᵢ+c*hᵢ)*lᵢ，尚未完成实际梯度、空间积分或 Green/PEC。 -/
theorem hasDerivAt_spatialEnergy2D (c p r : ℝ)
    (hx hy lx ly : ℝ → ℝ) (t Vx Vy : ℝ)
    (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (hhx : HasDerivAt hx Vx t)
    (hlx : HasDerivAt lx (Vx + r * hx t - p * lx t) t)
    (hhy : HasDerivAt hy Vy t)
    (hly : HasDerivAt ly (Vy + p * hy t - r * ly t) t)
    (hzero : absorptionSum p r = 0 → lx t = hx t ∧ ly t = hy t) :
    HasDerivAt (spatialEnergy2D c p r hx hy lx ly)
      ((Vx + c * hx t) * lx t + (Vy + c * hy t) * ly t -
        spatialDissipation2D c p r (hx t) (hy t) (lx t) (ly t)) t := by
  have hx_zero : absorptionSum p r = 0 → lx t = hx t :=
    fun ha_zero => (hzero ha_zero).1
  have hy_zero : absorptionSum r p = 0 → ly t = hy t := by
    intro ha_swapped_zero
    have ha_zero : absorptionSum p r = 0 := by
      simpa only [absorptionSum, add_comm] using ha_swapped_zero
    exact (hzero ha_zero).2
  have hx_energy := hasDerivAt_spatialEnergy c p r hx lx t Vx
    hp_nonneg hr_nonneg hhx hlx hx_zero
  have hy_energy := hasDerivAt_spatialEnergy c r p hy ly t Vy
    hr_nonneg hp_nonneg hhy hly hy_zero
  -- add 来自真实函数的和求导规则；最后只把两个减法合并。
  rw [spatialEnergy2D_eq_sum]
  apply (hx_energy.add hy_energy).congr_deriv
  dsimp [spatialDissipation2D]
  ring

/-!
## 四分支与非零真实时间路径

下面取 c=4、S=1，只检验 (5.3) 的吸收幅度限制和 (7.1)–(7.2) 的局部结论。
这些数值并不声称对任意材料满足全部 (5.2) 阈值。x、y 边层分别计算，
以检查“l² 用本方向吸收、h² 用另一方向吸收”的次序。
-/

/-- V7 (7.2) 的零吸收点态实例：p=r=0 时两个方向仍保留 4hᵢ²。
输入 h、l 的数值任意；非负性调用一般定理，不以分式除零来替代零区公式。
注意本结论只计算耗散密度，不从 p=r=0 推出 l=h。 -/
theorem spatial_zero_absorption_example (hx hy lx ly : ℝ) :
    spatialDissipation2D 4 0 0 hx hy lx ly = 4 * hx ^ 2 + 4 * hy ^ 2 ∧
    0 ≤ spatialDissipation2D 4 0 0 hx hy lx ly := by
  have h_density_nonneg : 0 ≤ spatialDissipation2D 4 0 0 hx hy lx ly :=
    spatialDissipation2D_nonneg 4 0 0 1 hx hy lx ly
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  constructor
  · calc
      spatialDissipation2D 4 0 0 hx hy lx ly = 4 * (hx ^ 2 + hy ^ 2) :=
        spatialDissipation2D_of_sum_zero 4 0 0 hx hy lx ly
          (by norm_num [absorptionSum])
      _ = 4 * hx ^ 2 + 4 * hy ^ 2 := by ring
  · exact h_density_nonneg

/-- V7 (7.2) 的 x 边层实例：p=1>0、r=0、S=1=c/4。
x 方向留下 5lₓ²，y 方向留下 3hᵧ²，显示两个方向不能用同一个系数顺序。
非负性来自一般点态定理，数值化简只核对精确展开。 -/
theorem spatial_x_layer_example (hx hy lx ly : ℝ) :
    spatialDissipation2D 4 1 0 hx hy lx ly = 5 * lx ^ 2 + 3 * hy ^ 2 ∧
    0 ≤ spatialDissipation2D 4 1 0 hx hy lx ly := by
  have h_x_nonneg : 0 ≤ spatialDissipation 4 1 0 hx lx :=
    spatialDissipation_nonneg 4 1 0 1 hx lx
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have h_y_nonneg : 0 ≤ spatialDissipation 4 0 1 hy ly :=
    spatialDissipation_nonneg 4 0 1 1 hy ly
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  constructor
  · norm_num [spatialDissipation2D, spatialDissipation,
      dissipationPlus, dissipationMinus, absorptionSum]
  · exact add_nonneg h_x_nonneg h_y_nonneg

/-- V7 (7.2) 的 y 边层实例：p=0、r=1>0，幅度条件同上。
此时精确留下 3hₓ²+5lᵧ²；与上一条交换 x、y，核验非对称边层没有漏项。 -/
theorem spatial_y_layer_example (hx hy lx ly : ℝ) :
    spatialDissipation2D 4 0 1 hx hy lx ly = 3 * hx ^ 2 + 5 * ly ^ 2 ∧
    0 ≤ spatialDissipation2D 4 0 1 hx hy lx ly := by
  have h_x_nonneg : 0 ≤ spatialDissipation 4 0 1 hx lx :=
    spatialDissipation_nonneg 4 0 1 1 hx lx
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have h_y_nonneg : 0 ≤ spatialDissipation 4 1 0 hy ly :=
    spatialDissipation_nonneg 4 1 0 1 hy ly
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  constructor
  · norm_num [spatialDissipation2D, spatialDissipation,
      dissipationPlus, dissipationMinus, absorptionSum]
  · exact add_nonneg h_x_nonneg h_y_nonneg

/-- V7 (7.2) 的角层实例：p=r=1>0，S=1=c/4。
两方向分别具有 5/2 的 l² 系数和 3/2 的 h² 系数；一般定理同时给出非负性。
它补足双向吸收，但不替代前两条非对称方向检查。 -/
theorem spatial_corner_example (hx hy lx ly : ℝ) :
    spatialDissipation2D 4 1 1 hx hy lx ly =
      (5 / 2 : ℝ) * (lx ^ 2 + ly ^ 2) + (3 / 2 : ℝ) * (hx ^ 2 + hy ^ 2) ∧
    0 ≤ spatialDissipation2D 4 1 1 hx hy lx ly := by
  have h_x_nonneg : 0 ≤ spatialDissipation 4 1 1 hx lx :=
    spatialDissipation_nonneg 4 1 1 1 hx lx
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have h_y_nonneg : 0 ≤ spatialDissipation 4 1 1 hy ly :=
    spatialDissipation_nonneg 4 1 1 1 hy ly
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  constructor
  · norm_num [spatialDissipation2D, spatialDissipation,
      dissipationPlus, dissipationMinus, absorptionSum]
    ring
  · exact add_nonneg h_x_nonneg h_y_nonneg

/-- 为检验 V7 (7.1) 构造的非零时间路径 l(t)=exp(-t)。
与 h(t)=0、σᵢ=1、σⱼ=0 搭配，辅助方程为 l'=-l。
这是时间路径实例的定义，不是完整二维 PDE 解。 -/
noncomputable def spatialDecayPath (t : ℝ) : ℝ := Real.exp (-t)

/-- 指数路径的真实导数。由 mathlib 的恒等函数、取负和 exp 求导规则构造；
ring 只把链式法则产生的 exp(-t)·(-1) 整理为 -exp(-t)。 -/
theorem hasDerivAt_spatialDecayPath (t : ℝ) :
    HasDerivAt spatialDecayPath (-spatialDecayPath t) t := by
  have h_exponent : HasDerivAt (fun s : ℝ => -s) (-1) t :=
    (hasDerivAt_id t).neg
  have h_exp := h_exponent.exp
  exact h_exp.congr_deriv (by dsimp [spatialDecayPath]; ring)

/-- V7 (7.1) 的非零正吸收路径调用：h=0、l=exp(-t)，c=4、σᵢ=1、σⱼ=0。
先明确验证 h'=0 与 l'=0+σⱼh-σᵢl，再调用一般真实求导定理。
结果为 F_sp'=-5 exp(-t)²；这个实例不承担空间梯度或 PDE 接口。 -/
theorem hasDerivAt_spatial_positive_path (t : ℝ) :
    HasDerivAt (spatialEnergy 4 1 0 (fun _ => 0) spatialDecayPath)
      (-5 * (spatialDecayPath t) ^ 2) t := by
  have h_h : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t :=
    hasDerivAt_const t 0
  have h_l : HasDerivAt spatialDecayPath
      (0 + 0 * (0 : ℝ) - 1 * spatialDecayPath t) t := by
    simpa using hasDerivAt_spatialDecayPath t
  have h_local := hasDerivAt_spatialEnergy 4 1 0
    (fun _ => 0) spatialDecayPath t 0 (by norm_num) (by norm_num) h_h h_l
    (by norm_num [absorptionSum])
  -- 求导已经完成；展开已证明的分支密度，把输出整理为本例的数值系数。
  apply h_local.congr_deriv
  norm_num [spatialDissipation, dissipationPlus, dissipationMinus, absorptionSum]

/-- 正吸收实例确实不是零路径：l(0)=1，局部能量 F_sp(0)=5/2。
这里只核对初值；随时间可导的核心证据是上一条一般定理的调用。 -/
theorem spatial_positive_path_initial :
    spatialDecayPath 0 = 1 ∧
    spatialEnergy 4 1 0 (fun _ => 0) spatialDecayPath 0 = (5 / 2 : ℝ) := by
  norm_num [spatialDecayPath, spatialEnergy, energyWeightX, absorptionSum]

/-- 零区的非零路径 h(t)=l(t)=t+1，显式满足零辅助量 f=l-h=0。
该条件由路径的定义保证，不能从 σᵢ=σⱼ=0 单独推出。 -/
def spatialLinearPath (t : ℝ) : ℝ := t + 1

/-- 上述零区路径的真实导数为 1。mathlib 的 add_const 表达常数项导数为零，
保留原来的恒等函数导数；后面用它验证两个方向的辅助演化。 -/
theorem hasDerivAt_spatialLinearPath (t : ℝ) :
    HasDerivAt spatialLinearPath 1 t := by
  exact (hasDerivAt_id t).add_const 1

/-- V7 (7.1) 后零区公式的非零二维时间路径实例：
两方向均取 h=l=t+1，p=r=0，c=4。
调用一般二维分支求导定理；全程保留零区耗散，它与移位乘积中的相应项抵消。
结论仅是时间分量能量导数 2(t+1)，不把这些路径命名为实际空间梯度。 -/
theorem hasDerivAt_spatial_zero_path (t : ℝ) :
    HasDerivAt
      (spatialEnergy2D 4 0 0 spatialLinearPath spatialLinearPath
        spatialLinearPath spatialLinearPath) (2 * (t + 1)) t := by
  have h_path : HasDerivAt spatialLinearPath 1 t :=
    hasDerivAt_spatialLinearPath t
  have h_aux : HasDerivAt spatialLinearPath
      (1 + 0 * spatialLinearPath t - 0 * spatialLinearPath t) t := by
    simpa using h_path
  have h_two := hasDerivAt_spatialEnergy2D 4 0 0
    spatialLinearPath spatialLinearPath spatialLinearPath spatialLinearPath t 1 1
    (by norm_num) (by norm_num) h_path h_aux h_path h_aux
    (fun _ => ⟨rfl, rfl⟩)
  -- 一般二维求导已经保留并相加两个方向；这里仅整理本例的导数值。
  apply h_two.congr_deriv
  norm_num [spatialDissipation2D, spatialDissipation, absorptionSum, spatialLinearPath]
  ring

/-- 零区时间路径的初值：每个分量等于 1，二维能量也等于 1。
说明“零吸收且零辅助量”并不要求梯度分量路径为零。 -/
theorem spatial_zero_path_initial :
    spatialLinearPath 0 = 1 ∧
    spatialEnergy2D 4 0 0 spatialLinearPath spatialLinearPath
      spatialLinearPath spatialLinearPath 0 = 1 := by
  norm_num [spatialLinearPath, spatialEnergy2D, spatialEnergy, energyWeightX, absorptionSum]

end LeanPML.PML
