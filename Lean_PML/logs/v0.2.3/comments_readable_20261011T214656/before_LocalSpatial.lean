import LeanPML.PML.Weights
import LeanPML.Time.Constancy
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# 空间块与零吸收区：V7 的真实时间路径版本

PDF 页码：p.8 (5.5) 权重与零区保持；p.9 (6.1)–(6.2)；p.10 (7.1) 与零区式；p.11 (7.2)。
符号：a=si+sj，h↔∂ᵢv，l↔Λᵢ，f=l−h；x 方向 (si,sj)=(p,r)，y 方向为 (r,p)。
HasDerivAt h V t 表示 h 在 t 处的真实导数为 V。系数仅在时间上固定。
F_sp、D_sp 是局部密度；实际梯度、混合微分交换和空间积分尚未实现。
零区不能删去 ch²，且吸收为零不自动推出 f=0；需另有兼容证据。

先读正区求导 → 零区兼容保持 → 二维合并。详细推导见 docs/v0.2.3_reading_guide.md。
-/

namespace LeanPML.PML

/-- PDF p.8 (5.5)、p.10 (7.1)：F_sp,i = [l²+wᵢ(l−h)²]/2。
wᵢ=(c−σⱼ)/a（a>0），零区取 0；这里只定义时间路径的局部密度。 -/
noncomputable def spatialEnergy (c si sj : ℝ) (h l : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((l t) ^ 2 + energyWeightX c si sj * (l t - h t) ^ 2) / 2

/-- PDF p.11 (7.2) 的单方向密度：
D_sp,i = σᵢ(c+σᵢ)l²/a + σⱼ(c−σⱼ)h²/a（a>0）；零区为 ch²。
注意 h² 系数调用 dissipationMinus c sj si；物理范围外 a<0 的 else 仅为总函数约定。 -/
noncomputable def spatialDissipation (c si sj h l : ℝ) : ℝ :=
  if 0 < absorptionSum si sj then
    dissipationPlus c si sj * l ^ 2 + dissipationMinus c sj si * h ^ 2
  else c * h ^ 2

/-- PDF p.9 (6.1)–(6.2)：Λ=∇v+ψ，空间密度为 ½(|Λ|²+Σᵢwᵢψᵢ²)。
此处 ψᵢ=lᵢ−hᵢ，显式使用 wₓ、wᵧ；不含 μ 因子或空间积分。 -/
noncomputable def spatialEnergy2D (c p r : ℝ)
    (hx hy lx ly : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((lx t) ^ 2 + (ly t) ^ 2 +
    energyWeightX c p r * (lx t - hx t) ^ 2 +
    energyWeightY c p r * (ly t - hy t) ^ 2) / 2

/-- PDF p.11 (7.2)：𝒮[U]=∫_{Ω₊}Σᵢ[σᵢ(c+σᵢ)Λᵢ²/a+σⱼ(c−σⱼ)(∂ᵢv)²/a]
+ ∫_Z c|∇v|²（两积分均对 dx dy）。
这里只定义点态 D_sp=D_sp,x+D_sp,y；y 方向交换 p,r，零区保留 c(hₓ²+hᵧ²)。 -/
noncomputable def spatialDissipation2D (c p r hx hy lx ly : ℝ) : ℝ :=
  spatialDissipation c p r hx lx + spatialDissipation c r p hy ly

/-- PDF p.10，(7.1) 后：σⱼ+awᵢ=c。
a>0 保证分母非零；供下一个代数引理使用。 -/
theorem spatial_weight_balance (c si sj : ℝ)
    (ha_pos : 0 < absorptionSum si sj) :
    sj + absorptionSum si sj * energyWeightX c si sj = c := by
  have ha_ne : absorptionSum si sj ≠ 0 := ne_of_gt ha_pos
  rw [energyWeightX, if_pos ha_pos]
  -- 分母 a 已证非零；约分后只需展开加减。
  field_simp [ha_ne]
  ring

/-- PDF p.10 (7.1) 的代数部分：
lV+(l+wᵢ(l−h))(σⱼh−σᵢl)=(V+ch)l−σᵢ(c+σᵢ)l²/a−σⱼ(c−σⱼ)h²/a。
这里只处理数值；a>0 用于消分母，真实求导在后面的定理中完成。 -/
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

/-- PDF p.10 §7.1：f=l−h，fₜ=σⱼh−σᵢl，lₜ=V+σⱼh−σᵢl。
由 hh : h′=V 与 hl 的真实导数证据相减，得到 f′，不把 f′ 预设为输入。 -/
theorem hasDerivAt_spatialAuxiliary (si sj : ℝ) (h l : ℝ → ℝ) (t V : ℝ)
    (hh : HasDerivAt h V t)
    (hl : HasDerivAt l (V + sj * h t - si * l t) t) :
    HasDerivAt (fun s => l s - h s) (sj * h t - si * l t) t := by
  -- sub 是 mathlib 的真实差函数求导规则；ring 仅消去导数值中的 V。
  exact (hl.sub hh).congr_deriv (by ring)

/-- PDF p.10 (7.1)，a>0：
½∂ₜ(l²+wᵢf²)=lV+(l+wᵢ(l−h))(σⱼh−σᵢl)
             =(V+ch)l−σᵢ(c+σᵢ)l²/a−σⱼ(c−σⱼ)h²/a。
hh、hl 提供真实导数；先求差与平方的导数，再调用代数引理。 -/
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

/-- PDF p.10 零区未编号式的单分量版本：d(h²/2)/dt=(V+ch)h−ch²。
只需真实 h′=V；接回分支能量时，l=h 由后续定理显式输入。 -/
theorem hasDerivAt_zeroSpatialComponent (c : ℝ) (h : ℝ → ℝ) (t V : ℝ)
    (hh : HasDerivAt h V t) :
    HasDerivAt (fun s => (h s) ^ 2 / 2)
      ((V + c * h t) * h t - c * (h t) ^ 2) t := by
  -- pow 和 div_const 给出真实导数；ring 只改写为论文中的平衡形式。
  exact ((hh.pow 2).div_const 2).congr_deriv (by ring)

/-- PDF p.10 零区原式：½∂ₜ|∇v|²=(∇vₜ+c∇v)·∇v−c|∇v|²。
此处证明时间版本：d[(hₓ²+hᵧ²)/2]/dt=(Vₓ+chₓ)hₓ+(Vᵧ+chᵧ)hᵧ−c(hₓ²+hᵧ²)。
hhx、hhy 绑定真实导数；实际空间梯度接口未实现。 -/
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

/-- PDF p.8 §5.2 零区保持句的时间版本：f′=0、f(0)=0 ⇒ f(t)=0，即 l(t)=h(t)。
非负吸收与 a=0 推出 σᵢ=σⱼ=0；闭区间连续、内部真实演化保证保持初值。
只输入初始兼容，包含 T=0，不要求端点双侧导数。 -/
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

/-- PDF p.10 零区公式：F_sp,i′=(V+ch)l−ch²。
a=0 使整个能量函数为 l²/2；先对 l 求导，再用当前 l(t)=h(t) 改写导数值。
没有对单点兼容等式求导；区间兼容可由上面的保持定理提供。 -/
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

/-- 合并 PDF p.10 正区 (7.1) 与零区式：F_sp,i′=(V+ch)l−D_sp,i。
输入真实导数和非负吸收；hzero 只在 a=0 时要求 l(t)=h(t)。
保留耦合项，不能据此声称本块单调。 -/
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

/-- 由 PDF (5.3)、(7.2) 推出：c>0、0≤σᵢ,σⱼ≤S≤c/4 ⇒ D_sp,i≥0。
正区复用分式系数非负，零区用 ch²≥0；不涉及空间积分。 -/
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

/-- PDF (7.2) 的点态推论：D_sp,x≥0、D_sp,y≥0 ⇒ D_sp≥0。
y 分量交换 p,r；输入 c>0、0≤p,r≤S≤c/4，无吸收正下界。 -/
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

/-- PDF (7.2) 零区被积式：a=0 ⇒ D_sp=c(hₓ²+hᵧ²)。
这里只化简定义，不求导，因此不需要 l=h。 -/
theorem spatialDissipation2D_of_sum_zero (c p r hx hy lx ly : ℝ)
    (ha_zero : absorptionSum p r = 0) :
    spatialDissipation2D c p r hx hy lx ly = c * (hx ^ 2 + hy ^ 2) := by
  have ha_swapped_zero : absorptionSum r p = 0 := by
    simpa only [absorptionSum, add_comm] using ha_zero
  simp only [spatialDissipation2D, spatialDissipation, ha_zero, ha_swapped_zero,
    lt_self_iff_false, ↓reduceIte]
  ring

/-- 由 PDF (5.5) 推出：wₓ(c;r,p)=wᵧ(c;p,r)。
正区为 (c−p)/(p+r)，零区两边均为 0；用于二维能量分解。 -/
theorem energyWeightX_swap (c p r : ℝ) :
    energyWeightX c r p = energyWeightY c p r := by
  simp only [energyWeightX, energyWeightY, absorptionSum, add_comm]

/-- 由 PDF (6.2) 空间密度推出：F_sp=F_sp,x+F_sp,y。
即 ½[lₓ²+lᵧ²+wₓ(lₓ−hₓ)²+wᵧ(lᵧ−hᵧ)²] 拆成两项；y 项交换 p,r。 -/
theorem spatialEnergy2D_eq_sum (c p r : ℝ) (hx hy lx ly : ℝ → ℝ) :
    spatialEnergy2D c p r hx hy lx ly =
      (fun t => spatialEnergy c p r hx lx t + spatialEnergy c r p hy ly t) := by
  funext t
  dsimp [spatialEnergy2D, spatialEnergy]
  rw [energyWeightX_swap c p r]
  ring

/-- 由 PDF (7.1) 和零区式按两个方向相加：
F_sp′=(Vₓ+chₓ)lₓ+(Vᵧ+chᵧ)lᵧ−D_sp。
输入真实 hᵢ′=Vᵢ、lₓ′=Vₓ+rhₓ−plₓ、lᵧ′=Vᵧ+phᵧ−rlᵧ；零区另需 lᵢ=hᵢ。
保留耦合项；实际梯度、空间积分和 Green/PEC 均留待后续。 -/
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

以下是本项目构造的教学实例，并非 PDF 原例；只检验局部幅度条件，不保证全部材料阈值。
-/

/-- (7.2) 的教学实例：c=4、S=1、p=r=0 ⇒ D_sp=4hₓ²+4hᵧ²≥0。
调用一般定理；仅计算密度，不从零吸收推断 l=h。 -/
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

/-- (7.2) 的 x 边层教学实例：c=4、S=1、p=1、r=0 ⇒ D_sp=5lₓ²+3hᵧ²≥0。
两个方向分别调用一般定理，核对非对称系数次序。 -/
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

/-- (7.2) 的 y 边层教学实例：c=4、S=1、p=0、r=1 ⇒ D_sp=3hₓ²+5lᵧ²≥0。 -/
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

/-- (7.2) 的角层教学实例：c=4、S=1、p=r=1 ⇒
D_sp=(5/2)(lₓ²+lᵧ²)+(3/2)(hₓ²+hᵧ²)≥0；非负性调用一般定理。 -/
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

/-- 本项目教学路径 l(t)=e^(−t)，配合 h=0、σᵢ=1、σⱼ=0 验证 (7.1)。 -/
noncomputable def spatialDecayPath (t : ℝ) : ℝ := Real.exp (-t)

/-- 教学路径的真实导数：l′(t)=e^(−t)·(−1)=−l(t)。 -/
theorem hasDerivAt_spatialDecayPath (t : ℝ) :
    HasDerivAt spatialDecayPath (-spatialDecayPath t) t := by
  have h_exponent : HasDerivAt (fun s : ℝ => -s) (-1) t :=
    (hasDerivAt_id t).neg
  have h_exp := h_exponent.exp
  exact h_exp.congr_deriv (by dsimp [spatialDecayPath]; ring)

/-- 调用 (7.1) 时间定理的非零实例：c=4、σᵢ=1、σⱼ=0、h=0、l=e^(−t)。
验证 h′=0、l′=−l 后，得到 F_sp,i′=−5e^(−2t)；不是完整 PDE 解。 -/
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

/-- 上述正区教学路径的初值：l(0)=1，F_sp,i(0)=(1+4)/2=5/2。 -/
theorem spatial_positive_path_initial :
    spatialDecayPath 0 = 1 ∧
    spatialEnergy 4 1 0 (fun _ => 0) spatialDecayPath 0 = (5 / 2 : ℝ) := by
  norm_num [spatialDecayPath, spatialEnergy, energyWeightX, absorptionSum]

/-- 零区教学路径 h(t)=l(t)=t+1，因此 f=0；兼容来自显式选择。 -/
def spatialLinearPath (t : ℝ) : ℝ := t + 1

/-- 零区教学路径的真实导数：d(t+1)/dt=1。 -/
theorem hasDerivAt_spatialLinearPath (t : ℝ) :
    HasDerivAt spatialLinearPath 1 t := by
  exact (hasDerivAt_id t).add_const 1

/-- 调用零区二维时间定理：p=r=0、c=4、hᵢ=lᵢ=t+1，得到 F_sp′=2(t+1)。
零区耗散 D_sp=8(t+1)² 与耦合项中的对应项抵消，没有被删掉。 -/
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

/-- 上述零区教学路径的初值：各分量为 1，F_sp(0)=(1²+1²)/2=1。 -/
theorem spatial_zero_path_initial :
    spatialLinearPath 0 = 1 ∧
    spatialEnergy2D 4 0 0 spatialLinearPath spatialLinearPath
      spatialLinearPath spatialLinearPath 0 = 1 := by
  norm_num [spatialLinearPath, spatialEnergy2D, spatialEnergy, energyWeightX, absorptionSum]

end LeanPML.PML
