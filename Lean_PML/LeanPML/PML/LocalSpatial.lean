import LeanPML.PML.Weights
import LeanPML.Time.Constancy
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# 空间块与零吸收区：从 PDF 公式到真实时间求导

来源：V7_global_energy_副本.pdf（页序与印刷页码相同）。第 8 页是 (5.5) 权重与零区保持，
第 9 页是 (6.1)–(6.2)，第 10 页是 (7.1) 和零区式，第 11 页是 (7.2)。

先固定一个空间点：si=σᵢ、sj=σⱼ、a=si+sj，系数不随时间变。
纸面 h=∂ᵢv、l=Λᵢ、f=ψᵢ=l−h；代码先将 h、l 建成 ℝ→ℝ 的时间函数。
x 方向用 (si,sj)=(p,r)，y 方向用 (r,p)；实际梯度与混合微分交换仍待后续连接。

阅读 Lean 时注意：
* h t 是函数 h 在时刻 t 的值；fun s => l s - h s 是整个差函数。
* HasDerivAt h V t 表示“h 在 t 处可导，导数是 V”；V 单独作为实数并不代表导数证据。
* have 为中间结论命名，calc 串起等式；ring 只整理代数，不能替代真实求导。

F_sp、D_sp 是局部能量与耗散密度，不是完整空间积分。
建议依次看：定义 → 正区求导 → 零区兼容保持 → 二维合并 → 实例。
需要更完整的纸面推导时，再查 docs/v0.2.3_reading_guide.md。
-/

namespace LeanPML.PML

/-- 单方向空间能量，取自 PDF 第 8 页 (5.5)、第 10 页 (7.1)：
  F_sp,i(t) = ½ [l(t)² + wᵢ(l(t)−h(t))²]。
h、l 是时间函数，l−h 就是辅助量 f；energyWeightX c si sj 表示 wᵢ。
权重在 a>0 时为 (c−σⱼ)/a，零区取 0，且不随时间变化。
后面的求导定理将证明这个函数的导数；定义本身没有预设导数公式。 -/
noncomputable def spatialEnergy (c si sj : ℝ) (h l : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((l t) ^ 2 + energyWeightX c si sj * (l t - h t) ^ 2) / 2

/-- PDF 第 11 页 (7.2) 中，一个方向的耗散密度为
  D_sp,i = σᵢ(c+σᵢ)l²/a + σⱼ(c−σⱼ)h²/a  （a>0）；
  D_sp,i = c h²                              （a=0）。
此处 h、l 是当前时刻的数值；l² 用本方向吸收 σᵢ，h² 用另一方向吸收 σⱼ，
所以第二个系数必须写 dissipationMinus c sj si。
非负吸收下 else 恰好对应 a=0；范围外 a<0 的取值仅为总函数约定。 -/
noncomputable def spatialDissipation (c si sj h l : ℝ) : ℝ :=
  if 0 < absorptionSum si sj then
    dissipationPlus c si sj * l ^ 2 + dissipationMinus c sj si * h ^ 2
  else c * h ^ 2

/-- PDF 第 9 页 (6.1)–(6.2)：Λ=∇v+ψ，空间密度是 ½(|Λ|²+Σᵢwᵢψᵢ²)。
在代码中展开为
  F_sp(t) = ½[lₓ²+lᵧ²+wₓ(lₓ−hₓ)²+wᵧ(lᵧ−hᵧ)²]。
hx、hy 对应两个梯度分量的时间路径，lx、ly 对应两个 Λ 分量。
这里仅定义局部密度，没有空间积分，也没有电块、极化块的 μ 因子。 -/
noncomputable def spatialEnergy2D (c p r : ℝ)
    (hx hy lx ly : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((lx t) ^ 2 + (ly t) ^ 2 +
    energyWeightX c p r * (lx t - hx t) ^ 2 +
    energyWeightY c p r * (ly t - hy t) ^ 2) / 2

/-- PDF 第 11 页 (7.2) 的完整表达式是
  𝒮[U] = ∫_{Ω₊} Σᵢ[σᵢ(c+σᵢ)Λᵢ²/a + σⱼ(c−σⱼ)(∂ᵢv)²/a] dx dy
          + ∫_Z c|∇v|² dx dy，j≠i。
本定义只构造被积密度 D_sp=D_sp,x+D_sp,y，不构造积分量 𝒮[U]。
x 方向使用 (p,r)，y 方向使用 (r,p)；零区两项合为 c(hₓ²+hᵧ²)。 -/
noncomputable def spatialDissipation2D (c p r hx hy lx ly : ℝ) : ℝ :=
  spatialDissipation c p r hx lx + spatialDissipation c r p hy ly

/-- PDF 第 10 页 (7.1) 后使用的等式：σⱼ+a wᵢ=c。
由 wᵢ=(c−σⱼ)/a 代入并约分得到；ha_pos : 0<a 保证 a≠0。
证明先展开权重的正分支，再消分母；下一条代数恒等式会调用这个结果。 -/
theorem spatial_weight_balance (c si sj : ℝ)
    (ha_pos : 0 < absorptionSum si sj) :
    sj + absorptionSum si sj * energyWeightX c si sj = c := by
  have ha_ne : absorptionSum si sj ≠ 0 := ne_of_gt ha_pos
  rw [energyWeightX, if_pos ha_pos]
  -- 分母 a 已证非零；约分后只需展开加减。
  field_simp [ha_ne]
  ring

/-- PDF 第 10 页 (7.1) 的两行代数表达式：
  lV+(l+wᵢ(l−h))(σⱼh−σᵢl)
    = (V+ch)l − σᵢ(c+σᵢ)l²/a − σⱼ(c−σⱼ)h²/a。
h、l、V 在这里都是实数，不带函数求导的含义。
证明用权重平衡式恢复 wᵢ 的分式表示，在 a≠0 下消分母后用 ring 展开。
后面的真实求导定理调用本引理，完成“已求出的导数值”的整理。 -/
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
    -- eq_div_iff 把目标 w=(c−sj)/a 转为 w*a=c−sj；a≠0 保证等价。
    -- 随后的 nlinarith 用已证 sj+a*w=c 整理出这个等式。
    apply (eq_div_iff ha_ne).2
    nlinarith [hbalance]
  rw [hweight_value]
  dsimp [dissipationPlus, dissipationMinus]
  rw [ha_swapped]
  -- 两个分式同分母 a≠0；消去分母后是普通多项式恒等式。
  field_simp [ha_ne]
  dsimp [absorptionSum]
  ring

/-- PDF 第 10 页 §7.1：f=l−h，fₜ=σⱼh−σᵢl，lₜ=V+σⱼh−σᵢl。
这里输入 hh : HasDerivAt h V t 和 hl，分别证明 h、l 在 t 处的真实导数。
对两函数相减：f′=l′−h′=(V+σⱼh−σᵢl)−V=σⱼh−σᵢl。
因此 f′ 是由原始导数证据推出的结论，并未作为额外假设。 -/
theorem hasDerivAt_spatialAuxiliary (si sj : ℝ) (h l : ℝ → ℝ) (t V : ℝ)
    (hh : HasDerivAt h V t)
    (hl : HasDerivAt l (V + sj * h t - si * l t) t) :
    HasDerivAt (fun s => l s - h s) (sj * h t - si * l t) t := by
  -- sub 是 mathlib 的真实差函数求导规则；ring 仅消去导数值中的 V。
  exact (hl.sub hh).congr_deriv (by ring)

/-- PDF 第 10 页 (7.1)，正吸收区 a>0：
  ½∂ₜ(l²+wᵢf²) = lV+(l+wᵢ(l−h))(σⱼh−σᵢl)
                 = (V+ch)l − σᵢ(c+σᵢ)l²/a − σⱼ(c−σⱼ)h²/a。
h、l 是函数，t 是当前时刻，V 是导数值；hh、hl 才是将它们相连的真实导数证据。
这里只要求 t 处的导数；ha_pos 保证权重分式合法。
证明分为四步：求 f=l−h 的导数 → 平方求导 → 乘权重并相加 → 调用代数恒等式。
目标 HasDerivAt 的第一个参数是能量函数，第二个参数是上式最后一行，第三个是 t。
输出保留 (V+ch)l；尚未进行空间积分或边界处理。 -/
theorem hasDerivAt_spatialEnergy_pos (c si sj : ℝ)
    (h l : ℝ → ℝ) (t V : ℝ)
    (ha_pos : 0 < absorptionSum si sj)
    (hh : HasDerivAt h V t)
    (hl : HasDerivAt l (V + sj * h t - si * l t) t) :
    HasDerivAt (spatialEnergy c si sj h l)
      ((V + c * h t) * l t -
        (dissipationPlus c si sj * (l t) ^ 2 +
          dissipationMinus c sj si * (h t) ^ 2)) t := by
  -- ① 用 l′−h′ 求 f′；这一步用到 f=l−h 和两个原始导数输入。
  have hf : HasDerivAt (fun s => l s - h s) (sj * h t - si * l t) t :=
    hasDerivAt_spatialAuxiliary si sj h l t V hh hl
  -- ② pow 2 使用 (g²)′=2gg′；congr_deriv 配合 ring 只整理导数值的写法。
  have hl_square : HasDerivAt (fun s => (l s) ^ 2)
      (2 * l t * (V + sj * h t - si * l t)) t := by
    exact (hl.pow 2).congr_deriv (by ring)
  have hf_square : HasDerivAt (fun s => (l s - h s) ^ 2)
      (2 * (l t - h t) * (sj * h t - si * l t)) t := by
    exact (hf.pow 2).congr_deriv (by ring)
  -- ③ wᵢ 不随时间变，const_mul 只乘常数；随后 add、div_const 组装能量导数。
  have hweighted_square : HasDerivAt
      (fun s => energyWeightX c si sj * (l s - h s) ^ 2)
      (energyWeightX c si sj * (2 * (l t - h t) * (sj * h t - si * l t))) t :=
    hf_square.const_mul (energyWeightX c si sj)
  have henergy_rule : HasDerivAt (spatialEnergy c si sj h l)
      ((2 * l t * (V + sj * h t - si * l t) +
        energyWeightX c si sj * (2 * (l t - h t) * (sj * h t - si * l t))) / 2) t :=
    (hl_square.add hweighted_square).div_const 2
  -- ④ henergy_rule 已证明能量可导；apply 后只剩“导数值等于论文右端”的代数目标。
  apply henergy_rule.congr_deriv
  -- calc 先整理为 (7.1) 第一行，再调用已证的代数恒等式。
  calc
    (2 * l t * (V + sj * h t - si * l t) +
        energyWeightX c si sj * (2 * (l t - h t) * (sj * h t - si * l t))) / 2 =
        l t * V + (l t + energyWeightX c si sj * (l t - h t)) *
          (sj * h t - si * l t) := by ring
    _ = _ := spatial_rate_identity c si sj (h t) (l t) V ha_pos

/-- PDF 第 10 页零区未编号公式的单方向版本：
  d(h²/2)/dt = hV = (V+ch)h−ch²。
输入只有真实 h′(t)=V；平方求导后，把 hV 改写成论文的平衡形式。
本引理不含 l，后续接回分支能量时才显式使用零区兼容 l=h。 -/
theorem hasDerivAt_zeroSpatialComponent (c : ℝ) (h : ℝ → ℝ) (t V : ℝ)
    (hh : HasDerivAt h V t) :
    HasDerivAt (fun s => (h s) ^ 2 / 2)
      ((V + c * h t) * h t - c * (h t) ^ 2) t := by
  -- pow 和 div_const 给出真实导数；ring 只改写为论文中的平衡形式。
  exact ((hh.pow 2).div_const 2).congr_deriv (by ring)

/-- PDF 第 10 页零区原式：½∂ₜ|∇v|²=(∇vₜ+c∇v)·∇v−c|∇v|²。
把两个方向展开，本定理证明
  d[(hₓ²+hᵧ²)/2]/dt = (Vₓ+chₓ)hₓ+(Vᵧ+chᵧ)hᵧ−c(hₓ²+hᵧ²)。
hhx、hhy 提供真实导数；先相加两个单方向结论，再合并函数中的 1/2。
此处 hₓ、hᵧ 仍是时间路径，实际空间梯度接口尚未实现。 -/
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

/-- PDF 第 8 页 §5.2 的零区保持句：φₜ=0、φ₀=0 ⇒ φ(t)=0。
对单方向 f=l−h，本定理证明：l(0)=h(0) ⇒ l(t)=h(t)，0≤t≤T。
先由非负吸收和 a=0 得 σᵢ=σⱼ=0，再由真实演化得 (l−h)′=0；
随后用闭区间连续、内部零导数得到 l(t)−h(t)=l(0)−h(0)，最后代入初始兼容。
hODE 只要求开区间内部的导数；端点及 T=0 由已有时间常值定理处理。
吸收为零本身只给出“保持初值”，不能省略 hinitial。 -/
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
    -- 取出当前内部时刻 s 的导数值及证据；V 可以随 s 变化。
    obtain ⟨V, hh, hl⟩ := hODE s hs
    have hf := hasDerivAt_spatialAuxiliary si sj h l s V hh hl
    simpa only [habsorption_zero.1, habsorption_zero.2, zero_mul, sub_self] using hf
  -- 差函数连续且内部导数为零：调用时间常值定理，把逐点求导结论变为 f(t)=f(0)。
  have hf_initial : l t - h t = l 0 - h 0 :=
    Time.eq_initial_of_hasDerivAt_zero (fun s => l s - h s) T hT_nonneg
      hf_cont hf_deriv ht
  -- 初始兼容在这里才使用；先验 a=0 单独不足以推出 f=0。
  rw [hinitial, sub_self] at hf_initial
  exact sub_eq_zero.mp hf_initial

/-- PDF 第 10 页零区公式在单方向上写成 F_sp,i′=(V+ch)l−ch²。
a=0 使权重始终为零，所以整个时间函数 F_sp,i(s)=l(s)²/2。
先从 hl 得 l′(t)=V 并求导，再用 hcompat : l(t)=h(t) 改写导数值。
这里没有对单点等式求导；若需整个区间都兼容，可调用前面的保持定理。 -/
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
  -- wᵢ=0 使整个能量函数等于 l²/2；funext 要求逐时刻证明此函数等式。
  have hfunction : spatialEnergy c si sj h l = (fun s => (l s) ^ 2 / 2) := by
    funext s
    simp only [spatialEnergy, hzero_weight, zero_mul, add_zero]
  rw [hfunction]
  -- 此时可导性已知，单点兼容 l(t)=h(t) 仅用于改写导数值，没有对它求导。
  apply hl_energy.congr_deriv
  rw [hcompat]

/-- 合并 PDF 第 10 页正区 (7.1) 与零区式：
  F_sp,i′ = (V+ch)l−D_sp,i。
输入 hh、hl 的真实导数及非负吸收；按 a>0 或 a=0 分别调用已证结果。
hzero 仅在零区要求当前 l(t)=h(t)，正区不要求辅助量为零。
保留耦合项，所以本结论本身不表示能量单调。 -/
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
  · -- 非正分支给 a≤0，非负吸收给 a≥0，二者合起来才得到 a=0。
    have ha_zero : absorptionSum si sj = 0 :=
      le_antisymm (le_of_not_gt ha_pos)
        (absorptionSum_nonneg si sj hsi_nonneg hsj_nonneg)
    have hcompat : l t = h t := hzero ha_zero
    simpa only [spatialDissipation, if_neg ha_pos] using
      hasDerivAt_spatialEnergy_zero c si sj h l t V
        hsi_nonneg hsj_nonneg ha_zero hl hcompat

/-- 由 PDF (5.3)、(7.2) 推出点态非负：
  c>0，0≤σᵢ,σⱼ≤S≤c/4 ⇒ D_sp,i≥0。
正区复用 v0.2.1 的系数界；幅度条件保证 σⱼ≤c，故 c−σⱼ≥0。
把非负系数乘平方再相加；零区直接用 ch²≥0，无需吸收正下界。
这仍是密度结论，不包含空间积分。 -/
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
    -- 旧系数界返回“非负 ∧ 上界”；这里只用 .1 取出非负性，再乘平方。
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

/-- PDF (7.2) 的点态推论：D_sp=D_sp,x+D_sp,y≥0。
输入 c>0、0≤p,r≤S≤c/4，分别调用上一条单方向非负定理。
y 分量交换 p,r 及相应假设，最后用 add_nonneg 将两项相加。 -/
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

/-- PDF (7.2) 零区积分中的密度：c|∇v|²=c(hₓ²+hᵧ²)。
本定理由 a=0 化简两个方向的分支定义，证明 D_sp 正好等于该表达式。
这里只计算密度，不涉及能量求导，所以不需要额外输入 l=h。 -/
theorem spatialDissipation2D_of_sum_zero (c p r hx hy lx ly : ℝ)
    (ha_zero : absorptionSum p r = 0) :
    spatialDissipation2D c p r hx hy lx ly = c * (hx ^ 2 + hy ^ 2) := by
  have ha_swapped_zero : absorptionSum r p = 0 := by
    simpa only [absorptionSum, add_comm] using ha_zero
  simp only [spatialDissipation2D, spatialDissipation, ha_zero, ha_swapped_zero,
    lt_self_iff_false, ↓reduceIte]
  ring

/-- 由 PDF (5.5) 的权重定义推出：wₓ(c;r,p)=wᵧ(c;p,r)。
正区两边均为 (c−p)/(p+r)，零区均为 0。
这说明 y 方向可通过交换 p,r 复用 x 方向定义，用于下面的能量分解。 Weights.lean 中定义 -/
theorem energyWeightX_swap (c p r : ℝ) :
    energyWeightX c r p = energyWeightY c p r := by
  simp only [energyWeightX, energyWeightY, absorptionSum, add_comm]

/-- 由 PDF (6.2) 的空间密度分解得到 F_sp=F_sp,x+F_sp,y，即
  ½[lₓ²+lᵧ²+wₓ(lₓ−hₓ)²+wᵧ(lᵧ−hᵧ)²]
    = ½[lₓ²+wₓ(lₓ−hₓ)²] + ½[lᵧ²+wᵧ(lᵧ−hᵧ)²]。
funext t 将“两个函数相等”变成“每个时刻取值相等”；y 权重通过交换引理连接。
该函数等式让后面的二维求导可以直接复用两个单方向定理。 -/
theorem spatialEnergy2D_eq_sum (c p r : ℝ) (hx hy lx ly : ℝ → ℝ) :
    spatialEnergy2D c p r hx hy lx ly =
      (fun t => spatialEnergy c p r hx lx t + spatialEnergy c r p hy ly t) := by
  funext t
  dsimp [spatialEnergy2D, spatialEnergy]
  rw [energyWeightX_swap c p r]
  ring

/-- 将 PDF (7.1) 及零区公式分别用于 x、y 方向，得到
  F_sp′ = (Vₓ+chₓ)lₓ+(Vᵧ+chᵧ)lᵧ−D_sp。
四个真实导数输入为 hₓ′=Vₓ、lₓ′=Vₓ+rhₓ−plₓ，
以及 hᵧ′=Vᵧ、lᵧ′=Vᵧ+phᵧ−rlᵧ；所有数值均取在 t。
hzero 只在 a=0 时提供 lₓ(t)=hₓ(t)、lᵧ(t)=hᵧ(t)。
证明先按两个方向调用单方向定理，再通过能量分解和 add 合并。
实际梯度、空间积分及 Green/PEC 是后续接口；耦合项在这里完整保留。 -/
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
  -- y 方向交换 p,r；因 r+p=p+r，仍可使用同一个零区兼容条件。
  have hy_zero : absorptionSum r p = 0 → ly t = hy t := by
    intro ha_swapped_zero
    have ha_zero : absorptionSum p r = 0 := by
      simpa only [absorptionSum, add_comm] using ha_swapped_zero
    exact (hzero ha_zero).2
  -- x 用 (si,sj)=(p,r)，y 用 (r,p)，因此导数证据和非负假设也按方向交换。
  have hx_energy := hasDerivAt_spatialEnergy c p r hx lx t Vx
    hp_nonneg hr_nonneg hhx hlx hx_zero
  have hy_energy := hasDerivAt_spatialEnergy c r p hy ly t Vy
    hr_nonneg hp_nonneg hhy hly hy_zero
  -- rw 改写整个能量函数为两方向之和，使真实函数求导规则 add 可以使用。
  rw [spatialEnergy2D_eq_sum]
  -- 此后只整理导数值：把两个耗散项合并为 D_sp，保留两个耦合项。
  apply (hx_energy.add hy_energy).congr_deriv
  dsimp [spatialDissipation2D]
  ring

/-!
## 四分支与非零真实时间路径

以下是本项目构造的教学实例，并非 PDF 原例；只检验局部幅度条件，不保证全部材料阈值。
norm_num 验证所选数值满足一般定理的假设；constructor 将“密度等式 ∧ 非负性”拆开证明。
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

/-- 教学路径 l(t)=e^(−t) 的真实导数为 −l(t)。
先证明内函数 −t 的导数为 −1，再用 exp 的链式法则得到 e^(−t)·(−1)。
congr_deriv 只把这个导数值整理为 −e^(−t)，不改变被求导的函数。 -/
theorem hasDerivAt_spatialDecayPath (t : ℝ) :
    HasDerivAt spatialDecayPath (-spatialDecayPath t) t := by
  have h_exponent : HasDerivAt (fun s : ℝ => -s) (-1) t :=
    (hasDerivAt_id t).neg
  have h_exp := h_exponent.exp
  exact h_exp.congr_deriv (by dsimp [spatialDecayPath]; ring)

/-- 调用 (7.1) 时间定理的非零实例：c=4、σᵢ=1、σⱼ=0、h=0、l=e^(−t)。
先验证 h′=0、l′=−l 满足辅助演化，再调用 hasDerivAt_spatialEnergy。
本例耦合项为 0，密度 D_sp,i=5e^(−2t)，故 F_sp,i′=−5e^(−2t)。
这是一般定理在真实时间路径上的应用，不是完整二维 PDE 解。 -/
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

/-- 零区教学路径的真实导数：d(t+1)/dt=1。
hasDerivAt_id 给出 t 的导数；add_const 说明加上常数 1 不改变导数。 -/
theorem hasDerivAt_spatialLinearPath (t : ℝ) :
    HasDerivAt spatialLinearPath 1 t := by
  exact (hasDerivAt_id t).add_const 1

/-- 零区二维时间路径：p=r=0、c=4、hᵢ=lᵢ=t+1，故各分量真实导数为 1。
验证辅助演化和兼容后，调用 hasDerivAt_spatialEnergy2D，得到 F_sp′=2(t+1)。
其中 D_sp=8(t+1)² 与耦合项中的对应项抵消，没有被删掉。
本例也说明：耗散密度非负，并不使单独空间块的导数非正。 -/
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
