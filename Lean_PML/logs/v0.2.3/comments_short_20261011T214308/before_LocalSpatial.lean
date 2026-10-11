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

## 直接对照 PDF 的阅读约定（本次仅补充注释）

对应 PDF：V7_global_energy_副本.pdf；以下页码均为实际页序号，也等于印刷页码。
第 8 页：(5.5) 分支权重、§5.2 零区保持句；第 9 页：(6.1)、(6.2)；
第 10 页：(7.1) 和其后未编号零区公式；第 11 页：(7.2)。
每条声明下的“PDF 原式”保留纸面符号；“推出/实例”表示本项目的改写或应用，
不是额外虚构的论文公式编号。公式用普通 Unicode 文本排版，直接读源码即可。

符号字典：
  PDF 的 a = σᵢ + σⱼ          ↔ Lean 的 absorptionSum si sj；
  PDF 的 h = ∂ᵢv、l = Λᵢ      ↔ Lean 的时间函数 h、l；
  PDF 的 f = ψᵢ = l − h       ↔ Lean 的 fun s => l s - h s；
  PDF 的 V = ∂ᵢvₜ             ↔ Lean 中由 HasDerivAt h V t 约束的实数 V；
  PDF 省略的当前时刻           ↔ Lean 的 h t、l t；l(t)² ↔ (l t) ^ 2。
HasDerivAt F D t 的意思是“真实函数 F 在 t 处可导，导数为 D”。
纸面空间符号与时间函数的上述对应是未来接口的目标，不是本轮新增的空间证明。

F_sp,i、F_sp、D_sp,i、D_sp 是下面为局部密度取的简称；
它们不同于 PDF 完整积分能量 𝓕_c[U] 和积分耗散 𝒮[U]。
-/

namespace LeanPML.PML

/-- V7 (7.1) 的单方向局部空间能量，含 1/2，不含空间积分。
用 (5.5) 已有的分支权重，f 直接定义为 l-h，避免独立辅助函数的兼容负担。
参数 c,si,sj 在时间上恒定；此定义没有断言 h 是真实空间梯度。

【PDF 第 8 页 (5.5)、第 10 页 (7.1)：取出单方向能量】
  wᵢ = (c − σⱼ)/a  （a > 0），  wᵢ = 0  （a = 0）；
  f = l − h，  F_sp,i(t) := ½ [l(t)² + wᵢ f(t)²]。
PDF (7.1) 左端就是 ∂ₜF_sp,i；F_sp,i 是本文件为这部分取的简称。
Lean 对照：energyWeightX c si sj = wᵢ，l t - h t = f(t)。
在 y 方向调用时交换 si、sj，因此仍复用同一个单方向定义。
-/
noncomputable def spatialEnergy (c si sj : ℝ) (h l : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((l t) ^ 2 + energyWeightX c si sj * (l t - h t) ^ 2) / 2

/-- V7 (7.2) 的单方向点态耗散。
正区 l² 前取 si(c+si)/a，h² 前取 sj(c-sj)/a；后者调用时必须交换 si,sj。
零区独立取 c*h²，不能用分式的除零值替代。
物理范围 si,sj≥0 时 else 就是 a=0；范围外 a<0 的值仅是总函数约定。

【PDF 第 11 页 (7.2)：取出一个方向的被积密度】
  D_sp,i = [σᵢ(c + σᵢ)/a] l² + [σⱼ(c − σⱼ)/a] h²  （a > 0）；
  D_sp,i = c h²                                               （a = 0）。
其中 l = Λᵢ、h = ∂ᵢv 是纸面对应，D_sp,i 是本项目的局部记号。
Lean 对照：dissipationPlus c si sj = σᵢ(c + σᵢ)/a；
            dissipationMinus c sj si = σⱼ(c − σⱼ)/a。
这里 h、l 是某时刻的实数值，所以不写 h t、l t；此定义不构造空间积分。
-/
noncomputable def spatialDissipation (c si sj h l : ℝ) : ℝ :=
  if 0 < absorptionSum si sj then
    dissipationPlus c si sj * l ^ 2 + dissipationMinus c sj si * h ^ 2
  else c * h ^ 2

/-- V7 (6.2)、(7.1) 空间部分的两个时间分量之和。
x,y 分别显式使用已有 energyWeightX、energyWeightY；不包含空间积分。
后面的分解引理把它连接到交换 p,r 的两个单方向表达式。

【PDF 第 9 页 (6.1)–(6.2)：仅取空间部分】
  Λ = ∇v + ψ，  ψᵢ = Λᵢ − ∂ᵢv；
  完整能量的空间部分 = ½ ∫_Ω [|Λ|² + Σᵢ wᵢ ψᵢ²] dx dy。
本定义是这个积分中的局部密度：
  F_sp(t) = ½ [lₓ(t)² + lᵧ(t)²
                + wₓ(lₓ(t) − hₓ(t))² + wᵧ(lᵧ(t) − hᵧ(t))²]。
Lean 对照：hx/hy ↔ ∂ₓv/∂ᵧv，lx/ly ↔ Λₓ/Λᵧ。
(6.2) 的电块、极化块不在此定义中；也没有进行上述空间积分。
-/
noncomputable def spatialEnergy2D (c p r : ℝ)
    (hx hy lx ly : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((lx t) ^ 2 + (ly t) ^ 2 +
    energyWeightX c p r * (lx t - hx t) ^ 2 +
    energyWeightY c p r * (ly t - hy t) ^ 2) / 2

/-- V7 (7.2) 的二维点态密度；这里只相加两个方向，不构造积分算子。
零区时该定义保留 c*(hx²+hy²)，其正式等式见下方零区定理。

【PDF 第 11 页 (7.2)：完整原式与本定义的关系】
  𝒮[U] = ∫_{Ω₊} Σ_{i∈{x,y}}
            [σᵢ(c + σᵢ)/a · Λᵢ² + σⱼ(c − σⱼ)/a · (∂ᵢv)²] dx dy
           + ∫_Z c|∇v|² dx dy，  j ≠ i。
这里 Ω₊ = {a > 0}，Z = {a = 0}。
本定义只相加两个点态密度，尚不是左端的积分量 𝒮[U]：
  D_sp = D_sp,x + D_sp,y；
  a > 0：D_sp = p(c+p)/a · lₓ² + r(c−r)/a · hₓ²
                   + r(c+r)/a · lᵧ² + p(c−p)/a · hᵧ²；
  a = 0：D_sp = c(hₓ² + hᵧ²)。
因此 y 方向调用 spatialDissipation c r p hy ly，交换的是吸收方向。
-/
noncomputable def spatialDissipation2D (c p r hx hy lx ly : ℝ) : ℝ :=
  spatialDissipation c p r hx lx + spatialDissipation c r p hy ly

/-- V7 (7.1) 所用的权重平衡 sj+a*w=c。
这里只需 a>0；没有除以 si 或 sj。分母非零由正分支给出。
输出将用于空间块的代数恒等式。

【PDF 第 10 页 (7.1) 后的未编号等式】
  σⱼ + a wᵢ = c。
代入 PDF (5.5) 可直接看出：
  σⱼ + a · (c − σⱼ)/a = σⱼ + c − σⱼ = c。
Lean 的 absorptionSum si sj 就是 a；ha_pos 保证这里的约分合法。
-/
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
下方真实时间定理将调用它整理由乘积/平方法则得到的导数。

【PDF 第 10 页 (7.1)：只核验两行右端相等】
  lV + (l + wᵢ(l − h))(σⱼh − σᵢl)
    = (V + ch)l − [σᵢ(c + σᵢ)/a] l² − [σⱼ(c − σⱼ)/a] h²。
Lean 左端逐项照写第一行，右端把两个分式命名为
dissipationPlus c si sj 与 dissipationMinus c sj si。
本引理没有 PDF 左端的 ∂ₜ；真正的时间求导由后面的定理承担。
-/
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
没有把 f' 当作独立输入。此结果供空间能量求导及零区保持使用。

【PDF 第 10 页 §7.1，(7.1) 前的未编号辅助方程】
  f = l − h，  fₜ = σⱼh − σᵢl，  lₜ = V + σⱼh − σᵢl。
本定理如何得到第一条导数，而不把它当作输入：
  f′(t) = l′(t) − h′(t)
        = [V + σⱼh(t) − σᵢl(t)] − V
        = σⱼh(t) − σᵢl(t)。
HasDerivAt (fun s => l s - h s) (...) t 正是最后这条真实导数命题。
-/
theorem hasDerivAt_spatialAuxiliary (si sj : ℝ) (h l : ℝ → ℝ) (t V : ℝ)
    (hh : HasDerivAt h V t)
    (hl : HasDerivAt l (V + sj * h t - si * l t) t) :
    HasDerivAt (fun s => l s - h s) (sj * h t - si * l t) t := by
  -- sub 是 mathlib 的真实差函数求导规则；ring 仅消去导数值中的 V。
  exact (hl.sub hh).congr_deriv (by ring)

/-- V7 (7.1) 正吸收分支的真实时间求导。
ha_pos 只用于权重与分式代数；hh、hl 是原始真实导数输入。
先由 f=l-h 求 f'，再平方求导、常数乘法、相加并除以 2。
输出保留 (V+c*h)*l，尚未使用任何空间积分或边界条件。

【PDF 第 10 页 (7.1)：完整原式】
  ½ ∂ₜ(l² + wᵢf²)
    = lV + (l + wᵢ(l − h))(σⱼh − σᵢl)
    = (V + ch)l − [σᵢ(c + σᵢ)/a] l² − [σⱼ(c − σⱼ)/a] h²。
本定理中每个量都取在同一个求导点 t：
  HasDerivAt (spatialEnergy c si sj h l) (上式最后一行) t。
证明顺序对应纸面链条：
  ① f=l−h → 求 f′；② 求 l²、f² 的导数；
  ③ 乘常数 wᵢ、相加、除以 2 → 得到第一行；
  ④ 调用 spatial_rate_identity → 得到最后一行。
这仍是固定空间点的时间版本，不代表已经构造 h=∂ᵢv 的空间接口。
-/
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
此时 c*h² 不能因吸收为零而删掉；这仍不声称 h 已是空间梯度。

【PDF 第 10 页 (7.1) 后零区公式：取一个分量】
原式：½ ∂ₜ|∇v|² = (∇vₜ + c∇v)·∇v − c|∇v|²。
本引理证明它的单方向时间版本：
  d/dt [h(t)²/2] = h(t)V = (V + c h(t))h(t) − c h(t)²。
这里没有 l 或 f，所以只需 h′(t)=V；将它接回实际分支能量时，
l=h 的兼容输入由 hasDerivAt_spatialEnergy_zero 明确提供。
-/
theorem hasDerivAt_zeroSpatialComponent (c : ℝ) (h : ℝ → ℝ) (t V : ℝ)
    (hh : HasDerivAt h V t) :
    HasDerivAt (fun s => (h s) ^ 2 / 2)
      ((V + c * h t) * h t - c * (h t) ^ 2) t := by
  -- pow 和 div_const 给出真实导数；ring 只改写为论文中的平衡形式。
  exact ((hh.pow 2).div_const 2).congr_deriv (by ring)

/-- V7 (7.1) 后未编号零区公式的二维时间版本。
输入两个方向真实 hᵢ'=Vᵢ，不要求端点或空间微分；相加后保留 c*(hx²+hy²)。
下游将把 hᵢ 与实际空间梯度连接，目前这个接口仍未兑现。

【PDF 第 10 页 (7.1) 后的未编号零区原式】
  ½ ∂ₜ|∇v|² = (∇vₜ + c∇v)·∇v − c|∇v|²。
将纸面的两个方向写开，对应本定理：
  d/dt [(hₓ(t)² + hᵧ(t)²)/2]
    = (Vₓ + c hₓ(t))hₓ(t) + (Vᵧ + c hᵧ(t))hᵧ(t)
        − c(hₓ(t)² + hᵧ(t)²)。
Lean 的 hhx、hhy 分别证明 hₓ′(t)=Vₓ、hᵧ′(t)=Vᵧ。
本式只验证时间分量；纸面 ∇v 与这些函数的对应留待空间分析。
-/
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
而不是预设整个区间已经相等。不涉及磁不变量或原 PDE 的提升构造。

【PDF 第 8 页 §5.2 未编号保持句；第 10 页零区公式的前提】
PDF 写道：在 Z 上 φₜ=0，因此 φ₀=0 保持。
在 U₀ 层 ψ=φ，对一个方向 f=ψᵢ=l−h；本定理证明如下时间版：
  σᵢ,σⱼ ≥ 0，a=0  ⇒  σᵢ=σⱼ=0  ⇒  f′(t)=0；
  f(0)=0  ⇒  f(t)=f(0)=0  ⇒  l(t)=h(t)，  0≤t≤T。
Lean 的 hinitial : l 0 = h 0 表达 f(0)=0；
结论 l t = h t 才表达全时段兼容，不是把它预设为假设。
闭区间连续和内部导数通过一般时间常值定理连接，包含 T=0。
-/
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
未来若需区间兼容，应调用上面的保持定理或完整 PDE 的兼容保持。

【PDF 第 10 页 (7.1) 后的零区公式：与分支能量接合】
  a=0，wᵢ=0，f=0，l=h；
  F_sp,i = l²/2，  F_sp,i′ = (V+ch)l − c h²。
注意代码中两个不同的等式用途：
  对所有时间 s：wᵢ=0 ⇒ F_sp,i(s)=l(s)²/2；
  只在当前点 t：l(t)=h(t)，用于改写已经得到的导数值。
因此没有从单点 l(t)=h(t) 错误地推断两函数的导数相等。
-/
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
输出完整保留耦合项；不声称本块能量已经单调。

【由 PDF 第 10 页正区 (7.1) 和未编号零区式合并；不是另一个论文编号】
  F_sp,i′(t) = (V + c h(t))l(t) − D_sp,i(t)，
其中
  a>0：D_sp,i = [σᵢ(c+σᵢ)/a]l² + [σⱼ(c−σⱼ)/a]h²；
  a=0：D_sp,i = c h²，且需要 l(t)=h(t)。
本定理的 hzero 正是第二分支的兼容条件；正分支不要求它成立。
Lean 的 by_cases ha_pos 对应这两行数学分类。
-/
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
该结论仅为点态密度性质，没有证明可测、可积或积分能量定理。

【由 PDF 第 11 页 (7.2) 的被积式推出；点态结论】
  c>0，0≤σᵢ,σⱼ≤S≤c/4  ⇒  D_sp,i ≥ 0。
分开看非负性的来源：
  a>0：σᵢ(c+σᵢ)/a ≥ 0，σⱼ(c−σⱼ)/a ≥ 0，l²,h² ≥ 0；
  a=0：D_sp,i = c h² ≥ 0。
这不是对 (7.2) 积分量 𝒮[U] 的形式化证明，当前只处理密度。
-/
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
空间积分的非负性仍需可测性、可积性等后续接口。

【由 PDF 第 11 页 (7.2) 推出的二维点态结论】
  D_sp = D_sp,x + D_sp,y ≥ 0。
其中
  D_sp,x = D_sp,i(c,p,r,hₓ,lₓ)，
  D_sp,y = D_sp,i(c,r,p,hᵧ,lᵧ)。
代码分别从单方向非负定理得到 hx_nonneg、hy_nonneg，再相加。
输入 0≤p,r≤S≤c/4、c>0；无需吸收的统一正下界。
-/
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
这是零区实例和以后积分分区需要的明确公式。

【PDF 第 11 页 (7.2) 第二个积分的被积式】
  ∫_Z c|∇v|² dx dy，其中 |∇v|²=(∂ₓv)²+(∂ᵧv)²。
本定理只证明对应的点态分支化简：
  a=0 ⇒ D_sp = c(hₓ²+hᵧ²)。
这里不求导、不构造积分，因此也不需要 l=h；兼容条件是在零区能量
求导接合时使用，而不是耗散定义的这一步分支计算所需。
-/
theorem spatialDissipation2D_of_sum_zero (c p r hx hy lx ly : ℝ)
    (ha_zero : absorptionSum p r = 0) :
    spatialDissipation2D c p r hx hy lx ly = c * (hx ^ 2 + hy ^ 2) := by
  have ha_swapped_zero : absorptionSum r p = 0 := by
    simpa only [absorptionSum, add_comm] using ha_zero
  simp only [spatialDissipation2D, spatialDissipation, ha_zero, ha_swapped_zero,
    lt_self_iff_false, ↓reduceIte]
  ring

/-- 由 V7 (5.5) 推出的方向映射：交换 p,r 的 x 权重就是原来的 y 权重。
两分支同时成立；这里不是新增权重定义。下方二维能量分解实际调用此等式。

【由 PDF 第 8 页 (5.5) 推出的方向交换关系】
  wₓ(c;p,r)=(c−r)/(p+r)，  wᵧ(c;p,r)=(c−p)/(p+r)  （p+r>0）；
  wₓ(c;r,p)=wᵧ(c;p,r)。
零区两边同为 0，故交换等式覆盖两个分支。
这是原权重定义的推论，不是 PDF 中另有编号的公式。
-/
theorem energyWeightX_swap (c p r : ℝ) :
    energyWeightX c r p = energyWeightY c p r := by
  simp only [energyWeightX, energyWeightY, absorptionSum, add_comm]

/-- V7 (6.2) 空间密度的方向分解：二维能量等于 x 分量加交换 p,r 的 y 分量。
用上一条权重映射核对方向，再由 ring 合并 1/2 因子；不涉及求导。
下方二维真实时间定理通过此函数等式复用单方向求导。

【由 PDF 第 9 页 (6.2) 的空间密度推出】
  ½ [lₓ²+lᵧ²+wₓ(lₓ−hₓ)²+wᵧ(lᵧ−hᵧ)²]
    = ½ [lₓ²+wₓ(lₓ−hₓ)²] + ½ [lᵧ²+wᵧ(lᵧ−hᵧ)²]。
即 F_sp = F_sp,x + F_sp,y；y 项通过交换 p,r 复用单方向定义。
Lean 用 funext t 逐时刻证明，所得结论是两个时间函数相等，可用于求导改写。
-/
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
输出保留两个 (Vᵢ+c*hᵢ)*lᵢ，尚未完成实际梯度、空间积分或 Green/PEC。

【由 PDF 第 10 页 (7.1) 及零区公式分别对 x、y 相加】
  d/dt {½[lₓ²+lᵧ²+wₓ(lₓ−hₓ)²+wᵧ(lᵧ−hᵧ)²]}
    = (Vₓ+chₓ)lₓ + (Vᵧ+chᵧ)lᵧ − D_sp。
输入的四条实际时间演化具体是：
  hₓ′=Vₓ，  lₓ′=Vₓ+r hₓ−p lₓ；
  hᵧ′=Vᵧ，  lᵧ′=Vᵧ+p hᵧ−r lᵧ。
所有值均在 t；若 a=0，还须 lₓ(t)=hₓ(t)、lᵧ(t)=hᵧ(t)。
PDF (7.2) 将 D_sp 作分区空间积分；本定理没有执行那一步。
尤其右端两个 (Vᵢ+chᵢ)lᵢ 保持原样，等待后续与主方程和 Green 公式结合。
-/
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
注意本结论只计算耗散密度，不从 p=r=0 推出 l=h。

【(7.2) 点态密度的本项目实例，PDF 没有此数值例】
  c=4，S=1，p=r=0：
  D_sp = 4hₓ² + 4hᵧ² ≥ 0。
这里只实例化独立零区分支，不声称吸收为零自动推出 l=h。
-/
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
非负性来自一般点态定理，数值化简只核对精确展开。

【(7.2) 点态密度的本项目 x 边层实例，非 PDF 原式】
  c=4，S=1，p=1，r=0，a=1：
  x 方向系数：(lₓ²,hₓ²) ↦ (5,0)；
  y 方向系数：(lᵧ²,hᵧ²) ↦ (0,3)；
  D_sp = 5lₓ² + 3hᵧ² ≥ 0。
这使交换方向的影响在最终结果中直接可见。
-/
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
此时精确留下 3hₓ²+5lᵧ²；与上一条交换 x、y，核验非对称边层没有漏项。

【(7.2) 点态密度的本项目 y 边层实例，非 PDF 原式】
  c=4，S=1，p=0，r=1，a=1：
  x 方向系数：(lₓ²,hₓ²) ↦ (0,3)；
  y 方向系数：(lᵧ²,hᵧ²) ↦ (5,0)；
  D_sp = 3hₓ² + 5lᵧ² ≥ 0。
-/
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
它补足双向吸收，但不替代前两条非对称方向检查。

【(7.2) 点态密度的本项目角层实例，非 PDF 原式】
  c=4，S=1，p=r=1，a=2：
  σᵢ(c+σᵢ)/a=5/2，  σⱼ(c−σⱼ)/a=3/2；
  D_sp = (5/2)(lₓ²+lᵧ²) + (3/2)(hₓ²+hᵧ²) ≥ 0。
-/
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
这是时间路径实例的定义，不是完整二维 PDE 解。

【用于调用 (7.1) 时间版的教学路径，PDF 未给出此定义】
  h(t)=0，  l(t)=e^(−t)，  V=0，  (σᵢ,σⱼ)=(1,0)。
本定义只命名 l；其导数和辅助演化在后续定理中验证。
-/
noncomputable def spatialDecayPath (t : ℝ) : ℝ := Real.exp (-t)

/-- 指数路径的真实导数。由 mathlib 的恒等函数、取负和 exp 求导规则构造；
ring 只把链式法则产生的 exp(-t)·(-1) 整理为 -exp(-t)。

【本项目路径的基础求导，供 (7.1) 实例使用】
  l(t)=e^(−t)  ⇒  l′(t)=e^(−t)·(−1)=−l(t)。
这是指数链式法则，不是 PDF 中另一个编号公式。
-/
theorem hasDerivAt_spatialDecayPath (t : ℝ) :
    HasDerivAt spatialDecayPath (-spatialDecayPath t) t := by
  have h_exponent : HasDerivAt (fun s : ℝ => -s) (-1) t :=
    (hasDerivAt_id t).neg
  have h_exp := h_exponent.exp
  exact h_exp.congr_deriv (by dsimp [spatialDecayPath]; ring)

/-- V7 (7.1) 的非零正吸收路径调用：h=0、l=exp(-t)，c=4、σᵢ=1、σⱼ=0。
先明确验证 h'=0 与 l'=0+σⱼh-σᵢl，再调用一般真实求导定理。
结果为 F_sp'=-5 exp(-t)²；这个实例不承担空间梯度或 PDE 接口。

【把教学路径代入 PDF (7.1)，并调用其一般时间版本】
  c=4，σᵢ=1，σⱼ=0，h=0，l=e^(−t)；
  a=1，wᵢ=4，F_sp,i=(5/2)e^(−2t)；
  (V+ch)l=0，D_sp,i=5e^(−2t)，故 F_sp,i′=−5e^(−2t)。
代码中的 −5*(spatialDecayPath t)² 就是这个导数值。
先证明真实路径的导数，再调用一般定理；没有把本行导数值当作输入。
-/
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
这里只核对初值；随时间可导的核心证据是上一条一般定理的调用。

【上一条教学路径的初值核对，非 PDF 独立公式】
  l(0)=e⁰=1，  F_sp,i(0)=(1²+4·1²)/2=5/2。
这说明实际调用 (7.1) 的路径并非恒零。
-/
theorem spatial_positive_path_initial :
    spatialDecayPath 0 = 1 ∧
    spatialEnergy 4 1 0 (fun _ => 0) spatialDecayPath 0 = (5 / 2 : ℝ) := by
  norm_num [spatialDecayPath, spatialEnergy, energyWeightX, absorptionSum]

/-- 零区的非零路径 h(t)=l(t)=t+1，显式满足零辅助量 f=l-h=0。
该条件由路径的定义保证，不能从 σᵢ=σⱼ=0 单独推出。

【用于调用零区公式的教学路径，PDF 未给出此定义】
  h(t)=l(t)=t+1，  f(t)=l(t)−h(t)=0。
等式来自本例的显式选择，而不是由 p=r=0 自动推出。
-/
def spatialLinearPath (t : ℝ) : ℝ := t + 1

/-- 上述零区路径的真实导数为 1。mathlib 的 add_const 表达常数项导数为零，
保留原来的恒等函数导数；后面用它验证两个方向的辅助演化。

【本项目路径的基础求导，供零区公式实例使用】
  d/dt (t+1)=1。
HasDerivAt spatialLinearPath 1 t 把实数 1 绑定到这条真实函数的导数。
-/
theorem hasDerivAt_spatialLinearPath (t : ℝ) :
    HasDerivAt spatialLinearPath 1 t := by
  exact (hasDerivAt_id t).add_const 1

/-- V7 (7.1) 后零区公式的非零二维时间路径实例：
两方向均取 h=l=t+1，p=r=0，c=4。
调用一般二维分支求导定理；全程保留零区耗散，它与移位乘积中的相应项抵消。
结论仅是时间分量能量导数 2(t+1)，不把这些路径命名为实际空间梯度。

【把教学路径代入 PDF 第 10 页未编号零区公式】
  p=r=0，c=4，hₓ=lₓ=hᵧ=lᵧ=t+1，Vₓ=Vᵧ=1；
  F_sp=(t+1)²，  D_sp=8(t+1)²；
  (Vₓ+chₓ)lₓ+(Vᵧ+chᵧ)lᵧ
    = 2(t+1)+8(t+1)²。
两项相减得到 F_sp′=2(t+1)，代码通过一般二维求导定理得到该结论。
D_sp≥0 没有使这个空间块自动单调，因为耦合乘积仍然存在。
-/
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
说明“零吸收且零辅助量”并不要求梯度分量路径为零。

【上一条零区教学路径的初值核对，非 PDF 独立公式】
  hₓ(0)=lₓ(0)=hᵧ(0)=lᵧ(0)=1；
  F_sp(0)=(1²+1²)/2=1。
所以“零吸收、辅助量为零”仍允许非零的时间分量。
-/
theorem spatial_zero_path_initial :
    spatialLinearPath 0 = 1 ∧
    spatialEnergy2D 4 0 0 spatialLinearPath spatialLinearPath
      spatialLinearPath spatialLinearPath 0 = 1 := by
  norm_num [spatialLinearPath, spatialEnergy2D, spatialEnergy, energyWeightX, absorptionSum]

end LeanPML.PML
