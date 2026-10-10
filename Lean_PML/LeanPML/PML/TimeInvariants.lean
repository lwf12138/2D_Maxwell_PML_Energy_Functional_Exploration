import LeanPML.Time.Constancy
-- 仅在文件末尾的显式实例中复用上一阶段的实际 E、P 及求导证据。
import LeanPML.Debye.ScalarEnergy

/-!
# 三个标量时间不变量：固定空间点版本

u、q、E、P、Z1、Z2 : ℝ → ℝ 是真实时间函数。
ε、κ、τ、b : ℝ 是时间常参数；完整模型中 b=p(x)r(y) 可随空间变化，
固定一个空间点后才视为时间常数。本文件没有要求 b 在整个空间恒定。

三个恒等式对任意实参数成立，无需正性或非零条件；因此包含物理范围
ε>0、κ>0、τ>0、b≥0，特别保留 b=0。没有除以 b。
不需要 E 的导数、连续性或额外教学方程 ε E'=-P'，也不输入磁场数据。

具体模型先由 HasDerivAt 和原方程导出零导数，再用闭区间常值接口得到
C(t)=C(0)，最后才用初始兼容 C(0)=0 得到全时段兼容。全时段兼容不是输入。
本阶段未构造积分提升、真实场空间、两个磁不变量或原 PDE 的双向等价。
-/

namespace LeanPML.PML

/-- V7 (2.4) 的 Debye 不变量：三个真实函数的线性组合。 -/
noncomputable def CD (κ τ : ℝ) (u q P : ℝ → ℝ) (t : ℝ) : ℝ :=
  q t + τ * P t - κ * u t

/-- 第一个电辅助不变量；ε*b 是与时间无关的乘数。 -/
noncomputable def CZ1 (ε b : ℝ) (u Z1 : ℝ → ℝ) (t : ℝ) : ℝ :=
  Z1 t + ε * b * u t

/-- 第二个电辅助不变量。 -/
noncomputable def CZ2 (b : ℝ) (q Z2 : ℝ → ℝ) (t : ℝ) : ℝ :=
  Z2 t + b * q t

/-- 局部 CD 零导数：dP 通过 hP 绑定到实际 P'，再使用极化方程。 -/
theorem hasDerivAt_CD_zero (κ τ : ℝ) (u q E P : ℝ → ℝ) (t dP : ℝ)
    (hu : HasDerivAt u (E t) t) (hq : HasDerivAt q (P t) t)
    (hP : HasDerivAt P dP t) (hDebye : τ * dP + P t = κ * E t) :
    HasDerivAt (CD κ τ u q P) 0 t := by
  -- add、const_mul、sub 是真实求导规则。参数常数不产生额外导数项。
  have h := (hq.add (hP.const_mul τ)).sub (hu.const_mul κ)
  -- congr_deriv 把得到的导数值替换成等于它的 0。
  apply h.congr_deriv
  calc
    P t + τ * dP - κ * E t = (τ * dP + P t) - κ * E t := by ring
    _ = 0 := sub_eq_zero.mpr hDebye

/-- 局部 CZ1 零导数：Z1' 与 ε*b*u' 正好抵消。 -/
theorem hasDerivAt_CZ1_zero (ε b : ℝ) (u E Z1 : ℝ → ℝ) (t : ℝ)
    (hu : HasDerivAt u (E t) t)
    (hZ1 : HasDerivAt Z1 (-ε * b * E t) t) :
    HasDerivAt (CZ1 ε b u Z1) 0 t := by
  have h := hZ1.add (hu.const_mul (ε * b))
  -- ring 只证明 -ε*b*E + (ε*b)*E = 0，不替代导数存在证据。
  exact h.congr_deriv (by ring)

/-- 局部 CZ2 零导数：只需要 q'=P 与 Z2'=-bP。 -/
theorem hasDerivAt_CZ2_zero (b : ℝ) (q P Z2 : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (P t) t) (hZ2 : HasDerivAt Z2 (-b * P t) t) :
    HasDerivAt (CZ2 b q Z2) 0 t := by
  exact (hZ2.add (hq.const_mul b)).congr_deriv (by ring)

/-- CD 连续只需要 u、q、P 连续，不需要 E 连续。 -/
theorem continuousOn_CD (κ τ : ℝ) {u q P : ℝ → ℝ} {s : Set ℝ}
    (hu : ContinuousOn u s) (hq : ContinuousOn q s) (hP : ContinuousOn P s) :
    ContinuousOn (CD κ τ u q P) s := by
  change ContinuousOn (fun t => q t + τ * P t - κ * u t) s
  exact (hq.add (hP.const_mul τ)).sub (hu.const_mul κ)

/-- CZ1 连续只需要 Z1、u 连续。 -/
theorem continuousOn_CZ1 (ε b : ℝ) {u Z1 : ℝ → ℝ} {s : Set ℝ}
    (hu : ContinuousOn u s) (hZ1 : ContinuousOn Z1 s) :
    ContinuousOn (CZ1 ε b u Z1) s := by
  change ContinuousOn (fun t => Z1 t + ε * b * u t) s
  exact hZ1.add (hu.const_mul (ε * b))

/-- CZ2 连续只需要 Z2、q 连续。 -/
theorem continuousOn_CZ2 (b : ℝ) {q Z2 : ℝ → ℝ} {s : Set ℝ}
    (hq : ContinuousOn q s) (hZ2 : ContinuousOn Z2 s) :
    ContinuousOn (CZ2 b q Z2) s := by
  change ContinuousOn (fun t => Z2 t + b * q t) s
  exact hZ2.add (hq.const_mul b)

/-- 任意初始 CD 保持；区间内的零导数是证明中的中间结论。 -/
theorem CD_eq_initial (κ τ T : ℝ) (u q E P : ℝ → ℝ) (hT : 0 ≤ T)
    (hucont : ContinuousOn u (Set.Icc 0 T))
    (hqcont : ContinuousOn q (Set.Icc 0 T))
    (hPcont : ContinuousOn P (Set.Icc 0 T))
    (hu : ∀ s ∈ Set.Ioo 0 T, HasDerivAt u (E s) s)
    (hq : ∀ s ∈ Set.Ioo 0 T, HasDerivAt q (P s) s)
    (hP : ∀ s ∈ Set.Ioo 0 T, ∃ dP : ℝ,
      HasDerivAt P dP s ∧ τ * dP + P s = κ * E s)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    CD κ τ u q P t = CD κ τ u q P 0 := by
  -- apply 交给一般时间接口，剩下内部逐点零导数目标。
  apply LeanPML.Time.eq_initial_of_hasDerivAt_zero (CD κ τ u q P) T hT
    (continuousOn_CD κ τ hucont hqcont hPcont) ?_ ht
  intro s hs
  -- 从存在量词中同时取出导数值、真实导数证据和原极化方程。
  rcases hP s hs with ⟨dP, hdP, hDebye⟩
  exact hasDerivAt_CD_zero κ τ u q E P s dP (hu s hs) (hq s hs) hdP hDebye

/-- 任意初始 CZ1 保持；无需 q、P 或磁场信息。 -/
theorem CZ1_eq_initial (ε b T : ℝ) (u E Z1 : ℝ → ℝ) (hT : 0 ≤ T)
    (hucont : ContinuousOn u (Set.Icc 0 T))
    (hZcont : ContinuousOn Z1 (Set.Icc 0 T))
    (hu : ∀ s ∈ Set.Ioo 0 T, HasDerivAt u (E s) s)
    (hZ1 : ∀ s ∈ Set.Ioo 0 T, HasDerivAt Z1 (-ε * b * E s) s)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    CZ1 ε b u Z1 t = CZ1 ε b u Z1 0 := by
  apply LeanPML.Time.eq_initial_of_hasDerivAt_zero (CZ1 ε b u Z1) T hT
    (continuousOn_CZ1 ε b hucont hZcont) ?_ ht
  intro s hs
  exact hasDerivAt_CZ1_zero ε b u E Z1 s (hu s hs) (hZ1 s hs)

/-- 任意初始 CZ2 保持；只需 q、Z2 连续和相应原方程。 -/
theorem CZ2_eq_initial (b T : ℝ) (q P Z2 : ℝ → ℝ) (hT : 0 ≤ T)
    (hqcont : ContinuousOn q (Set.Icc 0 T))
    (hZcont : ContinuousOn Z2 (Set.Icc 0 T))
    (hq : ∀ s ∈ Set.Ioo 0 T, HasDerivAt q (P s) s)
    (hZ2 : ∀ s ∈ Set.Ioo 0 T, HasDerivAt Z2 (-b * P s) s)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    CZ2 b q Z2 t = CZ2 b q Z2 0 := by
  apply LeanPML.Time.eq_initial_of_hasDerivAt_zero (CZ2 b q Z2) T hT
    (continuousOn_CZ2 b hqcont hZcont) ?_ ht
  intro s hs
  exact hasDerivAt_CZ2_zero b q P Z2 s (hq s hs) (hZ2 s hs)

/-- 初始 Debye 兼容推出整个闭区间兼容，初值条件只在 0 给定。 -/
theorem CD_compatibility (κ τ T : ℝ) (u q E P : ℝ → ℝ) (hT : 0 ≤ T)
    (hucont : ContinuousOn u (Set.Icc 0 T))
    (hqcont : ContinuousOn q (Set.Icc 0 T))
    (hPcont : ContinuousOn P (Set.Icc 0 T))
    (hu : ∀ s ∈ Set.Ioo 0 T, HasDerivAt u (E s) s)
    (hq : ∀ s ∈ Set.Ioo 0 T, HasDerivAt q (P s) s)
    (hP : ∀ s ∈ Set.Ioo 0 T, ∃ dP : ℝ,
      HasDerivAt P dP s ∧ τ * dP + P s = κ * E s)
    (hinit : q 0 + τ * P 0 - κ * u 0 = 0)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : q t + τ * P t = κ * u t := by
  have hz : CD κ τ u q P t = 0 :=
    (CD_eq_initial κ τ T u q E P hT hucont hqcont hPcont hu hq hP ht).trans hinit
  -- 先从保持定理得到 C(t)=C(0)=0，再将差为零改写成兼容关系。
  change q t + τ * P t - κ * u t = 0 at hz
  exact sub_eq_zero.mp hz

/-- 初始 CZ1 为零推出 Z1(t)=-ε*b*u(t)，不是逐时刻输入兼容。 -/
theorem CZ1_compatibility (ε b T : ℝ) (u E Z1 : ℝ → ℝ) (hT : 0 ≤ T)
    (hucont : ContinuousOn u (Set.Icc 0 T))
    (hZcont : ContinuousOn Z1 (Set.Icc 0 T))
    (hu : ∀ s ∈ Set.Ioo 0 T, HasDerivAt u (E s) s)
    (hZ1 : ∀ s ∈ Set.Ioo 0 T, HasDerivAt Z1 (-ε * b * E s) s)
    (hinit : Z1 0 + ε * b * u 0 = 0)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Z1 t = -ε * b * u t := by
  have hz : CZ1 ε b u Z1 t = 0 :=
    (CZ1_eq_initial ε b T u E Z1 hT hucont hZcont hu hZ1 ht).trans hinit
  change Z1 t + ε * b * u t = 0 at hz
  calc
    Z1 t = -(ε * b * u t) := eq_neg_of_add_eq_zero_left hz
    _ = -ε * b * u t := by ring

/-- 初始 CZ2 为零推出 Z2(t)=-b*q(t)。 -/
theorem CZ2_compatibility (b T : ℝ) (q P Z2 : ℝ → ℝ) (hT : 0 ≤ T)
    (hqcont : ContinuousOn q (Set.Icc 0 T))
    (hZcont : ContinuousOn Z2 (Set.Icc 0 T))
    (hq : ∀ s ∈ Set.Ioo 0 T, HasDerivAt q (P s) s)
    (hZ2 : ∀ s ∈ Set.Ioo 0 T, HasDerivAt Z2 (-b * P s) s)
    (hinit : Z2 0 + b * q 0 = 0)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Z2 t = -b * q t := by
  have hz : CZ2 b q Z2 t = 0 :=
    (CZ2_eq_initial b T q P Z2 hT hqcont hZcont hq hZ2 ht).trans hinit
  change Z2 t + b * q t = 0 at hz
  calc
    Z2 t = -(b * q t) := eq_neg_of_add_eq_zero_left hz
    _ = -b * q t := by ring

/-- b=0 时 Z1 保持初值：只需它自己的连续性及原方程化简后的零导数。 -/
theorem Z1_eq_initial_of_zero_absorption (ε T : ℝ) (Z1 : ℝ → ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn Z1 (Set.Icc 0 T))
    (hZ1 : ∀ s ∈ Set.Ioo 0 T, HasDerivAt Z1 0 s)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Z1 t = Z1 0 := by
  -- b=0 后 CZ1 与 u、E 无关。给通用定理选常零 u、E 是一种实例化，
  -- 不要求物理模型中的 u、E 为零，也不为结论额外索取它们的连续性。
  have h := CZ1_eq_initial ε 0 T (fun _ => 0) (fun _ => 0) Z1 hT
    continuous_const.continuousOn hcont
    (fun s _ => hasDerivAt_const s 0)
    (fun s hs => by simpa using hZ1 s hs) ht
  simpa only [CZ1, mul_zero, zero_mul, add_zero] using h

/-- b=0 时 Z2 保持初值；同样从已有 CZ2 保持结论实例化。 -/
theorem Z2_eq_initial_of_zero_absorption (T : ℝ) (Z2 : ℝ → ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn Z2 (Set.Icc 0 T))
    (hZ2 : ∀ s ∈ Set.Ioo 0 T, HasDerivAt Z2 0 s)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Z2 t = Z2 0 := by
  have h := CZ2_eq_initial 0 T (fun _ => 0) (fun _ => 0) Z2 hT
    continuous_const.continuousOn hcont
    (fun s _ => hasDerivAt_const s 0)
    (fun s hs => by simpa using hZ2 s hs) ht
  simpa only [CZ2, zero_mul, add_zero] using h

/-- 零吸收、Z1 初值为零，得到整个区间 Z1=0。 -/
theorem Z1_zero_of_zero_absorption (ε T : ℝ) (Z1 : ℝ → ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn Z1 (Set.Icc 0 T))
    (hZ1 : ∀ s ∈ Set.Ioo 0 T, HasDerivAt Z1 0 s) (hinit : Z1 0 = 0)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Z1 t = 0 :=
  (Z1_eq_initial_of_zero_absorption ε T Z1 hT hcont hZ1 ht).trans hinit

/-- 零吸收、Z2 初值为零，得到整个区间 Z2=0。 -/
theorem Z2_zero_of_zero_absorption (T : ℝ) (Z2 : ℝ → ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn Z2 (Set.Icc 0 T))
    (hZ2 : ∀ s ∈ Set.Ioo 0 T, HasDerivAt Z2 0 s) (hinit : Z2 0 = 0)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Z2 t = 0 :=
  (Z2_eq_initial_of_zero_absorption T Z2 hT hcont hZ2 ht).trans hinit

/-! ## 零不变量不等于零解：复用真实 Debye 显式函数的一个实例 -/

/-- u=(1-exp(-2t))/2。 -/
noncomputable def exampleU (t : ℝ) : ℝ := (1 - Debye.exampleE t) / 2
/-- q=(1+exp(-2t))/2。 -/
noncomputable def exampleQ (t : ℝ) : ℝ := (1 + Debye.exampleE t) / 2
/-- ε=b=1 时选择 Z1=-u。 -/
noncomputable def exampleZ1 (t : ℝ) : ℝ := -exampleU t
/-- b=1 时选择 Z2=-q。 -/
noncomputable def exampleZ2 (t : ℝ) : ℝ := -exampleQ t

/-- 用真实差与常数除法求导，验证 u'=E。 -/
theorem hasDerivAt_exampleU (t : ℝ) :
    HasDerivAt exampleU (Debye.exampleE t) t := by
  change HasDerivAt (fun s => (1 - Debye.exampleE s) / 2) (Debye.exampleE t) t
  have h := ((hasDerivAt_const t (1 : ℝ)).sub (Debye.hasDerivAt_exampleE t)).div_const 2
  exact h.congr_deriv (by ring)

/-- 同样验证 q'=P；P 是上一阶段实际的负指数函数。 -/
theorem hasDerivAt_exampleQ (t : ℝ) :
    HasDerivAt exampleQ (Debye.exampleP t) t := by
  change HasDerivAt (fun s => (1 + Debye.exampleE s) / 2) (Debye.exampleP t) t
  have h := ((hasDerivAt_const t (1 : ℝ)).add (Debye.hasDerivAt_exampleE t)).div_const 2
  exact h.congr_deriv (by dsimp only [Debye.exampleP]; ring)

/-- Z1=-u 的取负求导，验证 Z1'=-E。 -/
theorem hasDerivAt_exampleZ1 (t : ℝ) :
    HasDerivAt exampleZ1 (-Debye.exampleE t) t := by
  change HasDerivAt (fun s => -exampleU s) (-Debye.exampleE t) t
  exact (hasDerivAt_exampleU t).neg

/-- Z2=-q 的取负求导，验证 Z2'=-P。 -/
theorem hasDerivAt_exampleZ2 (t : ℝ) :
    HasDerivAt exampleZ2 (-Debye.exampleP t) t := by
  change HasDerivAt (fun s => -exampleQ s) (-Debye.exampleP t) t
  exact (hasDerivAt_exampleQ t).neg

/-- 四个新增函数由可导性得到连续；E、P 连续性已在 Debye 模块证明。 -/
theorem example_continuous :
    Continuous exampleU ∧ Continuous exampleQ ∧
    Continuous exampleZ1 ∧ Continuous exampleZ2 := by
  exact ⟨continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exampleU t).continuousAt),
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exampleQ t).continuousAt),
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exampleZ1 t).continuousAt),
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exampleZ2 t).continuousAt)⟩

/-- 实例只交付本阶段所需的极化方程，不引入 εE'=-P'。 -/
theorem example_polarization (t : ℝ) :
    ∃ dP : ℝ, HasDerivAt Debye.exampleP dP t ∧
      (1 : ℝ) * dP + Debye.exampleP t = (1 : ℝ) * Debye.exampleE t := by
  refine ⟨2 * Debye.exampleE t, Debye.hasDerivAt_exampleP t, ?_⟩
  dsimp only [Debye.exampleP]
  ring

/-- 仅在初时刻验证三个不变量为零，不以全时段代数兼容替代保持证明。 -/
theorem example_initial_compatibility :
    CD 1 1 exampleU exampleQ Debye.exampleP 0 = 0 ∧
    CZ1 1 1 exampleU exampleZ1 0 = 0 ∧ CZ2 1 exampleQ exampleZ2 0 = 0 := by
  norm_num [CD, CZ1, CZ2, exampleU, exampleQ, exampleZ1, exampleZ2,
    Debye.exampleE, Debye.exampleP]

/-- P(0)=-1、q(0)=1、Z2(0)=-1，且 q(0)≠0：零不变量允许非零原状态。 -/
theorem example_nonzero_initial :
    Debye.exampleP 0 = -1 ∧ exampleQ 0 = 1 ∧ exampleZ2 0 = -1 ∧ exampleQ 0 ≠ 0 := by
  norm_num [exampleQ, exampleZ2, Debye.exampleE, Debye.exampleP]

/-- 实例通过三个一般兼容保持定理得到整个闭区间的兼容关系。 -/
theorem example_compatibility_on_Icc (T : ℝ) (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    exampleQ t + Debye.exampleP t = exampleU t ∧
    exampleZ1 t = -exampleU t ∧ exampleZ2 t = -exampleQ t := by
  rcases example_continuous with ⟨hucont, hqcont, hz1cont, hz2cont⟩
  rcases example_initial_compatibility with ⟨hD0, hZ10, hZ20⟩
  -- 三个目标分别调用一般保持定理；这里只化简参数1，不用全时段代数定义走捷径。
  refine ⟨?_, ?_, ?_⟩
  · have h := CD_compatibility 1 1 T exampleU exampleQ Debye.exampleE Debye.exampleP hT
      hucont.continuousOn hqcont.continuousOn Debye.continuous_exampleP.continuousOn
      (fun s _ => hasDerivAt_exampleU s) (fun s _ => hasDerivAt_exampleQ s)
      (fun s _ => example_polarization s) hD0 ht
    simpa only [one_mul] using h
  · have h := CZ1_compatibility 1 1 T exampleU Debye.exampleE exampleZ1 hT
      hucont.continuousOn hz1cont.continuousOn (fun s _ => hasDerivAt_exampleU s)
      (fun s _ => by simpa using hasDerivAt_exampleZ1 s) hZ10 ht
    simpa using h
  · have h := CZ2_compatibility 1 T exampleQ Debye.exampleP exampleZ2 hT
      hqcont.continuousOn hz2cont.continuousOn (fun s _ => hasDerivAt_exampleQ s)
      (fun s _ => by simpa using hasDerivAt_exampleZ2 s) hZ20 ht
    simpa using h

end LeanPML.PML

