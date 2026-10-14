import LeanPML.PML.WeakCkRegularity
import LeanPML.Rectangle.SharpPoincare

/-!
# 矩形弱图空间兼容解类的全域先验能量定理

对应 V7 (6.7)–(6.10)。输入是真实原八变量、原式、PEC/H₀¹、初始兼容、
图范数/L² 时间正则性及初始加权成员。所有弱空间分析接口在证明内部构造。
空间不再要求联合 C∞；时间正则性准确列在 OriginalInterval、OriginalJet 中。
本文件改用已证 (5.1) 的 π 常数，保留旧保守入口。时间/系数假设仍须明确；不声称一般解存在唯一性。
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.Weak
namespace OriginalInterval
variable {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
variable (O : OriginalInterval D C ε κ τ μ T) (J : OriginalJet O)
variable (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)

/-- 改变已证 Poincaré 常数不改变状态的空间、零迹、极化约束。
这里只搬运相同数学约束，未搬运任何能量估计。 -/
theorem sharp_base_constraints
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    StateCoercivityConstraints D.measure C (weakGreenDomain D).spatial
      (sharpWeakPoincareDomain D) κ τ (O.baseState W₀x W₀y t) := by
  have hc := O.base_constraints W₀x W₀y hWx hWy ht
  exact ⟨hc.spatial, hc.zeroTrace, hc.polar⟩

/-- 同源导数层的同一搬运；T=0 的兼容条件仍显式保留。 -/
theorem sharp_first_constraints
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O J) {t : ℝ} (ht : t ∈ Icc 0 T) :
    StateCoercivityConstraints D.measure C (weakGreenDomain D).spatial
      (sharpWeakPoincareDomain D) κ τ (O.firstState J t) := by
  have hc := O.first_constraints J W₀x W₀y hWx hWy hdeg ht
  exact ⟨hc.spatial, hc.zeroTrace, hc.polar⟩

/-- 原系统构造使用精确矩形常数的有限区间问题。空间/极化/迹约束不依赖
Poincaré 数值；只替换已由真实图闭包证明的估计，其余演化直接复用。 -/
def sharpFiniteProblem
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O J) :
    FiniteIntervalProblemConditional (weakGreenDomain D) C ε κ τ μ (sharpPoincareConstant D) T
      (fun v _ => weak_sharp_poincare_domain D v) where
  T_nonneg := O.nonneg_time
  path := O.sameSource J W₀x W₀y
  regular := O.spatialPath J W₀x W₀y
  base_evolution t ht := O.base_evolution J W₀x W₀y hWx hWy ht
  continuous_base := (O.states_continuous J W₀x W₀y).1
  continuous_first := (O.states_continuous J W₀x W₀y).2
  static_base t ht := O.sharp_base_constraints W₀x W₀y hWx hWy ht
  static_first t ht := O.sharp_first_constraints J W₀x W₀y hWx hWy hdeg ht

/-- (6.4) 的具体弱原系统能量。状态来自真实历史和同一原场的两次导数；
该命名入口直接复用 energy7，没有另设自由实数能量。 -/
def sharpEnergy (t : ℝ) : ℝ :=
  energy7 D.measure C ε κ τ μ (sharpPoincareConstant D) (O.sameSource J W₀x W₀y) t

/-- (7.8) 的具体耗散；P_t/P_tt 分别由 OriginalAt/OriginalJet 绑定。 -/
def sharpDissipation (t : ℝ) : ℝ :=
  dissipation7 D.measure C ε κ τ μ (sharpPoincareConstant D) (O.sameSource J W₀x W₀y) t

/-- (6.7) 的实际图范数平方，沿同一个原解的两层组合。 -/
def sharpGraphEnergySquare (t : ℝ) : ℝ :=
  graphSquare7 D.measure C ε κ μ (sharpPoincareConstant D) (O.sameSource J W₀x W₀y) t

/-- 全部交付结论的输出包，字段均为下面主定理证明的结论，绝非原解输入。
law 在内部，bounds/monotone/balance 含端点及退化区间。physical 控制输入原场。
空间耗散保留一半，Debye 平方项保留 μτ/(4κ)。 -/
structure SharpEnergyConclusions : Prop where
  bounds : ∀ t ∈ Icc 0 T,
    O.sharpGraphEnergySquare J W₀x W₀y t / 4 ≤ O.sharpEnergy J W₀x W₀y t ∧
    O.sharpEnergy J W₀x W₀y t ≤ O.sharpGraphEnergySquare J W₀x W₀y t
  law : ∀ t ∈ Ioo 0 T,
    HasDerivAt (O.sharpEnergy J W₀x W₀y) (-O.sharpDissipation J W₀x W₀y t) t ∧
    (fieldSpatialDissipation D.measure C (O.baseState W₀x W₀y t) +
      scaleK ε κ μ (sharpPoincareConstant D) * fieldSpatialDissipation D.measure C (O.firstState J t))/2 +
      μ*τ/(4*κ) * (‖(O.derivatives t).P‖^2 +
        scaleK ε κ μ (sharpPoincareConstant D) * ‖J.polarDDot t‖^2) ≤ O.sharpDissipation J W₀x W₀y t ∧
    0 ≤ O.sharpDissipation J W₀x W₀y t
  monotone : AntitoneOn (O.sharpEnergy J W₀x W₀y) (Icc 0 T)
  initial_bounds : ∀ t ∈ Icc 0 T,
    0 ≤ O.sharpEnergy J W₀x W₀y t ∧ O.sharpEnergy J W₀x W₀y t ≤ O.sharpEnergy J W₀x W₀y 0
  integrable : ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
    IntervalIntegrable (O.sharpDissipation J W₀x W₀y) volume t₁ t₂
  balance : ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
    O.sharpEnergy J W₀x W₀y t₂ + ∫ t in t₁..t₂, O.sharpDissipation J W₀x W₀y t = O.sharpEnergy J W₀x W₀y t₁
  physical : ∀ t ∈ Icc 0 T,
    ε * ‖(O.fields t).E‖^2 + μ * (‖(O.fields t).Hx‖^2 + ‖(O.fields t).Hy‖^2) +
      κ⁻¹ * ‖(O.fields t).P‖^2 ≤ (4/μ) * O.sharpEnergy J W₀x W₀y t
  physical_initial : ∀ t ∈ Icc 0 T,
    ε * ‖(O.fields t).E‖^2 + μ * (‖(O.fields t).Hx‖^2 + ‖(O.fields t).Hy‖^2) +
      κ⁻¹ * ‖(O.fields t).P‖^2 ≤ (4/μ) * O.sharpEnergy J W₀x W₀y 0

/-- V7 (6.7)–(6.10)：弱原八式、初始兼容与真实图路径推出全域先验定理。
输入中没有 Green/Poincaré、混合交换、全时段兼容或能量目标字段。
初始加权成员经已证历史识别进入同源路径；P_tt 连续兑现 FTC 的可积性。
采用 H₀¹/H(div) 图范数路径和已证 (5.1) 常数；仍不宣称已自动选择一般 W¹,∞ 连续代表。 -/
theorem main_energy_estimate_SharpWeakOriginal
    (hp : CoercivityParameters C ε κ τ μ (sharpPoincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O J) :
    SharpEnergyConclusions O J W₀x W₀y := by
  let problem := O.sharpFiniteProblem J W₀x W₀y hWx hWy hdeg
  have hmain := main_energy_estimate_Conditional (weakGreenDomain D) C ε κ τ μ
    (sharpPoincareConstant D) T hp (fun v _ => weak_sharp_poincare_domain D v) problem J.continuous_polarDDot
  refine ⟨?_, ?_, hmain.1, ?_, ?_, hmain.2.2.2, ?_, ?_⟩
  · intro t ht
    exact (hmain.2.2.1 t ht).1
  · intro t ht
    exact hmain.2.1 t ht
  · intro t ht
    exact (hmain.2.2.1 t ht).2.1
  · intro t₁ t₂ h₁ h₁₂ h₂
    exact intervalIntegrable_dissipation7_Conditional (weakGreenDomain D) C ε κ τ μ
      (sharpPoincareConstant D) T (fun v _ => weak_sharp_poincare_domain D v) problem J.continuous_polarDDot h₁ h₁₂ h₂
  · intro t ht
    have hcontrol := physicalControl_Conditional D.measure C ε κ τ μ (sharpPoincareConstant D) hp
      (weakGreenDomain D).spatial (sharpWeakPoincareDomain D) (O.sameSource J W₀x W₀y) t
      (problem.static_base t ht) (problem.static_first t ht)
    have hmagnetic := O.magnetic_reconstruction W₀x W₀y (ne_of_gt hp.μ_pos) ht
    have hphysical : ε * ‖(O.fields t).E‖^2 + μ *
        (‖reconstructHx μ (O.baseState W₀x W₀y t)‖^2 + ‖reconstructHy μ (O.baseState W₀x W₀y t)‖^2) +
        κ⁻¹ * ‖(O.fields t).P‖^2 ≤ (4/μ) * O.sharpEnergy J W₀x W₀y t := hcontrol.physical
    simpa only [hmagnetic.1, hmagnetic.2] using hphysical
  · intro t ht
    have hcontrol := (hmain.2.2.1 t ht).2.2.2.physical
    have hmagnetic := O.magnetic_reconstruction W₀x W₀y (ne_of_gt hp.μ_pos) ht
    change ε * ‖(O.fields t).E‖^2 + μ *
        (‖reconstructHx μ (O.baseState W₀x W₀y t)‖^2 + ‖reconstructHy μ (O.baseState W₀x W₀y t)‖^2) +
        κ⁻¹ * ‖(O.fields t).P‖^2 ≤ (4/μ) * O.sharpEnergy J W₀x W₀y 0 at hcontrol
    simpa only [hmagnetic.1, hmagnetic.2] using hcontrol

/-- (8.4)–(8.8) 的输出包；Z/Q 是输入八变量，不是未识别的重构槽。
B 是结论右端的能量值，下方分别取已定义的 E₇(t) 与 E₇(0)。 -/
structure SharpOriginalAuxiliaryBounds (B t : ℝ) : Prop where
  displacement : ‖(O.u t).val.val 0‖^2 ≤ 8*(sharpPoincareConstant D)^2*B
  auxiliary : ‖O.φx t‖^2 + ‖O.φy t‖^2 ≤ 4*B
  primitivePolar : ‖O.q t‖^2 ≤ (16*κ^2*(sharpPoincareConstant D)^2+8*κ*τ^2/μ)*B
  electricMemory : ‖(O.fields t).Z1‖^2 ≤ 8*ε^2*C.S^4*(sharpPoincareConstant D)^2*B
  polarMemory : ‖(O.fields t).Z2‖^2 ≤ C.S^4*(16*κ^2*(sharpPoincareConstant D)^2+8*κ*τ^2/μ)*B
  magneticAuxiliary : ‖(O.fields t).Qx‖^2+‖(O.fields t).Qy‖^2 ≤ 4*C.S^2*B

/-- 全部辅助控制直接接到弱原解；静态约束由已证兼容保持和图路径给出。
没有把目标界作为参数字段，使用原文常数 8、4、16、8。 -/
theorem sharp_original_auxiliary_control
    (hp : CoercivityParameters C ε κ τ μ (sharpPoincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O J) {t : ℝ} (ht : t ∈ Icc 0 T) :
    SharpOriginalAuxiliaryBounds O (O.sharpEnergy J W₀x W₀y t) t := by
  have hbounds := physicalControl_Conditional D.measure C ε κ τ μ (sharpPoincareConstant D) hp
    (weakGreenDomain D).spatial (sharpWeakPoincareDomain D) (O.sameSource J W₀x W₀y) t
    (O.sharp_base_constraints W₀x W₀y hWx hWy ht)
    (O.sharp_first_constraints J W₀x W₀y hWx hWy hdeg ht)
  dsimp only [sameSource] at hbounds
  have hident := O.auxiliary_reconstruction W₀x W₀y hWx hWy ht
  have hphysical := O.base_physical W₀x W₀y hWx hWy ht
  dsimp only [sharpEnergy, energy7, sameSource]
  refine ⟨hbounds.displacement, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hphysical.1,hphysical.2] using hbounds.auxiliary
  · simpa only [hident.1] using hbounds.primitivePolar
  · simpa only [hident.2.1] using hbounds.electricMemory
  · simpa only [hident.2.2.1] using hbounds.polarMemory
  · simpa only [hident.2.2.2.1,hident.2.2.2.2] using hbounds.magneticAuxiliary

/-- 由已证单调性把 (8.4)–(8.8) 的全部右端替换为初值能量。
先证明乘数非负，再使用序的传递；不是再次假设初值控制。 -/
theorem sharp_original_auxiliary_initial_control
    (hp : CoercivityParameters C ε κ τ μ (sharpPoincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O J) {t : ℝ} (ht : t ∈ Icc 0 T) :
    SharpOriginalAuxiliaryBounds O (O.sharpEnergy J W₀x W₀y 0) t := by
  have hbounds := O.sharp_original_auxiliary_control J W₀x W₀y hp hWx hWy hdeg ht
  have henergy := ((O.main_energy_estimate_SharpWeakOriginal J W₀x W₀y hp hWx hWy hdeg).initial_bounds t ht).2
  have hμ : 0 < μ := hp.μ_pos
  have hκ : 0 < κ := hp.κ_pos
  have hτ : 0 < τ := hp.τ_pos
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact hbounds.displacement.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  · exact hbounds.auxiliary.trans (mul_le_mul_of_nonneg_left henergy (by norm_num))
  · exact hbounds.primitivePolar.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  · exact hbounds.electricMemory.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  · exact hbounds.polarMemory.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  · exact hbounds.magneticAuxiliary.trans (mul_le_mul_of_nonneg_left henergy (by positivity))

end OriginalInterval

/-- 真正 Cᵏ 时间条件与原文 π 常数合流的入口。
正长度区间内导数由原式识别；端点槽识别仍是 ClosedCkRegularity 的明确条件。
所有 Green/Poincaré/能量目标在证明内部取得。一般 W¹,∞ 代表选择仍未由此解决。 -/
theorem ClosedCkRegularity.main_energy_sharp
    {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    {O : OriginalInterval D C ε κ τ μ T} (R : ClosedCkRegularity O) (hT : 0 < T)
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hp : CoercivityParameters C ε κ τ μ (sharpPoincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0) :
    OriginalInterval.SharpEnergyConclusions O (R.toTimeRegularity hT).toOriginalJet W₀x W₀y ∧
      ∀ t ∈ Icc 0 T, OriginalInterval.SharpOriginalAuxiliaryBounds O
        (O.sharpEnergy (R.toTimeRegularity hT).toOriginalJet W₀x W₀y 0) t := by
  have hdeg : DegenerateJetCompatibility O (R.toTimeRegularity hT).toOriginalJet :=
    ⟨fun hz => (hT.ne' hz).elim, fun hz => (hT.ne' hz).elim, fun hz => (hT.ne' hz).elim⟩
  exact ⟨O.main_energy_estimate_SharpWeakOriginal _ W₀x W₀y hp hWx hWy hdeg,
    fun t ht => O.sharp_original_auxiliary_initial_control _ W₀x W₀y hp hWx hWy hdeg ht⟩
end LeanPML.PML.Weak
