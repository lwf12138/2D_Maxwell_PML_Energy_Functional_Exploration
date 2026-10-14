import LeanPML.PML.WeakFiniteProblem

/-!
# 矩形弱图空间兼容解类的全域先验能量定理

对应 V7 (6.7)–(6.10)。输入是真实原八变量、原式、PEC/H₀¹、初始兼容、
图范数/L² 时间正则性及初始加权成员。所有弱空间分析接口在证明内部构造。
空间不再要求联合 C∞；时间正则性准确列在 OriginalInterval、OriginalJet 中。
保守 C_P=2Lx 与阈值匹配，不声称最优 π 常数或一般解存在唯一性。
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

/-- (6.4) 的具体弱原系统能量。状态来自真实历史和同一原场的两次导数；
该命名入口直接复用 energy7，没有另设自由实数能量。 -/
def energy (t : ℝ) : ℝ :=
  energy7 D.measure C ε κ τ μ (poincareConstant D) (O.sameSource J W₀x W₀y) t

/-- (7.8) 的具体耗散；P_t/P_tt 分别由 OriginalAt/OriginalJet 绑定。 -/
def dissipation (t : ℝ) : ℝ :=
  dissipation7 D.measure C ε κ τ μ (poincareConstant D) (O.sameSource J W₀x W₀y) t

/-- (6.7) 的实际图范数平方，沿同一个原解的两层组合。 -/
def graphEnergySquare (t : ℝ) : ℝ :=
  graphSquare7 D.measure C ε κ μ (poincareConstant D) (O.sameSource J W₀x W₀y) t

/-- 原磁场等于能量框架中的重构场；μ≠0 用于唯一一次标量约分。
这里结论是输入 Hx/Hy 的实际 L² 商类，避免只控制没有识别的重构坐标。 -/
theorem magnetic_reconstruction (hμ : μ ≠ 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    reconstructHx μ (O.baseState W₀x W₀y t) = (O.fields t).Hx ∧
    reconstructHy μ (O.baseState W₀x W₀y t) = (O.fields t).Hy := by
  change (-μ⁻¹) • (O.flux t).val 1 = _ ∧ μ⁻¹ • (O.flux t).val 0 = _
  rw [O.flux_x t ht, O.flux_y t ht]
  constructor <;> simp [smul_smul, hμ]

/-- 全部交付结论的输出包，字段均为下面主定理证明的结论，绝非原解输入。
law 在内部，bounds/monotone/balance 含端点及退化区间。physical 控制输入原场。
空间耗散保留一半，Debye 平方项保留 μτ/(4κ)。 -/
structure EnergyConclusions : Prop where
  bounds : ∀ t ∈ Icc 0 T,
    O.graphEnergySquare J W₀x W₀y t / 4 ≤ O.energy J W₀x W₀y t ∧
    O.energy J W₀x W₀y t ≤ O.graphEnergySquare J W₀x W₀y t
  law : ∀ t ∈ Ioo 0 T,
    HasDerivAt (O.energy J W₀x W₀y) (-O.dissipation J W₀x W₀y t) t ∧
    (fieldSpatialDissipation D.measure C (O.baseState W₀x W₀y t) +
      scaleK ε κ μ (poincareConstant D) * fieldSpatialDissipation D.measure C (O.firstState J t))/2 +
      μ*τ/(4*κ) * (‖(O.derivatives t).P‖^2 +
        scaleK ε κ μ (poincareConstant D) * ‖J.polarDDot t‖^2) ≤ O.dissipation J W₀x W₀y t ∧
    0 ≤ O.dissipation J W₀x W₀y t
  monotone : AntitoneOn (O.energy J W₀x W₀y) (Icc 0 T)
  initial_bounds : ∀ t ∈ Icc 0 T,
    0 ≤ O.energy J W₀x W₀y t ∧ O.energy J W₀x W₀y t ≤ O.energy J W₀x W₀y 0
  integrable : ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
    IntervalIntegrable (O.dissipation J W₀x W₀y) volume t₁ t₂
  balance : ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
    O.energy J W₀x W₀y t₂ + ∫ t in t₁..t₂, O.dissipation J W₀x W₀y t = O.energy J W₀x W₀y t₁
  physical : ∀ t ∈ Icc 0 T,
    ε * ‖(O.fields t).E‖^2 + μ * (‖(O.fields t).Hx‖^2 + ‖(O.fields t).Hy‖^2) +
      κ⁻¹ * ‖(O.fields t).P‖^2 ≤ (4/μ) * O.energy J W₀x W₀y t
  physical_initial : ∀ t ∈ Icc 0 T,
    ε * ‖(O.fields t).E‖^2 + μ * (‖(O.fields t).Hx‖^2 + ‖(O.fields t).Hy‖^2) +
      κ⁻¹ * ‖(O.fields t).P‖^2 ≤ (4/μ) * O.energy J W₀x W₀y 0

/-- V7 (6.7)–(6.10)：弱原八式、初始兼容与真实图路径推出全域先验定理。
输入中没有 Green/Poincaré、混合交换、全时段兼容或能量目标字段。
初始加权成员经已证历史识别进入同源路径；P_tt 连续兑现 FTC 的可积性。
当前采用 H₀¹/H(div) 图范数路径和保守 2Lx，精确范围见输入结构，不宣称适定性。 -/
theorem main_energy_estimate_WeakOriginal
    (hp : CoercivityParameters C ε κ τ μ (poincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O J) :
    EnergyConclusions O J W₀x W₀y := by
  let problem := O.finiteProblem J W₀x W₀y hWx hWy hdeg
  have hmain := main_energy_estimate_Conditional (weakGreenDomain D) C ε κ τ μ
    (poincareConstant D) T hp (fun v _ => weak_poincare_domain D v) problem J.continuous_polarDDot
  refine ⟨?_, ?_, hmain.1, ?_, ?_, hmain.2.2.2, ?_, ?_⟩
  · intro t ht
    exact (hmain.2.2.1 t ht).1
  · intro t ht
    exact hmain.2.1 t ht
  · intro t ht
    exact (hmain.2.2.1 t ht).2.1
  · intro t₁ t₂ h₁ h₁₂ h₂
    exact intervalIntegrable_dissipation7_Conditional (weakGreenDomain D) C ε κ τ μ
      (poincareConstant D) T (fun v _ => weak_poincare_domain D v) problem J.continuous_polarDDot h₁ h₁₂ h₂
  · intro t ht
    have hcontrol := physicalControl_Conditional D.measure C ε κ τ μ (poincareConstant D) hp
      (weakGreenDomain D).spatial (weakPoincareDomain D) (O.sameSource J W₀x W₀y) t
      (problem.static_base t ht) (problem.static_first t ht)
    have hmagnetic := O.magnetic_reconstruction W₀x W₀y (ne_of_gt hp.μ_pos) ht
    have hphysical : ε * ‖(O.fields t).E‖^2 + μ *
        (‖reconstructHx μ (O.baseState W₀x W₀y t)‖^2 + ‖reconstructHy μ (O.baseState W₀x W₀y t)‖^2) +
        κ⁻¹ * ‖(O.fields t).P‖^2 ≤ (4/μ) * O.energy J W₀x W₀y t := hcontrol.physical
    simpa only [hmagnetic.1, hmagnetic.2] using hphysical
  · intro t ht
    have hcontrol := (hmain.2.2.1 t ht).2.2.2.physical
    have hmagnetic := O.magnetic_reconstruction W₀x W₀y (ne_of_gt hp.μ_pos) ht
    change ε * ‖(O.fields t).E‖^2 + μ *
        (‖reconstructHx μ (O.baseState W₀x W₀y t)‖^2 + ‖reconstructHy μ (O.baseState W₀x W₀y t)‖^2) +
        κ⁻¹ * ‖(O.fields t).P‖^2 ≤ (4/μ) * O.energy J W₀x W₀y 0 at hcontrol
    simpa only [hmagnetic.1, hmagnetic.2] using hcontrol

end OriginalInterval
end LeanPML.PML.Weak
