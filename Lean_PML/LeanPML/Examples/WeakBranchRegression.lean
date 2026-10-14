import LeanPML.PML.MainWeakRectangle
import LeanPML.PML.WeakRegionalAbsorption

/-!
# 弱原系统主定理的四种吸收分支调用

这里实际构造八变量零解、H₀¹/H(div) 图路径及真实时间导数，再调用
`main_energy_estimate_WeakOriginal`。原方程只在 (0,T) 使用，T=0 也保留。
这些是接口退化回归，不代替另一个文件的非零静态解。
系数来自区域 W¹,∞ 推荐入口；材料沿用 C_P=4、K=384 的精确证书。
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Time
open LeanPML.PML LeanPML.PML.Weak
namespace LeanPML.Examples.WeakBranchRegression

/-- 八个实际 L² 商类均为零；不是把能量或方程结论放入状态字段。 -/
def zeroOriginalState (D : Rect) : OriginalState D :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- 任意合法吸收系数下的原八式零解。空间域成员是实际图空间的零元；
每个时间导数由 mathlib 的常值函数求导得到，初始兼容仅在 t=0 验证。 -/
def zeroInterval (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ε κ τ μ T : ℝ) (hT : 0 ≤ T) : OriginalInterval D C ε κ τ μ T where
  nonneg_time := hT
  fields := fun _ => zeroOriginalState D
  derivatives := fun _ => zeroOriginalState D
  electric := fun _ => 0
  flux := fun _ => 0
  u₀ := 0
  q₀ := 0
  continuous_fields := ⟨continuousOn_const, continuousOn_const, continuousOn_const,
    continuousOn_const, continuousOn_const, continuousOn_const, continuousOn_const,
    continuousOn_const⟩
  continuous_electric := continuousOn_const
  continuous_flux := continuousOn_const
  electric_value := by intros; rfl
  flux_x := by intros; simp [zeroOriginalState]
  flux_y := by intros; simp [zeroOriginalState]
  equations := by
    intro t ht
    constructor
    · exact ⟨hasDerivAt_const t 0, hasDerivAt_const t 0, hasDerivAt_const t 0,
        hasDerivAt_const t 0, hasDerivAt_const t 0, hasDerivAt_const t 0,
        hasDerivAt_const t 0, hasDerivAt_const t 0⟩
    all_goals simp [zeroOriginalState]
  initial_compatible := by
    intro i
    fin_cases i <;> simp [invariants, historyU, historyQ, banachHistory,
      phiX, phiY, zeroOriginalState]

/-- 同一零解的真实导数层，所有图空间及 L² 导数均实际检查。
本构造没有输入导数层 PDE、全时段兼容或能量恒等式。 -/
def zeroJet (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ε κ τ μ T : ℝ) (hT : 0 ≤ T) : OriginalJet (zeroInterval D C ε κ τ μ T hT) where
  electricDot := fun _ => 0
  fluxDot := fun _ => 0
  electricDDot := fun _ => 0
  polarDDot := fun _ => 0
  fluxDDotX := fun _ => 0
  fluxDDotY := fun _ => 0
  electric_deriv := by
    intro t ht
    exact hasDerivAt_const t (0 : zeroBoundaryGraph D)
  flux_deriv := by
    intro t ht
    exact hasDerivAt_const t (0 : weakHDivGraph D)
  electricDot_value := by intros; rfl
  electric_second := by
    intro t ht
    exact hasDerivAt_const t (0 : ScalarL2 D.measure)
  polar_second := by
    intro t ht
    exact hasDerivAt_const t (0 : ScalarL2 D.measure)
  flux_second_x := by
    intro t ht
    exact hasDerivAt_const t (0 : ScalarL2 D.measure)
  flux_second_y := by
    intro t ht
    exact hasDerivAt_const t (0 : ScalarL2 D.measure)
  continuous_electricDot := continuousOn_const
  continuous_fluxDot := continuousOn_const
  continuous_polarDot := continuousOn_const
  continuous_polarDDot := continuousOn_const

/-- T=0 的导数层兼容由具体零数据核验，绝不从空的内部方程推出。 -/
theorem zero_degenerate (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ε κ τ μ T : ℝ) (hT : 0 ≤ T) :
    DegenerateJetCompatibility (zeroInterval D C ε κ τ μ T hT)
      (zeroJet D C ε κ τ μ T hT) := by
  constructor <;> intro hzero <;>
    simp [zeroInterval, zeroJet, zeroOriginalState, OriginalInterval.u, historyU, banachHistory]

/-- 两个初始加权零元恢复为原物理辅助场；不借助吸收严格正或除以 a。 -/
theorem zero_initial_weighted (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ε κ τ μ T : ℝ) (hT : 0 ≤ T) :
    physicalL2 D.measure C.wx C.wx_measurable C.wx_gap 0 =
      (zeroInterval D C ε κ τ μ T hT).φx 0 ∧
    physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap 0 =
      (zeroInterval D C ε κ τ μ T hT).φy 0 := by
  simp [OriginalInterval.φx, OriginalInterval.φy, phiX, phiY, OriginalInterval.u,
    zeroInterval, zeroOriginalState, historyU, banachHistory]

open LeanPML.Rectangle.ParameterCertificate

/-- 原始材料正性及 c≤c_* 来自实际 unitSquare 保守常数证书。
四个分支只改变 p/r 是否为零，使用同一 c、S、K。 -/
theorem configuration_parameters (xActive yActive : Bool) :
    CoercivityParameters
      (WeakRegionalAbsorption.certificateConfiguration xActive yActive).spatial
      1 1 1 1 (poincareConstant unitSquare) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    poincareConstant_pos unitSquare, ?_⟩
  exact WeakRegionalAbsorption.certificate_threshold xActive yActive

/-- V7 (6.7)–(6.10) 的真实弱主定理在每个布尔吸收分支上的正式调用。
输出包含图范数界、真实求导、定量耗散、单调性、积分平衡及原场 L² 控制；
这些结论全部由主定理产生，不作为零解结构的字段。 -/
theorem configuration_main (xActive yActive : Bool) (T : ℝ) (hT : 0 ≤ T) :
    let C := (WeakRegionalAbsorption.certificateConfiguration xActive yActive).spatial
    let O := zeroInterval unitSquare C 1 1 1 1 T hT
    OriginalInterval.EnergyConclusions O (zeroJet unitSquare C 1 1 1 1 T hT) 0 0 := by
  dsimp only
  have hphysical := zero_initial_weighted unitSquare
    (WeakRegionalAbsorption.certificateConfiguration xActive yActive).spatial 1 1 1 1 T hT
  exact OriginalInterval.main_energy_estimate_WeakOriginal _ _ 0 0
    (configuration_parameters xActive yActive) hphysical.1 hphysical.2
    (zero_degenerate _ _ 1 1 1 1 T hT)

/-- 显式列出四种实际主定理调用，包含两个方向不对称的单向边层。
T 可以为零；四种配置的域内系数取值另由 certificate_four_branches 核验。 -/
theorem all_four_configurations (T : ℝ) (hT : 0 ≤ T) :
    (let C := (WeakRegionalAbsorption.certificateConfiguration false false).spatial
     let O := zeroInterval unitSquare C 1 1 1 1 T hT
     OriginalInterval.EnergyConclusions O (zeroJet unitSquare C 1 1 1 1 T hT) 0 0) ∧
    (let C := (WeakRegionalAbsorption.certificateConfiguration true false).spatial
     let O := zeroInterval unitSquare C 1 1 1 1 T hT
     OriginalInterval.EnergyConclusions O (zeroJet unitSquare C 1 1 1 1 T hT) 0 0) ∧
    (let C := (WeakRegionalAbsorption.certificateConfiguration false true).spatial
     let O := zeroInterval unitSquare C 1 1 1 1 T hT
     OriginalInterval.EnergyConclusions O (zeroJet unitSquare C 1 1 1 1 T hT) 0 0) ∧
    (let C := (WeakRegionalAbsorption.certificateConfiguration true true).spatial
     let O := zeroInterval unitSquare C 1 1 1 1 T hT
     OriginalInterval.EnergyConclusions O (zeroJet unitSquare C 1 1 1 1 T hT) 0 0) :=
  ⟨configuration_main false false T hT, configuration_main true false T hT,
    configuration_main false true T hT, configuration_main true true T hT⟩

end LeanPML.Examples.WeakBranchRegression
