import LeanPML.Examples.WeakStaticMode
import LeanPML.PML.WeakReverse
import LeanPML.PML.AuxiliaryOperatorMemory

/-! 本轮连接的非零调用：复用已证原八式的静态解，不将初值证书冒充演化解。 -/
noncomputable section
open Set MeasureTheory
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
open LeanPML.PML LeanPML.PML.Weak
namespace LeanPML.Examples.WeakStaticMode

/-- 从已证静态路径提取 (6.6) 所需正则性，明确不提供 λ_tt。 -/
def timeRegularity (T : ℝ) (hT : 0 ≤ T) : V7TimeRegularity (solution T hT) where
  electricDot := (jet T hT).electricDot
  fluxDot := (jet T hT).fluxDot
  electricDDot := (jet T hT).electricDDot
  polarDDot := (jet T hT).polarDDot
  electric_deriv := (jet T hT).electric_deriv
  flux_deriv := (jet T hT).flux_deriv
  electricDot_value := (jet T hT).electricDot_value
  electric_second := (jet T hT).electric_second
  polar_second := (jet T hT).polar_second
  continuous_electricDot := (jet T hT).continuous_electricDot
  continuous_fluxDot := (jet T hT).continuous_fluxDot
  continuous_polarDot := (jet T hT).continuous_polarDot
  continuous_polarDDot := (jet T hT).continuous_polarDDot

/-- 非零弱原解调用较少输入的新入口，包括原 Qx 的初值控制；T=0 也覆盖。
这里 φy、Hx、Qx 非零，故不是仅对零状态进行类型检查。 -/
theorem closeout_main_call (T : ℝ) (hT : 0 ≤ T) :
    OriginalInterval.EnergyConclusions (solution T hT) (timeRegularity T hT).toOriginalJet 0 initialY ∧
    ∀ t ∈ Icc 0 T, OriginalInterval.OriginalAuxiliaryBounds (solution T hT)
      ((solution T hT).energy (timeRegularity T hT).toOriginalJet 0 initialY 0) t := by
  apply (timeRegularity T hT).main_energy_and_auxiliary 0 initialY parameters
  · simp only [map_zero, auxiliary_x]
  · rw [physical_initialY, auxiliary_y]
  · exact ⟨(degenerate T hT).polar, (degenerate T hT).spatialX,
      (degenerate T hT).spatialY⟩

/-- 同一非零静态通量的 primitive 路径。所有时间导数为零；
辅助方程利用 r=0，而不是要求 λ 本身为零。 -/
def primitiveData (T : ℝ) : PrimitiveIntervalData unitSquare coefficients 1 1 1 1 T where
  u := fun _ => 0
  e := fun _ => 0
  flux := fun _ => flux
  fluxDot := fun _ => 0
  P := fun _ => 0
  q := fun _ => 0
  Edot := fun _ => 0
  Pdot := fun _ => 0
  hu := by
    intro t ht
    change HasDerivAt (fun _ : ℝ => (0 : zeroBoundaryGraph unitSquare)) 0 t
    exact hasDerivAt_const t (0 : zeroBoundaryGraph unitSquare)
  he t _ := hasDerivAt_const t _
  hflux t _ := hasDerivAt_const t _
  hP t _ := hasDerivAt_const t _
  hq t _ := hasDerivAt_const t _
  polar := by intros; simp
  auxiliaryX := by
    intro t ht
    simpa using (hasDerivAt_const t (0 : ScalarL2 unitSquare.measure))
  auxiliaryY := by
    intro t ht
    simpa using (hasDerivAt_const t oneField)
  main := by intros; simp

/-- 非零 primitive 路径实际调用八式反向证明；不以代数检查代替求导。 -/
theorem reverse_static_call (T : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    OriginalAt unitSquare coefficients 1 1 1 1
      (reverseFields unitSquare coefficients 1 1 (primitiveData T).u (primitiveData T).e
        (primitiveData T).flux (primitiveData T).P (primitiveData T).q)
      (reverseDerivatives unitSquare coefficients 1 1 ((primitiveData T).e t)
        ((primitiveData T).fluxDot t) ((primitiveData T).P t)
        ((primitiveData T).Edot t) ((primitiveData T).Pdot t))
      t ((primitiveData T).e t) ((primitiveData T).flux t) :=
  primitive_to_original_WeakOn (primitiveData T) (by norm_num) t ht

/-- 非零 y 加权分量调用空间值指数核；同时检查 x/y 交换。 -/
theorem kernel_static_call (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (solution T hT).weightedX 0 t = coefficients.exponentialHistory unitSquare.measure 0
      (fun s => ((solution T hT).u s).val.val 1) t ∧
    (solution T hT).weightedY initialY t = weightedCongr unitSquare.measure coefficients.swap_wx_eq_wy
      (coefficients.swap.exponentialHistory unitSquare.measure initialY
        (fun s => ((solution T hT).u s).val.val 2) t) := by
  apply (solution T hT).operator_memory_both 0 initialY
  · simp only [map_zero, auxiliary_x]
  · rw [physical_initialY, auxiliary_y]
  · exact ht
end LeanPML.Examples.WeakStaticMode
