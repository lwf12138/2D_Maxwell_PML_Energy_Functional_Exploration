import LeanPML.PML.WeakCanonicalTime
import LeanPML.Rectangle.SharpParameterCertificate
import LeanPML.Examples.WeakCk

/-! 精确矩形常数下的非零弱静态原解调用。
旧非零解仍满足八式；仅更换已证明的 CP 和阈值证书，不另假设 PDE 结论。 -/
noncomputable section
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
open LeanPML.PML LeanPML.PML.Weak
namespace LeanPML.Examples.WeakStaticMode

/-- 旧实例 c 小于论文 c=1/128，故也满足原 π 常数下的阈值。 -/
def sharpParameters : CoercivityParameters coefficients 1 1 1 1 (sharpPoincareConstant unitSquare) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    sharpPoincareConstant_pos unitSquare,
    (by norm_num [coefficients,smallC,oldC] : coefficients.c ≤ oldC).trans original_parameters_threshold⟩

/-- 非零八变量弱解调用精确 CP 的主定理；包含 T=0 独立初始兼容。 -/
theorem sharp_main_call (T : ℝ) (hT : 0 ≤ T) :
    OriginalInterval.SharpEnergyConclusions (solution T hT) (jet T hT) 0 initialY := by
  apply (solution T hT).main_energy_estimate_SharpWeakOriginal (jet T hT) 0 initialY sharpParameters
  · simp only [map_zero,auxiliary_x]
  · rw [physical_initialY,auxiliary_y]
  · exact degenerate T hT

/-- 对正长度区间还实际调用 Cᵏ→jet→精确 CP 的合流入口。 -/
theorem sharp_closedCk_call (T : ℝ) (hT : 0 < T) :
    OriginalInterval.SharpEnergyConclusions (solution T hT.le)
      ((closedCkRegularity T hT.le).toTimeRegularity hT).toOriginalJet 0 initialY ∧
    ∀ t ∈ Icc 0 T, OriginalInterval.SharpOriginalAuxiliaryBounds (solution T hT.le)
      ((solution T hT.le).sharpEnergy
        ((closedCkRegularity T hT.le).toTimeRegularity hT).toOriginalJet 0 initialY 0) t := by
  apply (closedCkRegularity T hT.le).main_energy_sharp hT 0 initialY sharpParameters
  · simp only [map_zero,auxiliary_x]
  · rw [physical_initialY,auxiliary_y]

/-- 输入非零磁场在新主定理中得到真实 L² 控制，迫使新能量为正。 -/
theorem sharp_energy_pos (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    0 < (solution T hT).sharpEnergy (jet T hT) 0 initialY t := by
  have hcontrol := (sharp_main_call T hT).physical t ht
  have hnorm : 0 < ‖oneField‖ := norm_pos_iff.mpr oneField_ne_zero
  simp only [solution,state,norm_zero,norm_neg,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,inv_one,one_mul,zero_add,add_zero,div_one] at hcontrol
  change ‖oneField‖^2 ≤ 4*(solution T hT).sharpEnergy (jet T hT) 0 initialY t at hcontrol
  nlinarith [sq_pos_of_pos hnorm]
/-- 实际新弱主定理的能量入口恒定；不是另设一个自由常数能量。 -/
theorem sharp_energy_constant (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (solution T hT).sharpEnergy (jet T hT) 0 initialY t =
      (solution T hT).sharpEnergy (jet T hT) 0 initialY 0 := by
  unfold OriginalInterval.sharpEnergy energy7
  change twoLayerEnergy _ _ _ _ _ _ _ ((solution T hT).baseState 0 initialY t)
    ((solution T hT).firstState (jet T hT) t) = _
  rw [(states_constant T hT t).1,(states_constant T hT t).2]
  rfl

/-- 在内部时刻，真实主能量律与常值导数唯一性共同给出耗散为零。
因此正的静态能量不会严格递减；这不否定单调不增。 -/
theorem sharp_dissipation_zero (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    (solution T hT).sharpDissipation (jet T hT) 0 initialY t = 0 := by
  have hlaw := ((sharp_main_call T hT).law t ht).1
  have hconstant : HasDerivAt ((solution T hT).sharpEnergy (jet T hT) 0 initialY) 0 t := by
    have hfunction : (solution T hT).sharpEnergy (jet T hT) 0 initialY =
        fun _ => (solution T hT).sharpEnergy (jet T hT) 0 initialY 0 :=
      funext (sharp_energy_constant T hT)
    rw [hfunction]
    exact hasDerivAt_const t _
  exact neg_eq_zero.mp (hlaw.unique hconstant)

/-- 非零静态解回归的联合结论，准确使用内部耗散与全闭区间能量入口。 -/
theorem sharp_nonzero_static_regression (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    0 < (solution T hT).sharpEnergy (jet T hT) 0 initialY t ∧
    (solution T hT).sharpEnergy (jet T hT) 0 initialY t =
      (solution T hT).sharpEnergy (jet T hT) 0 initialY 0 ∧
    (solution T hT).sharpDissipation (jet T hT) 0 initialY t = 0 :=
  ⟨sharp_energy_pos T hT (Ioo_subset_Icc_self ht),sharp_energy_constant T hT t,sharp_dissipation_zero T hT ht⟩



/-- 不输入任何端点 jet 识别的正长度区间调用。
四个 Cᵏ 字段来自同一非零静态原解；原场与 canonicalInterval.fields 定义相同。 -/
def canonicalCore (T : ℝ) (hT : 0 ≤ T) : V7ClosedCkCore (solution T hT) :=
  let R := closedCkRegularity T hT
  ⟨R.u_graph,R.u_value,R.polar,R.flux⟩

theorem canonical_main_call (T : ℝ) (hT : 0 < T) :
    OriginalInterval.SharpEnergyConclusions
      (V7ClosedCkCore.canonicalInterval (O := solution T hT.le) hT)
      (((canonicalCore T hT.le).regularity hT).toTimeRegularity hT).toOriginalJet 0 initialY ∧
    ∀ t ∈ Icc 0 T, OriginalInterval.SharpOriginalAuxiliaryBounds
      (V7ClosedCkCore.canonicalInterval (O := solution T hT.le) hT)
      ((V7ClosedCkCore.canonicalInterval (O := solution T hT.le) hT).sharpEnergy
        (((canonicalCore T hT.le).regularity hT).toTimeRegularity hT).toOriginalJet 0 initialY 0) t := by
  apply (canonicalCore T hT.le).main_energy hT 0 initialY sharpParameters
  · simp only [map_zero,auxiliary_x]
  · rw [physical_initialY,auxiliary_y]
end LeanPML.Examples.WeakStaticMode
