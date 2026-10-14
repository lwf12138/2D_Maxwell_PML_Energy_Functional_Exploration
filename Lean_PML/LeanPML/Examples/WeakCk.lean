import LeanPML.PML.WeakCkRegularity
import LeanPML.Examples.WeakCloseout

/-! 非零弱静态原解调用真正 ContDiffOn 入口；只限正长度区间。
旧入口的 T=0 回归保持不变，本例不以空内部方程证明任意端点 jet 相容。 -/
noncomputable section
open Set MeasureTheory
open LeanPML.Analysis LeanPML.Rectangle LeanPML.PML LeanPML.PML.Weak
namespace LeanPML.Examples.WeakStaticMode

/-- 本静态原解的真实 Cᵏ 正则性及端点导数识别，全部由常值路径证明。
通量、磁场和 y 辅助场非零；u=E=P=0 不使整个原状态为零。 -/
def closedCkRegularity (T : ℝ) (hT : 0 ≤ T) : ClosedCkRegularity (solution T hT) where
  u_graph := by
    have hzero : (solution T hT).u = fun _ => 0 := funext (history_u T hT)
    rw [hzero]
    exact contDiffOn_const
  u_value := by
    have hzero : (fun t => ((solution T hT).u t).val.val 0) =
        fun _ => (0 : ScalarL2 ParameterCertificate.unitSquare.measure) := by
      funext t
      rw [history_u]
      rfl
    rw [hzero]
    exact contDiffOn_const
  polar := contDiffOn_const
  flux := contDiffOn_const
  electric_endpoint := by intros; simp [solution, state, zeroState, derivWithin_const]
  polar_endpoint := by intros; simp [solution, state, zeroState, derivWithin_const]

/-- 非零原解实际调用 Cᵏ→真实 jet→能量主定理，没有重新输入 λ_tt。
保守 Poincaré 参数仍复用已证 parameters。 -/
theorem closedCk_main_call (T : ℝ) (hT : 0 < T) :
    OriginalInterval.EnergyConclusions (solution T hT.le)
      ((closedCkRegularity T hT.le).toTimeRegularity hT).toOriginalJet 0 initialY ∧
    ∀ t ∈ Icc 0 T, OriginalInterval.OriginalAuxiliaryBounds (solution T hT.le)
      ((solution T hT.le).energy ((closedCkRegularity T hT.le).toTimeRegularity hT).toOriginalJet
        0 initialY 0) t := by
  apply (closedCkRegularity T hT.le).main_energy_from_closedCk hT 0 initialY parameters
  · simp only [map_zero, auxiliary_x]
  · rw [physical_initialY, auxiliary_y]
end LeanPML.Examples.WeakStaticMode
