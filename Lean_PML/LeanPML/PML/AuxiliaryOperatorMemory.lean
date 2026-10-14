import LeanPML.Analysis.OperatorMemory
import LeanPML.PML.AuxiliaryWeightedEvolution
import LeanPML.PML.WeakPathAssembly

/-!
# (5.7) 的加权空间算子指数版本

核是实际有界吸收乘子 M_p 的 exp((s−t)M_p)，在真正的 WeightedL2 中积分。
它与旧 auxiliaryWeightedHistory 相等，后者已与普通 L² 原辅助场识别。
本文件证明商类等式；不声称得到一个对所有时间同时有效的点值代表。
-/
noncomputable section
set_option maxRecDepth 2048
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1600000
open MeasureTheory Set
open LeanPML.Analysis
namespace LeanPML.PML.SpatialAbsorption
variable {α : Type*} [MeasurableSpace α] [Nonempty α]

local instance weightedComplete (ν : Measure α) (C : SpatialAbsorption α) :
    CompleteSpace (WeightedL2 ν C.wx) := weighted_completeSpace ν C.wx C.wx_measurable

/-- 有界吸收系数 p 的加权乘子；能量权重 w 自身没有成为有界乘子。 -/
def dampingOperator (ν : Measure α) (C : SpatialAbsorption α) :
    WeightedL2 ν C.wx →L[ℝ] WeightedL2 ν C.wx :=
  weightedMul ν C.wx C.pCoeff.value C.pCoeff.measurable C.pCoeff.bound C.pCoeff.abs_le

/-- (5.7) 实际空间值版本：在给定 t 的加权商类中，旧历史等于指数核 Bochner 积分。
连续普通场与原辅助 ODE 先给出加权历史，故没有预设全时段加权成员。
x方向取 C，y方向取 C.swap，从而阻尼系数和强迫差值均自动交换。 -/
theorem auxiliary_operator_memory
    (ν : Measure α) (C : SpatialAbsorption α) (W₀ : WeightedL2 ν C.wx)
    (φ h l : ℝ → ScalarL2 ν) (T : ℝ)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (hinitial : physicalL2 ν C.wx C.wx_measurable C.wx_gap W₀ = φ 0)
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt φ (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (l s)) s)
    (hspace : ∀ s ∈ Icc 0 T, l s = h s + φ s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s => (dampingKernel (C.dampingOperator ν) (s-t))
      (C.differenceLift ν (h s))) volume 0 t ∧
    C.auxiliaryWeightedHistory ν W₀ h l t =
      (dampingKernel (C.dampingOperator ν) (-t)) W₀ +
      ∫ s in (0 : ℝ)..t, (dampingKernel (C.dampingOperator ν) (s-t))
        (C.differenceLift ν (h s)) := by
  letI : CompleteSpace (WeightedL2 ν C.wx) := weighted_completeSpace ν C.wx C.wx_measurable
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hcontinuous := C.continuousOn_auxiliaryWeightedHistory ν W₀ h l T hT hh hl
  have hforcing := (C.differenceLift ν).continuous.comp_continuousOn hh
  have hderiv := fun s hs => C.hasDerivAt_auxiliaryWeightedHistory_damped ν W₀ φ h l T s
    hφ hh hl hinitial hODE (hspace s (Ioo_subset_Icc_self hs)) hs
  have hformula := operator_memory_formula (C.dampingOperator ν)
    (C.auxiliaryWeightedHistory ν W₀ h l) (fun s => C.differenceLift ν (h s))
    hcontinuous hforcing hderiv ht
  simpa only [C.auxiliaryWeightedHistory_initial, dampingKernel] using hformula

/-- (5.7) 的空间值指数核命名入口；合法性由 auxiliary_operator_memory 给出。 -/
def exponentialHistory (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (h : ℝ → ScalarL2 ν) (t : ℝ) :=
  (dampingKernel (C.dampingOperator ν) (-t)) W₀ +
    ∫ s in (0 : ℝ)..t, (dampingKernel (C.dampingOperator ν) (s-t)) (C.differenceLift ν (h s))
end LeanPML.PML.SpatialAbsorption

namespace LeanPML.PML.Weak.OriginalInterval
open LeanPML.Rectangle
/-- 原八式实际调用两个方向的 (5.7) 空间值公式。
空间关系、普通 L² 演化及连续性均取自已有原解证明，不新增辅助 ODE 假设。
等式逐时刻在加权商类中成立；不宣称同一个空间零测集适用于所有时刻。 -/
theorem operator_memory_both
    {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (O : OriginalInterval D C ε κ τ μ T)
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    O.weightedX W₀x t = C.exponentialHistory D.measure W₀x (fun s => (O.u s).val.val 1) t ∧
    O.weightedY W₀y t = weightedCongr D.measure C.swap_wx_eq_wy
      (C.swap.exponentialHistory D.measure W₀y (fun s => (O.u s).val.val 2) t) := by
  constructor
  · exact (C.auxiliary_operator_memory D.measure W₀x O.φx
      (fun s => (O.u s).val.val 1) (fun s => (O.flux s).val 0) T
      O.continuous_history.2.1
      ((zeroCoordinate D 1).continuous.comp_continuousOn O.continuous_history.1)
      ((weakHDivCoordinate D 0).continuous.comp_continuousOn O.continuous_flux)
      hWx (fun s hs => (O.auxiliary_hasDerivAt hs).1)
      (fun s hs => (O.spatial hs).1) ht).2
  · apply congrArg (weightedCongr D.measure C.swap_wx_eq_wy)
    exact (C.swap.auxiliary_operator_memory D.measure W₀y O.φy
      (fun s => (O.u s).val.val 2) (fun s => (O.flux s).val 1) T
      O.continuous_history.2.2
      ((zeroCoordinate D 2).continuous.comp_continuousOn O.continuous_history.1)
      ((weakHDivCoordinate D 1).continuous.comp_continuousOn O.continuous_flux)
      hWy (fun s hs => (O.auxiliary_hasDerivAt hs).2)
      (fun s hs => (O.spatial hs).2) ht).2
end LeanPML.PML.Weak.OriginalInterval
