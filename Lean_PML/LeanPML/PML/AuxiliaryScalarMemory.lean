import LeanPML.Analysis.MultiplierExponential
import LeanPML.PML.AuxiliaryOperatorMemory

/-!
# V7 (5.7)：标量指数核的实际空间值记忆公式

复用旧加权历史和真实原辅助 ODE；只补算子核→标量乘子的识别。
积分仍是 Bochner 时间积分，包含可积性证明，不从点态公式跳过空间可积性。
x 方向用 p 阻尼、(r−p)∂xu 强迫；y 方向用 C.swap。
原文的时间不变差值因子放在积分内部，是同一个标量核。
-/
noncomputable section
open MeasureTheory Set
open LeanPML.Analysis
namespace LeanPML.PML.SpatialAbsorption
variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/-- (5.7) 的标量指数核，平方根坐标为 exp(tp(x))X(x)。
这是有界吸收乘法，不是无界能量权重乘法。 -/
def scalarKernel (ν : Measure α) (C : SpatialAbsorption α) (t : ℝ) :=
  scalarExpMultiplier ν C.wx C.pCoeff.value C.pCoeff.measurable
    C.pCoeff.bound C.pCoeff.abs_le t

/-- 已证算子指数与论文标量核相同；后续历史表示实际调用本等式。 -/
theorem dampingKernel_eq_scalarKernel (ν : Measure α) (C : SpatialAbsorption α) (t : ℝ) :
    dampingKernel (C.dampingOperator ν) t = C.scalarKernel ν t :=
  dampingKernel_eq_scalarExpMultiplier ν C.wx C.pCoeff.value C.wx_measurable
    C.pCoeff.measurable C.pCoeff.bound C.pCoeff.abs_le t

/-- 标量指数核记忆表达式；其可积性和与原历史的相等由下条定理证明。
强迫 differenceLift 是已证 g↦(r−p)g 的普通 L² 到加权空间映射。 -/
def scalarMemory (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (h : ℝ → ScalarL2 ν) (t : ℝ) :=
  C.scalarKernel ν (-t) W₀ +
    ∫ s in (0 : ℝ)..t, C.scalarKernel ν (s-t) (C.differenceLift ν (h s))

/-- 旧历史和新表达完全相等；只是已证明核识别的代入，不是第二套独立模型。 -/
theorem exponentialHistory_eq_scalarMemory (ν : Measure α) (C : SpatialAbsorption α)
    (W₀ : WeightedL2 ν C.wx) (h : ℝ → ScalarL2 ν) (t : ℝ) :
    C.exponentialHistory ν W₀ h t = C.scalarMemory ν W₀ h t := by
  simp only [exponentialHistory, scalarMemory, C.dampingKernel_eq_scalarKernel]

/-- (5.7) 的真实加权空间公式和可积性。
输入仍为普通场连续性、真实 ODE、初始加权成员及空间关系；没有预设传播结果。
固定时间 t 的商类等式包含零区和零阻尼。 -/
theorem auxiliary_scalar_memory
    (ν : Measure α) (C : SpatialAbsorption α) (W₀ : WeightedL2 ν C.wx)
    (φ h l : ℝ → ScalarL2 ν) (T : ℝ)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (hinitial : physicalL2 ν C.wx C.wx_measurable C.wx_gap W₀ = φ 0)
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt φ (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (l s)) s)
    (hspace : ∀ s ∈ Icc 0 T, l s = h s + φ s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s => C.scalarKernel ν (s-t) (C.differenceLift ν (h s))) volume 0 t ∧
    C.auxiliaryWeightedHistory ν W₀ h l t = C.scalarMemory ν W₀ h t := by
  simpa only [C.dampingKernel_eq_scalarKernel, scalarMemory] using
    C.auxiliary_operator_memory ν W₀ φ h l T hφ hh hl hinitial hODE hspace ht

/-- 给定时间的物理代表公式：核恢复为 exp(tp) 乘原辅助场。
这是每个 t 各自的 a.e. 等式，不宣称一个空间零测集对所有 t 通用。 -/
theorem scalarKernel_physical_ae (ν : Measure α) (C : SpatialAbsorption α)
    (t : ℝ) (W : WeightedL2 ν C.wx) :
    ⇑(physicalL2 ν C.wx C.wx_measurable C.wx_gap (C.scalarKernel ν t W)) =ᵐ[ν]
      fun x => Real.exp (t * C.p x) * (physicalL2 ν C.wx C.wx_measurable C.wx_gap W) x := by
  rw [scalarKernel, physical_scalarExpMultiplier]
  exact coeFn_boundedMul ν _ _ _ _ _

/-- 普通 L² 的指数核乘子：用于直接表示输入原辅助场，而非只表示平方根坐标。 -/
def scalarKernelL2 (ν : Measure α) (C : SpatialAbsorption α) (t : ℝ) :=
  boundedMul ν (fun x => Real.exp (t * C.pCoeff.value x))
    ((measurable_const.mul C.pCoeff.measurable).exp)
    (Real.exp (|t| * C.pCoeff.bound))
    (exp_multiplier_bound C.pCoeff.value C.pCoeff.bound C.pCoeff.abs_le t)

/-- 物理恢复与标量指数核交换；后续合法地将连续线性恢复映射移过 Bochner 积分。 -/
theorem physical_scalarKernel (ν : Measure α) (C : SpatialAbsorption α)
    (t : ℝ) (W : WeightedL2 ν C.wx) :
    physicalL2 ν C.wx C.wx_measurable C.wx_gap (C.scalarKernel ν t W) =
      C.scalarKernelL2 ν t (physicalL2 ν C.wx C.wx_measurable C.wx_gap W) :=
  physical_scalarExpMultiplier ν C.wx C.pCoeff.value C.wx_measurable C.wx_gap
    C.pCoeff.measurable C.pCoeff.bound C.pCoeff.abs_le t W

/-- (5.7) 直接写成原普通 L² 辅助场的公式，强迫为 (r−p)∂iu。
可积性来自已证加权历史再经连续嵌入；无需任意代表元的逐点时间可导性。
与原文只差把固定空间系数置于时间积分内的写法。 -/
theorem auxiliary_scalar_memory_physical
    (ν : Measure α) (C : SpatialAbsorption α) (W₀ : WeightedL2 ν C.wx)
    (φ h l : ℝ → ScalarL2 ν) (T : ℝ)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (hinitial : physicalL2 ν C.wx C.wx_measurable C.wx_gap W₀ = φ 0)
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt φ (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (l s)) s)
    (hspace : ∀ s ∈ Icc 0 T, l s = h s + φ s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s => C.scalarKernelL2 ν (s-t)
      (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (h s))) volume 0 t ∧
    φ t = C.scalarKernelL2 ν (-t) (φ 0) +
      ∫ s in (0 : ℝ)..t, C.scalarKernelL2 ν (s-t)
        (C.rCoeff.operator ν (h s) - C.pCoeff.operator ν (h s)) := by
  letI : CompleteSpace (WeightedL2 ν C.wx) := weighted_completeSpace ν C.wx C.wx_measurable
  let recovery := physicalL2 ν C.wx C.wx_measurable C.wx_gap
  have hmemory := C.auxiliary_scalar_memory ν W₀ φ h l T hφ hh hl hinitial hODE hspace ht
  have hphysical := C.physical_auxiliaryWeightedHistory ν W₀ φ h l T
    hφ hh hl hinitial hODE ht
  have hcommute := recovery.intervalIntegral_comp_comm hmemory.1
  have hint : IntervalIntegrable (fun s => recovery
      (C.scalarKernel ν (s-t) (C.differenceLift ν (h s)))) volume 0 t :=
    ⟨recovery.integrable_comp hmemory.1.1, recovery.integrable_comp hmemory.1.2⟩
  have heq := congrArg recovery hmemory.2
  simp only [scalarMemory, map_add] at heq
  rw [← hcommute] at heq
  simp only [recovery, C.physical_scalarKernel, C.physical_differenceLift, hinitial] at heq hint
  rw [hphysical] at heq
  exact ⟨hint, heq⟩
end LeanPML.PML.SpatialAbsorption

namespace LeanPML.PML.Weak.OriginalInterval
open LeanPML.Rectangle
/-- 原八式中的两个实际辅助场调用标量核公式。x/y 方向通过 swap 严格区分。
所有连续性、演化、空间识别均复用原解已证结果。 -/
theorem scalar_memory_both
    {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (O : OriginalInterval D C ε κ τ μ T)
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    O.weightedX W₀x t = C.scalarMemory D.measure W₀x (fun s => (O.u s).val.val 1) t ∧
    O.weightedY W₀y t = weightedCongr D.measure C.swap_wx_eq_wy
      (C.swap.scalarMemory D.measure W₀y (fun s => (O.u s).val.val 2) t) := by
  simpa only [SpatialAbsorption.exponentialHistory_eq_scalarMemory] using
    O.operator_memory_both W₀x W₀y hWx hWy ht
/-- (5.7) 的 x 方向物理 L² 公式由原八式直接调用；y 方向用 swap 的同一结论。
所有时刻分别在商类意义相等，不把它升级为共同零测集之外的逐点路径结论。 -/
theorem scalar_memory_physical_x
    {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (O : OriginalInterval D C ε κ τ μ T) (W₀x : WeightedL2 D.measure C.wx)
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s => C.scalarKernelL2 D.measure (s-t)
      (C.rCoeff.operator D.measure ((O.u s).val.val 1) -
       C.pCoeff.operator D.measure ((O.u s).val.val 1))) volume 0 t ∧
    O.φx t = C.scalarKernelL2 D.measure (-t) (O.φx 0) +
      ∫ s in (0 : ℝ)..t, C.scalarKernelL2 D.measure (s-t)
        (C.rCoeff.operator D.measure ((O.u s).val.val 1) -
         C.pCoeff.operator D.measure ((O.u s).val.val 1)) := by
  exact C.auxiliary_scalar_memory_physical D.measure W₀x O.φx
    (fun s => (O.u s).val.val 1) (fun s => (O.flux s).val 0) T
    O.continuous_history.2.1
    ((zeroCoordinate D 1).continuous.comp_continuousOn O.continuous_history.1)
    ((weakHDivCoordinate D 0).continuous.comp_continuousOn O.continuous_flux)
    hWx (fun s hs => (O.auxiliary_hasDerivAt hs).1) (fun s hs => (O.spatial hs).1) ht

/-- (5.7) 的 y 方向物理 L² 公式由原八式直接调用；通过 swap 交换阻尼/强迫方向。
所有时刻分别在商类意义相等，不把它升级为共同零测集之外的逐点路径结论。 -/
theorem scalar_memory_physical_y
    {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (O : OriginalInterval D C ε κ τ μ T) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s => C.swap.scalarKernelL2 D.measure (s-t)
      (C.swap.rCoeff.operator D.measure ((O.u s).val.val 2) -
       C.swap.pCoeff.operator D.measure ((O.u s).val.val 2))) volume 0 t ∧
    O.φy t = C.swap.scalarKernelL2 D.measure (-t) (O.φy 0) +
      ∫ s in (0 : ℝ)..t, C.swap.scalarKernelL2 D.measure (s-t)
        (C.swap.rCoeff.operator D.measure ((O.u s).val.val 2) -
         C.swap.pCoeff.operator D.measure ((O.u s).val.val 2)) := by
  exact C.swap.auxiliary_scalar_memory_physical D.measure W₀y O.φy
    (fun s => (O.u s).val.val 2) (fun s => (O.flux s).val 1) T
    O.continuous_history.2.2
    ((zeroCoordinate D 2).continuous.comp_continuousOn O.continuous_history.1)
    ((weakHDivCoordinate D 1).continuous.comp_continuousOn O.continuous_flux)
    hWy (fun s hs => (O.auxiliary_hasDerivAt hs).2) (fun s hs => (O.spatial hs).2) ht

end LeanPML.PML.Weak.OriginalInterval
