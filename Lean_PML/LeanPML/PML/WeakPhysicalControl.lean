import LeanPML.PML.MainWeakRectangle

/-!
# V7 (8.4)–(8.8)：弱原解的全部辅助变量控制

复用已有 PhysicalControl；本文件补上重构坐标与输入 OriginalInterval.fields
的实际 L² 商类识别，并把时刻能量界接到初值。参数常数仍为已证 C_P=2Lx。
这不把图范数等价解释为任意八变量裸 L² 范数等价。
-/
noncomputable section
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.Weak
namespace OriginalInterval
variable {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
variable (O : OriginalInterval D C ε κ τ μ T) (J : OriginalJet O)
variable (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)

/-- (2.5) 在闭区间上的实际原变量识别。兼容来自初始条件保持，
不是在本定理中再要求全时段重构。 -/
theorem auxiliary_reconstruction
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    reconstructQ κ τ (O.baseState W₀x W₀y t) = O.q t ∧
    reconstructZ1 D.measure C ε (O.baseState W₀x W₀y t) = (O.fields t).Z1 ∧
    reconstructZ2 D.measure C κ τ (O.baseState W₀x W₀y t) = (O.fields t).Z2 ∧
    reconstructAuxX D.measure C (O.baseState W₀x W₀y t) = (O.fields t).Qx ∧
    reconstructAuxY D.measure C (O.baseState W₀x W₀y t) = (O.fields t).Qy := by
  have hreconstruct := O.reconstruction ht
  have hq : reconstructQ κ τ (O.baseState W₀x W₀y t) = O.q t :=
    reconstructQ_eq_z κ τ _ hreconstruct.1
  have hphysical := O.base_physical W₀x W₀y hWx hWy ht
  refine ⟨hq, hreconstruct.2.1.symm, ?_, ?_, ?_⟩
  · unfold reconstructZ2
    rw [hq]
    exact hreconstruct.2.2.1.symm
  · unfold reconstructAuxX
    rw [hphysical.2]
    exact hreconstruct.2.2.2.1.symm
  · unfold reconstructAuxY
    rw [hphysical.1]
    exact hreconstruct.2.2.2.2.symm

/-- (8.4)–(8.8) 的输出包；Z/Q 是输入八变量，不是未识别的重构槽。
B 是结论右端的能量值，下方分别取已定义的 E₇(t) 与 E₇(0)。 -/
structure OriginalAuxiliaryBounds (B t : ℝ) : Prop where
  displacement : ‖(O.u t).val.val 0‖^2 ≤ 8*(poincareConstant D)^2*B
  auxiliary : ‖O.φx t‖^2 + ‖O.φy t‖^2 ≤ 4*B
  primitivePolar : ‖O.q t‖^2 ≤ (16*κ^2*(poincareConstant D)^2+8*κ*τ^2/μ)*B
  electricMemory : ‖(O.fields t).Z1‖^2 ≤ 8*ε^2*C.S^4*(poincareConstant D)^2*B
  polarMemory : ‖(O.fields t).Z2‖^2 ≤ C.S^4*(16*κ^2*(poincareConstant D)^2+8*κ*τ^2/μ)*B
  magneticAuxiliary : ‖(O.fields t).Qx‖^2+‖(O.fields t).Qy‖^2 ≤ 4*C.S^2*B

/-- 全部辅助控制直接接到弱原解；静态约束由已证兼容保持和图路径给出。
没有把目标界作为参数字段，使用原文常数 8、4、16、8。 -/
theorem original_auxiliary_control
    (hp : CoercivityParameters C ε κ τ μ (poincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O J) {t : ℝ} (ht : t ∈ Icc 0 T) :
    OriginalAuxiliaryBounds O (O.energy J W₀x W₀y t) t := by
  have hbounds := physicalControl_Conditional D.measure C ε κ τ μ (poincareConstant D) hp
    (weakGreenDomain D).spatial (weakPoincareDomain D) (O.sameSource J W₀x W₀y) t
    (O.base_constraints W₀x W₀y hWx hWy ht)
    (O.first_constraints J W₀x W₀y hWx hWy hdeg ht)
  dsimp only [sameSource] at hbounds
  have hident := O.auxiliary_reconstruction W₀x W₀y hWx hWy ht
  have hphysical := O.base_physical W₀x W₀y hWx hWy ht
  dsimp only [energy, energy7, sameSource]
  refine ⟨hbounds.displacement, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hphysical.1,hphysical.2] using hbounds.auxiliary
  · simpa only [hident.1] using hbounds.primitivePolar
  · simpa only [hident.2.1] using hbounds.electricMemory
  · simpa only [hident.2.2.1] using hbounds.polarMemory
  · simpa only [hident.2.2.2.1,hident.2.2.2.2] using hbounds.magneticAuxiliary

/-- 由已证单调性把 (8.4)–(8.8) 的全部右端替换为初值能量。
先证明乘数非负，再使用序的传递；不是再次假设初值控制。 -/
theorem original_auxiliary_initial_control
    (hp : CoercivityParameters C ε κ τ μ (poincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0)
    (hdeg : DegenerateJetCompatibility O J) {t : ℝ} (ht : t ∈ Icc 0 T) :
    OriginalAuxiliaryBounds O (O.energy J W₀x W₀y 0) t := by
  have hbounds := O.original_auxiliary_control J W₀x W₀y hp hWx hWy hdeg ht
  have henergy := ((O.main_energy_estimate_WeakOriginal J W₀x W₀y hp hWx hWy hdeg).initial_bounds t ht).2
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
end LeanPML.PML.Weak
