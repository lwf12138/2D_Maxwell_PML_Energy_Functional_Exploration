import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# 有界算子阻尼的空间值记忆公式

服务于 V7 (5.7)：在 Banach 空间中用算子指数作积分因子。
证明不读取 L² 代表元，不交换时间与空间的 a.e. 量词。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace LeanPML.Analysis
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- 有界乘子的算子指数；固定其范数拓扑以便在具体闭子空间中调用。 -/
def dampingKernel (B : H →L[ℝ] H) (t : ℝ) : H →L[ℝ] H := NormedSpace.exp (t • B)

/-- 由 (5.7) 推广的 Banach 空间 FTC 公式，原文未单列。
输入 W 的闭区间连续与内部真实 ODE；输出核 exp((s−t)B) 的 Bochner 积分。
B 是有界阻尼算子，不能用无界能量权重替代。 -/
theorem operator_memory_formula (B : H →L[ℝ] H) (W F : ℝ → H) {T t : ℝ}
    (hW : ContinuousOn W (Icc 0 T)) (hF : ContinuousOn F (Icc 0 T))
    (hODE : ∀ s ∈ Ioo 0 T, HasDerivAt W (-B (W s) + F s) s)
    (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s => (NormedSpace.exp ((s-t) • B)) (F s)) volume 0 t ∧
    W t = (NormedSpace.exp (-t • B)) (W 0) +
      ∫ s in (0 : ℝ)..t, (NormedSpace.exp ((s-t) • B)) (F s) := by
  let K : ℝ → (H →L[ℝ] H) := fun s => NormedSpace.exp ((s-t) • B)
  have hK (s : ℝ) : HasDerivAt K (K s * B) s := by
    simpa only [K, one_smul, Function.comp_def, id_eq] using
      (hasDerivAt_exp_smul_const B (s-t)).scomp s ((hasDerivAt_id s).sub_const t)
  have hKcontinuous : Continuous K := continuous_iff_continuousAt.mpr fun s => (hK s).continuousAt
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hproduct : ContinuousOn (fun s => K s (W s)) (Icc 0 t) :=
    hKcontinuous.continuousOn.clm_apply (hW.mono hsub)
  have hforcing : ContinuousOn (fun s => K s (F s)) (Icc 0 t) :=
    hKcontinuous.continuousOn.clm_apply (hF.mono hsub)
  have hint := hforcing.intervalIntegrable_of_Icc (μ := volume) ht.1
  have hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => K r (W r)) (K s (F s)) s := by
    intro s hs
    have hraw := (hK s).clm_apply (hODE s ⟨hs.1, hs.2.trans_le ht.2⟩)
    convert hraw using 1
    simp only [ContinuousLinearMap.mul_apply, map_add, map_neg]
    abel
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hproduct hderiv hint
  have hKt : K t = ContinuousLinearMap.id ℝ H := by simp only [K, sub_self, zero_smul, NormedSpace.exp_zero]; rfl
  have hK0 : K 0 = NormedSpace.exp (-t • B) := by simp [K]
  rw [hKt,hK0] at hFTC
  exact ⟨hint, by simpa only [ContinuousLinearMap.id_apply, add_comm] using (eq_add_of_sub_eq hFTC.symm)⟩
end LeanPML.Analysis
