import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# 真实 Banach 值历史与内部零导数保持

V7 (2.3)–(2.4) 的时间分析工具：历史是实际 Bochner 积分，
只需 [0,T] 连续、(0,T) 内导数。供弱原场及 H₀¹ 图路径使用。
这里不读空间代表元，不要求端点方程，也不将兼容保持放入输入。
-/
noncomputable section
open MeasureTheory Set
namespace LeanPML.Time
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- (2.3) 的 Banach 值初值加历史；下文连续性确保实际可积。 -/
def banachHistory (f : ℝ → H) (u₀ : H) (t : ℝ) : H := u₀ + ∫ s in (0:ℝ)..t, f s

omit [CompleteSpace H] in
/-- 零长度历史的初值，不使用任何内部方程。 -/
theorem banachHistory_initial (f : ℝ → H) (u₀ : H) : banachHistory f u₀ 0 = u₀ := by
  simp [banachHistory]

omit [CompleteSpace H] in
/-- 闭区间连续给 Bochner 历史的闭区间连续性，含 T=0。 -/
theorem continuousOn_banachHistory (f : ℝ → H) (u₀ : H) {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) : ContinuousOn (banachHistory f u₀) (Icc 0 T) := by
  have hint := hf.intervalIntegrable_of_Icc (μ := volume) hT
  have hc := intervalIntegral.continuousOn_primitive_interval' hint
    (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
  rw [uIcc_of_le hT] at hc
  exact continuousOn_const.add hc

/-- FTC 给内部的真实 Banach 导数；不要求 f 有空间点值或全轴连续。 -/
theorem hasDerivAt_banachHistory (f : ℝ → H) (u₀ : H) {T t : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (banachHistory f u₀) (f t) t := by
  have hsub : Icc (0:ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2.le
  have hint := (hf.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1.le
  have hmeas := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo
    (hf.mono Ioo_subset_Icc_self) t ht
  have hc := (hf t ⟨ht.1.le, ht.2.le⟩).continuousAt (Icc_mem_nhds ht.1 ht.2)
  exact ((hasDerivAt_const t u₀).add
    (intervalIntegral.integral_hasDerivAt_right hint hmeas hc)).congr_deriv (zero_add _)

/-- (2.4) 的场层时间工具：实际 Banach 路径内部零导数推出端点也保持初值。
FTC 对零导数可积性直接成立；t=0 时同一证明使用零区间积分。 -/
theorem banach_eq_initial_of_hasDerivAt_zero (F : ℝ → H) {T t : ℝ}
    (hcont : ContinuousOn F (Icc 0 T))
    (hderiv : ∀ s ∈ Ioo 0 T, HasDerivAt F 0 s) (ht : t ∈ Icc 0 T) : F t = F 0 := by
  have hsub : Icc (0:ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hcont.mono hsub)
    (fun s hs => hderiv s ⟨hs.1, hs.2.trans_le ht.2⟩)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:H)) volume 0 t)
  rw [intervalIntegral.integral_zero] at hFTC
  exact sub_eq_zero.mp hFTC.symm

/-- 有界线性坐标投影与真实历史交换。用于 H₀¹ 历史的 L² 函数/弱梯度坐标。 -/
theorem map_banachHistory {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (L : H →L[ℝ] G) (f : ℝ → H) (u₀ : H) {T t : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    L (banachHistory f u₀ t) = banachHistory (fun s => L (f s)) (L u₀) t := by
  have hint := (hf.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  rw [banachHistory, map_add, ← L.intervalIntegral_comp_comm hint]
  rfl
end LeanPML.Time
