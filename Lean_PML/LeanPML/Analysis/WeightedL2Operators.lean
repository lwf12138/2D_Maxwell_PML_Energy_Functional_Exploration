import LeanPML.Analysis.WeightedL2

/-!
# v1.0.1：退化加权空间的物理像与有界系数作用

由 V7 (5.5)–(5.6) 推出，原文未单列这些算子声明。
复用 `WeightedL2` 的平方根坐标 X=√w ψ、闭性和完备性。
本文件补充物理像的双向刻画及有界系数乘法；不假定 w 有界，
不构造普通 L² 上的无界权重乘法，不涉及加权正则性传播。
建议顺序：`physicalL2_range_iff` → `weightedMul` → `physicalL2_weightedMul`。
-/
noncomputable section
open MeasureTheory
namespace LeanPML.Analysis
variable {α : Type*} [MeasurableSpace α]

/-- (5.6) 的精确普通 L² 像：平方根加权可积且在零区 a.e. 为零。
双向结论防止只保留加权积分、却遗漏原测度能看到的零区。
恢复映射的连续性和单射性已经在 WeightedL2 中证明。 -/
theorem physicalL2_range_iff (ν : Measure α) (w : α → ℝ)
    (hw : Measurable w) (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (f : ScalarL2 ν) :
    (∃ X : WeightedL2 ν w, physicalL2 ν w hw hgap X = f) ↔
      MemLp (fun x => Real.sqrt (w x) * f x) 2 ν ∧
      (∀ᵐ x ∂ν, w x = 0 → f x = 0) := by
  constructor
  · rintro ⟨X, rfl⟩
    have hcoordinate := sqrt_mul_physicalL2 ν w hw hgap X
    exact ⟨(memLp_congr_ae hcoordinate).mpr (Lp.memLp X.val),
      physicalL2_zero_on_zero ν w hw hgap X⟩
  · rintro ⟨hf_weighted, hf_zero⟩
    refine ⟨weightedOfFunction ν w f hf_weighted, ?_⟩
    apply Lp.ext
    exact physicalL2_weightedOfFunction ν w f hw hgap hf_weighted hf_zero

/-- 有界可测系数 m 在平方根坐标上作用：X↦mX。
输入界只施加于 m；零区由 X=0 保持，没有对 w 新增上界。
这为后续弱空间中的 a、b 等乘法提供实际连续线性算子。 -/
def weightedMul (ν : Measure α) (w m : α → ℝ) (hm : Measurable m)
    (C : ℝ) (hm_bound : ∀ x, |m x| ≤ C) :
    WeightedL2 ν w →L[ℝ] WeightedL2 ν w :=
  ((boundedMul ν m hm C hm_bound).comp (weightedSubspace ν w).subtypeL).codRestrict
    (weightedSubspace ν w) (by
      intro X
      change ∀ᵐ x ∂ν, w x = 0 → (boundedMul ν m hm C hm_bound X.val) x = 0
      filter_upwards [coeFn_boundedMul ν m hm C hm_bound X.val, X.property]
        with x hmul hzero
      intro hw_zero
      rw [hmul, hzero hw_zero, mul_zero])

/-- 有界系数在加权范数中仍满足 ‖mψ‖w≤C‖ψ‖w；由旧 L² 乘子估计推出。
它不允许把可能无界的 w 代入 m 并省略 hm_bound。 -/
theorem weightedMul_norm_le (ν : Measure α) (w m : α → ℝ) (hm : Measurable m)
    (C : ℝ) (hm_bound : ∀ x, |m x| ≤ C) (X : WeightedL2 ν w) :
    ‖weightedMul ν w m hm C hm_bound X‖ ≤ C * ‖X‖ :=
  norm_boundedMul_le ν m hm C hm_bound X.val

/-- 恢复与有界乘法交换：物理场确实变成 mψ。
等式属于实际 L² 商类；用 a.e. 代表公式证明，不读取特殊点值。 -/
theorem physicalL2_weightedMul (ν : Measure α) (w m : α → ℝ)
    (hw : Measurable w) (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    (hm : Measurable m) (C : ℝ) (hm_bound : ∀ x, |m x| ≤ C)
    (X : WeightedL2 ν w) :
    physicalL2 ν w hw hgap (weightedMul ν w m hm C hm_bound X) =
      boundedMul ν m hm C hm_bound (physicalL2 ν w hw hgap X) := by
  apply Lp.ext
  filter_upwards [physicalL2_coe ν w hw hgap (weightedMul ν w m hm C hm_bound X),
    coeFn_boundedMul ν m hm C hm_bound X.val,
    coeFn_boundedMul ν m hm C hm_bound (physicalL2 ν w hw hgap X),
    physicalL2_coe ν w hw hgap X] with x hleft hmul hright hphysical
  change _ = _ at hleft
  rw [hleft, hright, hphysical]
  change (Real.sqrt (w x))⁻¹ * (boundedMul ν m hm C hm_bound X.val) x = _
  rw [hmul]
  ring

end LeanPML.Analysis
