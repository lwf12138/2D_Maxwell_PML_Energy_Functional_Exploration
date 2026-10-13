import LeanPML.Analysis.EnergyCalculus
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# 用平方根坐标实现 V7 的加权 L²

V7 (5.5)–(5.6) 的权重可以无界，且在零吸收区 Z 上等于零。
这里使用实际 L² 等价类 X=√w ψ，并要求 X 在 Z 上 a.e. 为零。
加权范数就是 X 的普通 L² 范数；物理分量 ψ 通过有界乘子 1/√w
恢复（Z 上取零）。所有等式都按底层测度 ν 的 a.e. 意义解释，
不读取某个等价类在指定点的值。

阅读顺序：weightedSubspace → WeightedL2 → physicalL2 →
weighted_norm_sq_eq_integral。低层假设 w=0 或 w≥1；PML 中由
正吸收区 w≥3/2 推出，不要求 w 的上界或吸收系数的正下界。
本文件不构造空间梯度、零迹或 PDE 能量律。
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace LeanPML.Analysis

variable {α : Type*} [MeasurableSpace α]

/-- 由 V7 (5.6) 推出，原文未单列：平方根加权坐标的零区条件。
成员是 mathlib 的实际 L² 等价类；加法、数乘保持 a.e. 零值。 -/
def weightedSubspace (ν : Measure α) (w : α → ℝ) : Submodule ℝ (Lp ℝ 2 ν) where
  carrier := {X | ∀ᵐ x ∂ν, w x = 0 → X x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
    intro _
    exact hx
  add_mem' := by
    intro X Y hX hY
    filter_upwards [hX, hY, Lp.coeFn_add X Y] with x hx hy hsum
    intro hw
    simp only [hsum, Pi.add_apply, hx hw, hy hw, add_zero]
  smul_mem' := by
    intro c X hX
    filter_upwards [hX, Lp.coeFn_smul c X] with x hx hsmul
    intro hw
    simp only [hsmul, Pi.smul_apply, smul_eq_mul, hx hw, mul_zero]

/-- V7 (5.6) 的具体表示：范数和内积继承自实际 L² 子空间。
元素保存 X=√w ψ 的等价类，而非 ψ 的任意逐点代表元。 -/
abbrev WeightedL2 (ν : Measure α) (w : α → ℝ) := weightedSubspace ν w

/-- 由 (5.6) 推出，原文未单列：输入实际函数及平方根加权 L² 成员证据，
得到平方根坐标；恢复时自动在零区延拓为零。若要恢复原 f，还需
physicalL2_weightedOfFunction 的 f 在零区为零条件，不能省略。 -/
def weightedOfFunction (ν : Measure α) (w f : α → ℝ)
    (hf_weighted : MemLp (fun x => Real.sqrt (w x) * f x) 2 ν) :
    WeightedL2 ν w :=
  ⟨hf_weighted.toLp _, by
    filter_upwards [hf_weighted.coeFn_toLp] with x hx
    intro hw_zero
    simp only [hx, hw_zero, Real.sqrt_zero, zero_mul]⟩

/-- 构造所得平方根坐标与输入函数 a.e. 对应；这是等价类层面的陈述。 -/
theorem weightedOfFunction_coe (ν : Measure α) (w f : α → ℝ)
    (hf_weighted : MemLp (fun x => Real.sqrt (w x) * f x) 2 ν) :
    (weightedOfFunction ν w f hf_weighted : Lp ℝ 2 ν) =ᵐ[ν]
      fun x => Real.sqrt (w x) * f x := hf_weighted.coeFn_toLp

/-- 全零吸收时加权辅助空间只有零元；普通场并未因此被删除。
由零区 a.e. 条件直接证明，不利用除以零。 -/
theorem weighted_eq_zero_of_weight_zero (ν : Measure α)
    (X : WeightedL2 ν (fun _ => 0)) : X = 0 := by
  apply Subtype.ext
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [X.property] with x hx
  exact hx rfl

/-- 正区下界使逆平方根有界，原文 (5.6) 后嵌入的关键估计。
零区的逆值按实数总除法为 0；此约定只用于恢复映射，非空间耗散。 -/
theorem inv_sqrt_abs_le_one {s : ℝ} (hs : s = 0 ∨ 1 ≤ s) :
    |(Real.sqrt s)⁻¹| ≤ 1 := by
  rcases hs with hs_zero | hs_lower
  · simp [hs_zero]
  · have hs_sqrt : 1 ≤ Real.sqrt s := Real.one_le_sqrt.mpr hs_lower
    have hs_sqrt_pos : 0 < Real.sqrt s := lt_of_lt_of_le zero_lt_one hs_sqrt
    rw [abs_of_nonneg (inv_nonneg.mpr hs_sqrt_pos.le)]
    exact (inv_le_one₀ hs_sqrt_pos).mpr hs_sqrt

/-- V7 (5.6) 后嵌入的实际映射：ψ=(√w)⁻¹X，零区取零。
hw 用于乘子的可测性，hgap 给出逆平方根≤1；w 本身可以无界。
先作子空间包含，再调用已证明的有界乘法，故映射与代表元选择无关。 -/
def physicalL2 (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) :
    WeightedL2 ν w →L[ℝ] ScalarL2 ν :=
  (boundedMul ν (fun x => (Real.sqrt (w x))⁻¹) hw.sqrt.inv 1
    (fun x => inv_sqrt_abs_le_one (hgap x))).comp (weightedSubspace ν w).subtypeL

/-- 恢复映射的 a.e. 公式；后续局部密度到空间积分的改写使用它。 -/
theorem physicalL2_coe (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (X : WeightedL2 ν w) :
    physicalL2 ν w hw hgap X =ᵐ[ν]
      fun x => (Real.sqrt (w x))⁻¹ * (X : ScalarL2 ν) x :=
  coeFn_boundedMul ν _ hw.sqrt.inv 1 (fun x => inv_sqrt_abs_le_one (hgap x)) X.val

/-- 由 V7 (5.6) 推出：恢复后的普通 L² 场在零区 a.e. 为零。
这是实际 ν-a.e. 结论，不能被加权测度“看不见零区”所替代。 -/
theorem physicalL2_zero_on_zero (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (X : WeightedL2 ν w) :
    ∀ᵐ x ∂ν, w x = 0 → physicalL2 ν w hw hgap X x = 0 := by
  filter_upwards [physicalL2_coe ν w hw hgap X] with x hx
  intro hw_zero
  simp only [hx, hw_zero, Real.sqrt_zero, inv_zero, zero_mul]

/-- 平方根坐标能从物理场完整恢复，原文 (5.6) 的具体表示等价。
正区用 √w≠0 约分；零区用 X 的子空间条件。仅有乘子总定义还不够。 -/
theorem sqrt_mul_physicalL2 (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (X : WeightedL2 ν w) :
    (fun x => Real.sqrt (w x) * physicalL2 ν w hw hgap X x) =ᵐ[ν]
      (X : ScalarL2 ν) := by
  filter_upwards [physicalL2_coe ν w hw hgap X, X.property] with x hx hzero
  rw [hx]
  rcases hgap x with hw_zero | hw_lower
  · simp only [hw_zero, Real.sqrt_zero, inv_zero, zero_mul, hzero hw_zero]
  · have hsqrt_ne : Real.sqrt (w x) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hw_lower))
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt_ne, one_mul]

/-- V7 (5.6) 后连续嵌入：‖ψ‖₂≤‖ψ‖w。
结论来自逆平方根乘子的范数界，不作为 WeightedL2 的定义字段。 -/
theorem physicalL2_norm_le (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (X : WeightedL2 ν w) :
    ‖physicalL2 ν w hw hgap X‖ ≤ ‖X‖ := by
  simpa only [physicalL2, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.coe_norm, one_mul] using
    norm_boundedMul_le ν _ hw.sqrt.inv 1
      (fun x => inv_sqrt_abs_le_one (hgap x)) X.val

/-- (5.6) 后嵌入的平方形式，直接供图范数与能量估计使用。 -/
theorem physicalL2_norm_sq_le (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (X : WeightedL2 ν w) :
    ‖physicalL2 ν w hw hgap X‖ ^ 2 ≤ ‖X‖ ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _) (physicalL2_norm_le ν w hw hgap X) 2

/-- 恢复映射为单射；没有丢失零区之外的等价类信息。
两个普通 L² 场相同后，乘回 √w 并用 a.e. 重建即可。 -/
theorem physicalL2_injective (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) :
    Function.Injective (physicalL2 ν w hw hgap) := by
  intro X Y hphysical
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sqrt_mul_physicalL2 ν w hw hgap X,
    sqrt_mul_physicalL2 ν w hw hgap Y] with x hx hy
  rw [← hx, ← hy, hphysical]

/-- 由 (5.6) 推出：加权密度 wψ² 与平方根坐标 X² a.e. 相等。
这个等式让后续能量积分合法性复用普通 L² 的平方可积性。 -/
theorem weighted_square_ae (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (X : WeightedL2 ν w) :
    (fun x => w x * (physicalL2 ν w hw hgap X x) ^ 2) =ᵐ[ν]
      fun x => ((X : ScalarL2 ν) x) ^ 2 := by
  filter_upwards [sqrt_mul_physicalL2 ν w hw hgap X] with x hx
  have hw_nonneg : 0 ≤ w x := (hgap x).elim (fun hz => by simp [hz])
    (fun hpos => le_trans zero_le_one hpos)
  calc
    w x * (physicalL2 ν w hw hgap X x) ^ 2 =
        (Real.sqrt (w x) * physicalL2 ν w hw hgap X x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hw_nonneg]
    _ = ((X : ScalarL2 ν) x) ^ 2 := congrArg (fun r : ℝ => r ^ 2) hx

/-- (5.6) 的平方加权密度确实可积；不依赖不可积积分的总定义。 -/
theorem integrable_weighted_square (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (X : WeightedL2 ν w) :
    Integrable (fun x => w x * (physicalL2 ν w hw hgap X x) ^ 2) ν :=
  (Lp.memLp X.val).integrable_sq.congr (weighted_square_ae ν w hw hgap X).symm

/-- V7 (5.6) 的精确范数公式：‖X‖²=∫wψ²，ψ 为恢复后的物理场。
实际积分与具体加权空间相连；后续 (6.2) 辅助能量项使用本定理。 -/
theorem weighted_norm_sq_eq_integral (ν : Measure α) (w : α → ℝ)
    (hw : Measurable w) (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    (X : WeightedL2 ν w) :
    ‖X‖ ^ 2 = ∫ x, w x * (physicalL2 ν w hw hgap X x) ^ 2 ∂ν := by
  calc
    ‖X‖ ^ 2 = ∫ x, ((X : ScalarL2 ν) x) ^ 2 ∂ν := norm_sq_eq_integral ν X.val
    _ = ∫ x, w x * (physicalL2 ν w hw hgap X x) ^ 2 ∂ν :=
      integral_congr_ae (weighted_square_ae ν w hw hgap X).symm

/-- 加权内积的积分密度对应，原文 (5.6) 未单列。
恢复 X、Y 后，√w 的两个因子合并成 w；后续加权时间导数使用此式。 -/
theorem weighted_product_ae (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (X Y : WeightedL2 ν w) :
    (fun x => w x * physicalL2 ν w hw hgap X x * physicalL2 ν w hw hgap Y x) =ᵐ[ν]
      fun x => (X : ScalarL2 ν) x * (Y : ScalarL2 ν) x := by
  filter_upwards [sqrt_mul_physicalL2 ν w hw hgap X,
    sqrt_mul_physicalL2 ν w hw hgap Y] with x hx hy
  have hw_nonneg : 0 ≤ w x := (hgap x).elim (fun hz => by simp [hz])
    (fun hpos => le_trans zero_le_one hpos)
  calc
    w x * physicalL2 ν w hw hgap X x * physicalL2 ν w hw hgap Y x =
        (Real.sqrt (w x)) ^ 2 * physicalL2 ν w hw hgap X x *
          physicalL2 ν w hw hgap Y x := by rw [Real.sq_sqrt hw_nonneg]
    _ = (Real.sqrt (w x) * physicalL2 ν w hw hgap X x) *
        (Real.sqrt (w x) * physicalL2 ν w hw hgap Y x) := by ring
    _ = (X : ScalarL2 ν) x * (Y : ScalarL2 ν) x := by rw [hx, hy]

/-- 加权交叉项可积；由实际 L² 坐标的乘积可积性及 a.e. 对应得到。 -/
theorem integrable_weighted_product (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x) (X Y : WeightedL2 ν w) :
    Integrable (fun x => w x * physicalL2 ν w hw hgap X x *
      physicalL2 ν w hw hgap Y x) ν :=
  (integrable_product ν X.val Y.val).congr (weighted_product_ae ν w hw hgap X Y).symm

/-- 实际加权内积等于 ∫wψχ；与范数公式一起落实 (5.6) 的内积空间表示。 -/
theorem weighted_inner_eq_integral (ν : Measure α) (w : α → ℝ)
    (hw : Measurable w) (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    (X Y : WeightedL2 ν w) :
    ⟪X, Y⟫_ℝ = ∫ x, w x * physicalL2 ν w hw hgap X x *
      physicalL2 ν w hw hgap Y x ∂ν := by
  calc
    ⟪X, Y⟫_ℝ = ∫ x, (X : ScalarL2 ν) x * (Y : ScalarL2 ν) x ∂ν :=
      inner_eq_integral ν X.val Y.val
    _ = _ := integral_congr_ae (weighted_product_ae ν w hw hgap X Y).symm

/-- 实际加权空间中的平方范数时间求导，供 (6.2) 加权辅助项使用。
输入必须是 WeightedL2 范数中的 HasDerivAt；普通 L² 或逐点可导不足以替代。 -/
theorem hasDerivAt_weighted_half_norm_sq (ν : Measure α) (w : α → ℝ)
    {X : ℝ → WeightedL2 ν w} {Xdot : WeightedL2 ν w} {t : ℝ}
    (hX : HasDerivAt X Xdot t) :
    HasDerivAt (fun s => ‖X s‖ ^ 2 / 2) ⟪X t, Xdot⟫_ℝ t :=
  hasDerivAt_half_norm_sq hX

/-- 加权路径可导蕴含其零延拓物理场在普通 L² 中可导。
只使用已构造的连续线性恢复映射；反向推断并不成立，也未被假设。 -/
theorem hasDerivAt_physicalL2 (ν : Measure α) (w : α → ℝ) (hw : Measurable w)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    {X : ℝ → WeightedL2 ν w} {Xdot : WeightedL2 ν w} {t : ℝ}
    (hX : HasDerivAt X Xdot t) :
    HasDerivAt (fun s => physicalL2 ν w hw hgap (X s))
      (physicalL2 ν w hw hgap Xdot) t :=
  (physicalL2 ν w hw hgap).hasFDerivAt.comp_hasDerivAt t hX

/-- 由 (5.6) 推出：原函数已在零区为零时，构造再恢复得到原函数 a.e.。
这给出了具体表示的反向接口，而非仅给一个抽象加权空间名字。 -/
theorem physicalL2_weightedOfFunction (ν : Measure α) (w f : α → ℝ)
    (hw : Measurable w) (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    (hf_weighted : MemLp (fun x => Real.sqrt (w x) * f x) 2 ν)
    (hf_zero : ∀ᵐ x ∂ν, w x = 0 → f x = 0) :
    physicalL2 ν w hw hgap (weightedOfFunction ν w f hf_weighted) =ᵐ[ν] f := by
  filter_upwards [physicalL2_coe ν w hw hgap (weightedOfFunction ν w f hf_weighted),
    weightedOfFunction_coe ν w f hf_weighted, hf_zero] with x hphysical hcoordinate hzero
  rw [hphysical, hcoordinate]
  rcases hgap x with hw_zero | hw_lower
  · simp only [hw_zero, Real.sqrt_zero, inv_zero, zero_mul, hzero hw_zero]
  · have hsqrt_ne : Real.sqrt (w x) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hw_lower))
    rw [← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul]

/-- 加权平方可积且零区消失的实际函数属于普通 L²。
由上述零延拓恢复而得；原文 (5.6) 后嵌入的函数版本。 -/
theorem memLp_of_weighted (ν : Measure α) (w f : α → ℝ)
    (hw : Measurable w) (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    (hf_weighted : MemLp (fun x => Real.sqrt (w x) * f x) 2 ν)
    (hf_zero : ∀ᵐ x ∂ν, w x = 0 → f x = 0) : MemLp f 2 ν :=
  (memLp_congr_ae (physicalL2_weightedOfFunction ν w f hw hgap hf_weighted hf_zero)).mp
    (Lp.memLp _)

/-- 表示元独立性：输入函数 a.e. 相等，构造出的加权状态相等。
与 ordinary L² 一样，零测集上的修改不会产生不同能量状态。 -/
theorem weightedOfFunction_congr (ν : Measure α) (w f g : α → ℝ)
    (hf : MemLp (fun x => Real.sqrt (w x) * f x) 2 ν)
    (hg : MemLp (fun x => Real.sqrt (w x) * g x) 2 ν)
    (hfg : f =ᵐ[ν] g) : weightedOfFunction ν w f hf = weightedOfFunction ν w g hg := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [weightedOfFunction_coe ν w f hf,
    weightedOfFunction_coe ν w g hg, hfg] with x hxf hxg hxfg
  rw [hxf, hxg, hxfg]

/-- 由 (5.6) 推出，原文未单列：平方根坐标构成闭子空间。
乘以零区示性函数是范数≤1的连续线性算子；本子空间正是它的核。
这一步补足完备性依据，不把“子空间”自动当成闭空间。 -/
theorem weightedSubspace_isClosed (ν : Measure α) (w : α → ℝ) (hw : Measurable w) :
    IsClosed (weightedSubspace ν w : Set (ScalarL2 ν)) := by
  let mask : α → ℝ := fun x => if w x = 0 then 1 else 0
  have hmask_measurable : Measurable mask :=
    Measurable.ite (hw (measurableSet_singleton 0)) measurable_const measurable_const
  have hmask_bound : ∀ x, |mask x| ≤ 1 := by
    intro x
    dsimp [mask]
    split_ifs <;> norm_num
  let M : ScalarL2 ν →L[ℝ] ScalarL2 ν := boundedMul ν mask hmask_measurable 1 hmask_bound
  have hkernel : weightedSubspace ν w = M.ker := by
    ext X
    change (∀ᵐ x ∂ν, w x = 0 → X x = 0) ↔ M X = 0
    rw [Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro hX
      filter_upwards [hX, coeFn_boundedMul ν mask hmask_measurable 1 hmask_bound X]
        with x hx hmul
      rw [hmul]
      by_cases hw_zero : w x = 0
      · simp [mask, hw_zero, hx hw_zero]
      · simp [mask, hw_zero]
    · intro hMX
      filter_upwards [hMX, coeFn_boundedMul ν mask hmask_measurable 1 hmask_bound X]
        with x hx hmul
      intro hw_zero
      change (boundedMul ν mask hmask_measurable 1 hmask_bound X) x = 0 at hx
      rw [hmul] at hx
      simpa [mask, hw_zero] using hx
  rw [hkernel]
  exact M.isClosed_ker

/-- 上述实际加权内积空间是完备的：闭子空间继承普通 L² 的完备性。
因此可作为 (6.5) 加权 Hilbert 路径的承载空间；没有对无界 w 作乘法连续性假设。 -/
theorem weighted_completeSpace (ν : Measure α) (w : α → ℝ) (hw : Measurable w) :
    CompleteSpace (WeightedL2 ν w) :=
  (weightedSubspace_isClosed ν w hw).completeSpace_coe

section Example

variable (ν : Measure α) [IsFiniteMeasure ν] (w : α → ℝ)

/-- 能量接口的非零实例种子：在有限测度域上取平方根坐标 X=1。
仅这个实例取处处非零权重，使 X 的零区条件为空；一般空间仍允许零区。
物理场是 ψ=1/√w，并非无界权重的普通乘法算子。 -/
def weightedConstant (hw_ne : ∀ x, w x ≠ 0) : WeightedL2 ν w :=
  ⟨(memLp_const (1 : ℝ)).toLp (fun _ : α => 1), by
    exact ae_of_all ν (fun x hx => False.elim (hw_ne x hx))⟩

/-- 测度非零时，常数平方根坐标给出非零加权状态。
同时使用 L² 代表函数的 a.e. 公式，不能从某个点值推断 L² 元素非零。 -/
theorem weightedConstant_ne_zero [NeZero ν] (hw_ne : ∀ x, w x ≠ 0) :
    weightedConstant ν w hw_ne ≠ 0 := by
  intro hzero
  have hcoordinate_zero : ((weightedConstant ν w hw_ne : WeightedL2 ν w) : ScalarL2 ν) = 0 :=
    congrArg Subtype.val hzero
  have hzero_ae := Lp.eq_zero_iff_ae_eq_zero.mp hcoordinate_zero
  have hone_ae : ((weightedConstant ν w hw_ne : WeightedL2 ν w) : ScalarL2 ν) =ᵐ[ν]
      (fun _ : α => (1 : ℝ)) := (memLp_const (1 : ℝ)).coeFn_toLp
  obtain ⟨x, hx_one, hx_zero⟩ := (hone_ae.and hzero_ae).exists
  norm_num [hx_zero] at hx_one

/-- 非恒定空间值时间路径 X(t)=tX₀：导数是在实际加权范数中取得。
这是能量计算接口实例，不是 primitive 或完整 PDE 解。 -/
theorem hasDerivAt_weighted_linear (hw_ne : ∀ x, w x ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s • weightedConstant ν w hw_ne)
      (weightedConstant ν w hw_ne) t := by
  simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const (weightedConstant ν w hw_ne)

/-- 上述路径在 0、1 两时刻不同，明确排除恒定或全零测试。 -/
theorem weighted_linear_nonconstant [NeZero ν] (hw_ne : ∀ x, w x ≠ 0) :
    (0 : ℝ) • weightedConstant ν w hw_ne ≠ (1 : ℝ) • weightedConstant ν w hw_ne := by
  simpa only [zero_smul, one_smul, ne_eq, eq_comm] using weightedConstant_ne_zero ν w hw_ne

/-- 非零路径实际调用加权平方范数求导；后续空间能量实例可直接复用导数证据。 -/
theorem hasDerivAt_weighted_linear_energy (hw_ne : ∀ x, w x ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖s • weightedConstant ν w hw_ne‖ ^ 2 / 2)
      ⟪t • weightedConstant ν w hw_ne, weightedConstant ν w hw_ne⟫_ℝ t :=
  hasDerivAt_weighted_half_norm_sq ν w (hasDerivAt_weighted_linear ν w hw_ne t)

end Example

end LeanPML.Analysis
