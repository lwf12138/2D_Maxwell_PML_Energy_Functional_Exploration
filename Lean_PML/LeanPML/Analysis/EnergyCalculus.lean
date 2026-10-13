import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic.Ring

/-!
# 实际空间内积与时间求导

本文件为 V7 (6.2) 的空间能量提供分析工具；这些工具由该式推出，原文未单列。
先证明有界可测系数在实际 L² 等价类上定义连续乘法，再连接积分与内积，
最后用 mathlib 的内积求导规则处理时间路径。

测度用 ν，避免与材料参数 μ 混淆。系数只随空间改变，与时间无关。
这里的有界乘子用于 a、b 等有界系数，**不**用于可能无界的能量权重 w。
加权范数由 WeightedL2 模块另外承载；本文件不交换逐点导数与空间积分。

阅读顺序：boundedMul → inner_boundedMul_eq_integral → hasDerivAt_operator_inner。
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace LeanPML.Analysis

section Multiplication

variable {α : Type*} [MeasurableSpace α]

/-- 普通标量空间就是 mathlib 的实际 L²：函数按 ν 几乎处处相等取商。
源自 V7 (6.2) 中的普通 L² 项；不是一个任意命名的抽象类型。 -/
abbrev ScalarL2 (ν : Measure α) := Lp ℝ 2 ν

/-- 有界可测系数乘以 L² 函数仍属 L²。
这是构造 (6.2) 变系数二次项的辅助分析结论；界由调用者的系数条件证明。 -/
theorem memLp_bounded_mul (ν : Measure α) (m : α → ℝ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ x, |m x| ≤ C)
    (f : ScalarL2 ν) : MemLp (fun x => m x * f x) 2 ν := by
  have hmeas : AEStronglyMeasurable (fun x => m x * f x) ν :=
    hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  apply (Lp.memLp f).of_le_mul hmeas
  filter_upwards [] with x
  -- 范数比较 |m f| ≤ C |f| 将可积性传给乘积，不要求 ν 是有限测度。
  simpa only [norm_mul, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg (f x))

private def boundedMulLinear (ν : Measure α) (m : α → ℝ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ x, |m x| ≤ C) :
    ScalarL2 ν →ₗ[ℝ] ScalarL2 ν where
  toFun f := (memLp_bounded_mul ν m hm C hbound f).toLp (fun x => m x * f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_bounded_mul ν m hm C hbound (f + g)).coeFn_toLp,
      (memLp_bounded_mul ν m hm C hbound f).coeFn_toLp,
      (memLp_bounded_mul ν m hm C hbound g).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add
        ((memLp_bounded_mul ν m hm C hbound f).toLp (fun x => m x * f x))
        ((memLp_bounded_mul ν m hm C hbound g).toLp (fun x => m x * g x))]
      with x hsum hf hg hfg hresult
    simp only [Pi.add_apply] at hresult hfg
    rw [hsum, hresult, hf, hg, hfg, mul_add]
  map_smul' r f := by
    apply Lp.ext
    filter_upwards [(memLp_bounded_mul ν m hm C hbound (r • f)).coeFn_toLp,
      (memLp_bounded_mul ν m hm C hbound f).coeFn_toLp,
      Lp.coeFn_smul r f,
      Lp.coeFn_smul r
        ((memLp_bounded_mul ν m hm C hbound f).toLp (fun x => m x * f x))]
      with x hr hf hrf hresult
    simp only [Pi.smul_apply, smul_eq_mul] at hrf hresult
    simp only [RingHom.id_apply]
    rw [hr, hresult, hf, hrf]
    ring

/-- 将实际乘法 f↦m f 封装为连续线性映射。
用于 V7 (6.2) 的有界系数项；Measurable 和 |m|≤C 是输入，连续性由范数界证明。
等价类上的线性关系通过 Lp.ext 的 a.e. 证明建立，未读取某个特殊代表元的点值。 -/
def boundedMul (ν : Measure α) (m : α → ℝ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ x, |m x| ≤ C) :
    ScalarL2 ν →L[ℝ] ScalarL2 ν :=
  (boundedMulLinear ν m hm C hbound).mkContinuous C (by
    intro f
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(memLp_bounded_mul ν m hm C hbound f).coeFn_toLp] with x hx
    change ‖((memLp_bounded_mul ν m hm C hbound f).toLp _) x‖ ≤ C * ‖f x‖
    rw [hx, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg (f x)))

/-- 乘子的代表函数只在 a.e. 意义下等于 m f。
源于上一构造；后续积分改写和加权零延拓都使用此等式。 -/
theorem coeFn_boundedMul (ν : Measure α) (m : α → ℝ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ x, |m x| ≤ C) (f : ScalarL2 ν) :
    ⇑(boundedMul ν m hm C hbound f) =ᵐ[ν] fun x => m x * f x :=
  (memLp_bounded_mul ν m hm C hbound f).coeFn_toLp

/-- 实际乘子范数控制：‖m f‖₂≤C‖f‖₂。
这是有界乘子的结论，不是假设；无界权重 w 不可直接套用。 -/
theorem norm_boundedMul_le (ν : Measure α) (m : α → ℝ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ x, |m x| ≤ C) (f : ScalarL2 ν) :
    ‖boundedMul ν m hm C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_boundedMul ν m hm C hbound f] with x hx
  rw [hx, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg (f x))

/-- 两个真实 L² 函数的乘积可积；V7 (6.2) 的交叉项使用此结论。
mathlib 用 L² 的 Hölder 性质证明，而非依赖不可积积分的总定义。 -/
theorem integrable_product (ν : Measure α) (f g : ScalarL2 ν) :
    Integrable (fun x => f x * g x) ν := by
  simpa only [Real.inner_apply] using (L2.integrable_inner (𝕜 := ℝ) f g)

/-- 实际 L² 内积等于乘积的空间积分；用于连接 (6.2) 内积表达与已有点态密度。 -/
theorem inner_eq_integral (ν : Measure α) (f g : ScalarL2 ν) :
    ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂ν := by
  simp only [L2.inner_def, Real.inner_apply]

/-- L² 范数平方是实际平方积分；平方可积由 Lp.memLp 给出。
源于 V7 (6.2)、(6.4) 的各普通平方项。 -/
theorem norm_sq_eq_integral (ν : Measure α) (f : ScalarL2 ν) :
    ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_integral]
  simp only [pow_two]

/-- 有界系数交叉密度 m f g 可积。
这是 (6.2) 变系数极化交叉项合法性的入口；先构造 m f∈L²，再用 L²×L²⊂L¹。 -/
theorem integrable_boundedMul_product (ν : Measure α) (m : α → ℝ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ x, |m x| ≤ C)
    (f g : ScalarL2 ν) :
    Integrable (fun x => m x * f x * g x) ν := by
  have hproduct : Integrable (fun x => (boundedMul ν m hm C hbound f) x * g x) ν :=
    integrable_product ν _ g
  apply hproduct.congr
  filter_upwards [coeFn_boundedMul ν m hm C hbound f] with x hx
  rw [hx]

/-- 有界系数的积分/内积对应：⟪M_m f,g⟫=∫mfg。
源于 V7 (6.2)；等式使用 a.e. 改写，不依赖 L² 代表函数的任意选择。 -/
theorem inner_boundedMul_eq_integral (ν : Measure α) (m : α → ℝ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ x, |m x| ≤ C)
    (f g : ScalarL2 ν) :
    ⟪boundedMul ν m hm C hbound f, g⟫_ℝ = ∫ x, m x * f x * g x ∂ν := by
  rw [inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [coeFn_boundedMul ν m hm C hbound f] with x hx
  rw [hx]

end Multiplication

section TimeCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- 实际内积路径乘积法则：(⟪X,Y⟫)'=⟪X,Y'⟫+⟪X',Y⟫。
由 V7 (6.2) 的交叉项推出，原文未单列；Xdot/Ydot 必须绑定真实 HasDerivAt。
本项目能量求导直接调用它；不使用逐点微分与积分交换。 -/
theorem hasDerivAt_inner {X Y : ℝ → H} {Xdot Ydot : H} {t : ℝ}
    (hX : HasDerivAt X Xdot t) (hY : HasDerivAt Y Ydot t) :
    HasDerivAt (fun s => ⟪X s, Y s⟫_ℝ)
      (⟪X t, Ydot⟫_ℝ + ⟪Xdot, Y t⟫_ℝ) t :=
  hX.inner ℝ hY

/-- 平方范数除以 2 的真实求导：½(‖X‖²)'=⟪X,X'⟫。
来自 (6.2) 的平方项；适用于实际普通及后续加权空间中的路径，
但必须给出相应空间范数下的 HasDerivAt，不能只给逐点导数。 -/
theorem hasDerivAt_half_norm_sq {X : ℝ → H} {Xdot : H} {t : ℝ}
    (hX : HasDerivAt X Xdot t) :
    HasDerivAt (fun s => ‖X s‖ ^ 2 / 2) ⟪X t, Xdot⟫_ℝ t := by
  -- mathlib 先给出 2⟪X,X'⟫；div_const 处理常数，ring 只约去导数值中的 2。
  exact (hX.norm_sq.div_const 2).congr_deriv (by ring)

/-- 固定空间算子作用后的真实导数：(M X)'=M X'。
在本阶段 M 是已构造的有界乘子或零延拓映射，不能据此把任意 M 称为空间梯度。 -/
theorem hasDerivAt_operator (M : H →L[ℝ] H)
    {X : ℝ → H} {Xdot : H} {t : ℝ} (hX : HasDerivAt X Xdot t) :
    HasDerivAt (fun s => M (X s)) (M Xdot) t :=
  M.hasFDerivAt.comp_hasDerivAt t hX

/-- 固定系数交叉项求导：(⟪M X,Y⟫)'=⟪M X,Y'⟫+⟪M X',Y⟫。
源于 (6.2) 的变系数项；M 不随时间变化，这正是没有额外 M' 项的原因。 -/
theorem hasDerivAt_operator_inner (M : H →L[ℝ] H)
    {X Y : ℝ → H} {Xdot Ydot : H} {t : ℝ}
    (hX : HasDerivAt X Xdot t) (hY : HasDerivAt Y Ydot t) :
    HasDerivAt (fun s => ⟪M (X s), Y s⟫_ℝ)
      (⟪M (X t), Ydot⟫_ℝ + ⟪M Xdot, Y t⟫_ℝ) t := by
  have hMX : HasDerivAt (fun s => M (X s)) (M Xdot) t :=
    hasDerivAt_operator M hX
  exact hasDerivAt_inner hMX hY

/-- 二次项是交叉项 X=Y 的实例；此处不要求 M 自伴，也不偷换两个交叉项。
(6.2) 的固定变系数平方项以此形式求导。 -/
theorem hasDerivAt_operator_quadratic (M : H →L[ℝ] H)
    {X : ℝ → H} {Xdot : H} {t : ℝ} (hX : HasDerivAt X Xdot t) :
    HasDerivAt (fun s => ⟪M (X s), X s⟫_ℝ)
      (⟪M (X t), Xdot⟫_ℝ + ⟪M Xdot, X t⟫_ℝ) t :=
  hasDerivAt_operator_inner M hX hX

end TimeCalculus
end LeanPML.Analysis
