import LeanPML.Analysis.WeightedL2Operators
import LeanPML.Analysis.OperatorMemory
import Mathlib.Topology.ContinuousMap.Compact

/-!
# V7 (5.7)：有界吸收乘子的指数就是标量指数乘法

先在系数值域的紧区间上建立连续函数代数的乘法表示，再调用 mathlib 的
`NormedSpace.map_exp`。该定理以连续代数同态交换收敛幂级数，避免在 L²
商类上读取某点的值。这里只要求吸收系数有界；加权空间的 w 可以无界、为零。
最后的代表公式是每个给定时间的 a.e. 等式，不交换时间与零测集的量词。
-/
noncomputable section
open MeasureTheory
namespace LeanPML.Analysis
variable {α : Type*} [MeasurableSpace α]

/-- 加权乘子的平方根坐标代表；由既有 boundedMul 的 a.e. 表示推出。
用于核验下面代数同态的加法和乘法，未改变 WeightedL2 的等价类定义。 -/
theorem coeFn_weightedMul (ν : Measure α) (w m : α → ℝ) (hm : Measurable m)
    (C : ℝ) (hbound : ∀ x, |m x| ≤ C) (X : WeightedL2 ν w) :
    ⇑(weightedMul ν w m hm C hbound X).val =ᵐ[ν] fun x => m x * X.val x :=
  coeFn_boundedMul ν m hm C hbound X.val

section FunctionalCalculus
variable (ν : Measure α) (w : α → ℝ) (C : ℝ)
variable (m : α → Set.Icc (-C) C) (hm : Measurable m)

/-- 将系数值域上的连续函数 F 解释为乘 F(m(x)) 的加权算子。
紧值域只控制 F(m)，不要求空间权重 w 有界。 -/
def weightedFunctional (F : C(Set.Icc (-C) C, ℝ)) :
    WeightedL2 ν w →L[ℝ] WeightedL2 ν w :=
  weightedMul ν w (fun x => F (m x)) (F.continuous.measurable.comp hm) ‖F‖
    (fun x => F.norm_coe_le_norm (m x))

private theorem functional_coe (F : C(Set.Icc (-C) C, ℝ)) (X : WeightedL2 ν w) :
    ⇑(weightedFunctional ν w C m hm F X).val =ᵐ[ν] fun x => F (m x) * X.val x :=
  coeFn_weightedMul ν w _ _ _ _ X

/-- F↦M_(F∘m) 是真正的实代数同态。所有等式都在加权商类上证明。
此构造使幂、幂级数和指数具有同一个实际调用者，而非独立形式运算。 -/
def weightedFunctionalAlgHom :
    C(Set.Icc (-C) C, ℝ) →ₐ[ℝ] (WeightedL2 ν w →L[ℝ] WeightedL2 ν w) where
  toFun := weightedFunctional ν w C m hm
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro X
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [functional_coe ν w C m hm 0 X, Lp.coeFn_zero ℝ 2 ν] with x hleft hz
    simpa using hleft.trans (by simpa using hz.symm)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro X
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [functional_coe ν w C m hm 1 X] with x hleft
    simpa using hleft
  map_add' F G := by
    apply ContinuousLinearMap.ext
    intro X
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [functional_coe ν w C m hm (F+G) X,
      functional_coe ν w C m hm F X, functional_coe ν w C m hm G X,
      Lp.coeFn_add (weightedFunctional ν w C m hm F X).val
        (weightedFunctional ν w C m hm G X).val] with x hsum hF hG hadd
    change _ = (((weightedFunctional ν w C m hm F X).val +
      (weightedFunctional ν w C m hm G X).val : ScalarL2 ν) x)
    rw [hsum, hadd, Pi.add_apply, hF, hG]
    simp only [ContinuousMap.add_apply]
    ring
  map_mul' F G := by
    apply ContinuousLinearMap.ext
    intro X
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [functional_coe ν w C m hm (F*G) X,
      functional_coe ν w C m hm F (weightedFunctional ν w C m hm G X),
      functional_coe ν w C m hm G X] with x hprod hF hG
    change _ = (weightedFunctional ν w C m hm F (weightedFunctional ν w C m hm G X)).val x
    rw [hprod, hF, hG]
    simp only [ContinuousMap.mul_apply]
    ring
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro X
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [functional_coe ν w C m hm (algebraMap ℝ _ r) X,
      Lp.coeFn_smul r X.val] with x hleft hright
    change _ = ((r • X.val : ScalarL2 ν) x)
    rw [hleft, hright]
    rfl

/-- 上述代数同态是连续的：算子范数 ≤ 连续系数函数的一致范数。
该估计合法交换指数级数；并未给无界 w 安装有界乘法算子。 -/
theorem weightedFunctional_continuous : Continuous (weightedFunctionalAlgHom ν w C m hm) := by
  let representation : C(Set.Icc (-C) C, ℝ) →ₐ[ℝ] (WeightedL2 ν w →L[ℝ] WeightedL2 ν w) := weightedFunctionalAlgHom ν w C m hm
  have hbound : ∀ F, ‖representation F‖ ≤ 1 * ‖F‖ := by
    intro F
    rw [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
    intro X
    exact weightedMul_norm_le ν w _ _ _ _ X
  let linear : C(Set.Icc (-C) C, ℝ) →ₗ[ℝ] (WeightedL2 ν w →L[ℝ] WeightedL2 ν w) := representation.toLinearMap
  have hlinear : ∀ F, ‖linear F‖ ≤ 1 * ‖F‖ := hbound
  exact (LinearMap.mkContinuous (𝕜 := ℝ) (E := C(Set.Icc (-C) C, ℝ))
    (F := WeightedL2 ν w →L[ℝ] WeightedL2 ν w) linear 1 hlinear).continuous

/-- 连续函数代数中的指数逐点为实指数；由连续求值同态交换指数得到。
这是数学上的函数演算，不是 L² 商类的非法点值求取。 -/
theorem continuousMap_exp_apply (F : C(Set.Icc (-C) C, ℝ)) (z : Set.Icc (-C) C) :
    NormedSpace.exp F z = Real.exp (F z) := by
  have heval := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ z)
    (continuous_eval_const z) F
  simpa only [ContinuousMap.evalAlgHom_apply, Real.exp_eq_exp_ℝ] using heval

end FunctionalCalculus

omit [MeasurableSpace α] in
/-- 标量指数系数有明确有限界；这里只对有界吸收 m 作指数。
时间 t 可正可负，不除以 m，因此包含零吸收分支。 -/
theorem exp_multiplier_bound (m : α → ℝ) (C : ℝ)
    (hbound : ∀ x, |m x| ≤ C) (t : ℝ) (x : α) :
    |Real.exp (t * m x)| ≤ Real.exp (|t| * C) := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * m x ≤ |t * m x| := le_abs_self _
    _ = |t| * |m x| := abs_mul _ _
    _ ≤ |t| * C := mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg t)

/-- 论文 (5.7) 中真正的标量指数乘子，作用于加权等价类。
下条定理将它与已用的算子指数识别；不是另设无联系的历史。 -/
def scalarExpMultiplier (ν : Measure α) (w m : α → ℝ) (hm : Measurable m)
    (C : ℝ) (hbound : ∀ x, |m x| ≤ C) (t : ℝ) :
    WeightedL2 ν w →L[ℝ] WeightedL2 ν w :=
  weightedMul ν w (fun x => Real.exp (t * m x))
    ((measurable_const.mul hm).exp) (Real.exp (|t| * C))
    (exp_multiplier_bound m C hbound t)

/-- 连续代数同态与指数交换的算子版本；固定范数拓扑后供具体闭子空间调用。 -/
theorem functional_exp_kernel {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (representation : C(K, ℝ) →ₐ[ℝ] (H →L[ℝ] H))
    (hcontinuous : Continuous representation) (F : C(K, ℝ))
    (B : H →L[ℝ] H) (t : ℝ) (hscaled : representation F = t • B) :
    representation (NormedSpace.exp F) = dampingKernel B t := by
  have hexp := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) representation hcontinuous F
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
  rw [hscaled] at hexp
  exact hexp

/-- V7 (5.7) 的核识别：exp(t M_m)=M_(exp(tm))，等式在实际 WeightedL2 算子上成立。
证明路线：紧系数值域 → 连续代数同态 → 合法指数级数 → 商类 a.e. 识别。
w 的可测性只用于加权空间完备性；无吸收正下界或权重上界。 -/
theorem dampingKernel_eq_scalarExpMultiplier (ν : Measure α) (w m : α → ℝ)
    (hw : Measurable w) (hm : Measurable m) (C : ℝ)
    (hbound : ∀ x, |m x| ≤ C) (t : ℝ) :
    dampingKernel (weightedMul ν w m hm C hbound) t =
      scalarExpMultiplier ν w m hm C hbound t := by
  letI : CompleteSpace (WeightedL2 ν w) := weighted_completeSpace ν w hw
  let coefficient : α → Set.Icc (-C) C := fun x => ⟨m x, abs_le.mp (hbound x)⟩
  have hcoefficient : Measurable coefficient := hm.subtype_mk
  let F : C(Set.Icc (-C) C, ℝ) := ⟨fun z => t * z.val, continuous_const.mul continuous_subtype_val⟩
  let representation := weightedFunctionalAlgHom ν w C coefficient hcoefficient
  have hscaled : representation F = t • weightedMul ν w m hm C hbound := by
    apply ContinuousLinearMap.ext
    intro X
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [functional_coe ν w C coefficient hcoefficient F X,
      coeFn_weightedMul ν w m hm C hbound X,
      Lp.coeFn_smul t (weightedMul ν w m hm C hbound X).val] with x hF hmX hsmul
    change (weightedFunctional ν w C coefficient hcoefficient F X).val x =
      ((t • (weightedMul ν w m hm C hbound X).val : ScalarL2 ν) x)
    rw [hF, hsmul, Pi.smul_apply, smul_eq_mul, hmX]
    change (t * m x) * X.val x = t * (m x * X.val x)
    ring
  have hexp := functional_exp_kernel representation
    (weightedFunctional_continuous ν w C coefficient hcoefficient) F
    (weightedMul ν w m hm C hbound) t hscaled
  rw [← hexp]
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [functional_coe ν w C coefficient hcoefficient (NormedSpace.exp F) X,
    coeFn_weightedMul ν w (fun x => Real.exp (t * m x)) ((measurable_const.mul hm).exp) _
      (exp_multiplier_bound m C hbound t) X] with x hleft hright
  change (weightedFunctional ν w C coefficient hcoefficient (NormedSpace.exp F) X).val x =
    (weightedMul ν w (fun x => Real.exp (t * m x)) _ _ _ X).val x
  rw [hleft, hright, continuousMap_exp_apply]
  rfl

/-- 每个固定 t 的平方根坐标 a.e. 公式；不声称存在共同零测集使所有 t 同时成立。
与上一算子等式一起用于论文标量核的空间值记忆表示。 -/
theorem dampingKernel_coe (ν : Measure α) (w m : α → ℝ)
    (hw : Measurable w) (hm : Measurable m) (C : ℝ)
    (hbound : ∀ x, |m x| ≤ C) (t : ℝ) (X : WeightedL2 ν w) :
    ⇑(dampingKernel (weightedMul ν w m hm C hbound) t X).val =ᵐ[ν]
      fun x => Real.exp (t * m x) * X.val x := by
  rw [dampingKernel_eq_scalarExpMultiplier ν w m hw hm C hbound t]
  exact coeFn_weightedMul ν w _ _ _ _ X

/-- 标量指数乘子经物理恢复变成普通 L² 上的同一乘法。
与 (5.7) 的原辅助场连接；公式只在商类意义下使用。 -/
theorem physical_scalarExpMultiplier (ν : Measure α) (w m : α → ℝ)
    (hw : Measurable w) (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ x, |m x| ≤ C)
    (t : ℝ) (X : WeightedL2 ν w) :
    physicalL2 ν w hw hgap (scalarExpMultiplier ν w m hm C hbound t X) =
      boundedMul ν (fun x => Real.exp (t * m x)) ((measurable_const.mul hm).exp)
        (Real.exp (|t| * C)) (exp_multiplier_bound m C hbound t)
        (physicalL2 ν w hw hgap X) :=
  physicalL2_weightedMul ν w _ hw hgap _ _ _ X

end LeanPML.Analysis
