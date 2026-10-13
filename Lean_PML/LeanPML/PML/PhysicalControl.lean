import LeanPML.PML.Coercivity

/-!
# V7 (6.10)、(8.4)–(8.8)：兼容提升后的实际 L² 场控制

本文件用已有的空间场和乘法算子重构 H、q、Z₁、Z₂、Q；
系数 p、r 可以随空间变化，w 的无界性由 WeightedL2 承载。
阅读顺序：reconstructQ → physicalControl_of_graph_bound → physicalControl_Conditional。
最后的主入口将调用 Coercivity 的参数阈值及条件性 Poincaré 估计。

这里证明给定兼容提升的控制，不证明原八变量 PDE 与 primitive 系统双向等价，
也不证明提升规范唯一。普通二维 L² 平方始终是两个分量平方之和。
-/

noncomputable section
open MeasureTheory
open LeanPML.Analysis

namespace LeanPML.PML
variable {α : Type*} [MeasurableSpace α]

/-- V7 (2.5)、(6.10)：λ=(μH_y,−μH_x) 的实际 L² 重构；
μ≠0 在核验逆关系及能量缩放时使用。 -/
def reconstructHx {ν : Measure α} {C : SpatialAbsorption α}
    (μ : ℝ) (U : FieldState ν C.wx C.wy) : ScalarL2 ν := (-μ⁻¹) • U.Λy

/-- 同上，H_y=μ⁻¹λ_x。 -/
def reconstructHy {ν : Measure α} {C : SpatialAbsorption α}
    (μ : ℝ) (U : FieldState ν C.wx C.wy) : ScalarL2 ν := μ⁻¹ • U.Λx

/-- V7 (2.5)、(8.5)：q=κu−τP，线性组合在真实 L² 中进行。 -/
def reconstructQ {ν : Measure α} {C : SpatialAbsorption α}
    (κ τ : ℝ) (U : FieldState ν C.wx C.wy) : ScalarL2 ν :=
  κ • U.v - τ • U.R

/-- V7 (2.5)、(8.6)：Z₁=−εbu。乘 b 使用从原始幅度条件构造的有界乘子，
并未把无界权重 w 当作普通 L² 乘子。 -/
def reconstructZ1 (ν : Measure α) (C : SpatialAbsorption α)
    (ε : ℝ) (U : FieldState ν C.wx C.wy) : ScalarL2 ν :=
  (-ε) • C.bCoeff.operator ν U.v

/-- V7 (2.5)、(8.7)：Z₂=−bq；q 使用上面的兼容重构。 -/
def reconstructZ2 (ν : Measure α) (C : SpatialAbsorption α)
    (κ τ : ℝ) (U : FieldState ν C.wx C.wy) : ScalarL2 ν :=
  -(C.bCoeff.operator ν (reconstructQ κ τ U))

/-- V7 (2.5)、(8.8)：Q_x=pφ_y。先由加权空间恢复普通 φ_y，再乘 p。 -/
def reconstructAuxX (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) : ScalarL2 ν :=
  C.pCoeff.operator ν (physicalY ν C U.ψy)

/-- V7 (2.5)、(8.8)：Q_y=−rφ_x；这里保留方向交叉及负号。 -/
def reconstructAuxY (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) : ScalarL2 ν :=
  -(C.rCoeff.operator ν (physicalX ν C U.ψx))

/-- V7 (6.1) 下，重构 q 与已有状态槽 z 相同。输入是极化约束，
输出为实际 L² 等价类相等，不是增加一个全时段 PDE 假设。 -/
theorem reconstructQ_eq_z {ν : Measure α} {C : SpatialAbsorption α}
    (κ τ : ℝ) (U : FieldState ν C.wx C.wy) (hpolar : PolarConstraint κ τ U) :
    reconstructQ κ τ U = U.z := by
  have hconstraint : U.z + τ • U.R = κ • U.v := hpolar
  unfold reconstructQ
  rw [← hconstraint, add_sub_cancel_right]

/-- 由 (6.10) 的重构关系推出：旋转及 μ 缩放没有丢失磁场；
这是 L² 场恒等式，不涉及 Maxwell 演化。 -/
theorem reconstruct_magnetic {ν : Measure α} {C : SpatialAbsorption α}
    (μ : ℝ) (hμ_ne : μ ≠ 0) (U : FieldState ν C.wx C.wy) :
    μ • reconstructHy μ U = U.Λx ∧ (-μ) • reconstructHx μ U = U.Λy := by
  constructor <;> simp [reconstructHx, reconstructHy, smul_smul, hμ_ne]

/-- 由 (8.5) 的 Young 估计推出，原文未单列：任意真实范数空间内，
差的平方不超过两个平方之和的两倍。后面用于 κu−τP。 -/
theorem norm_sub_sq_le_two {H : Type*} [SeminormedAddCommGroup H] (x y : H) :
    ‖x-y‖^2 ≤ 2*‖x‖^2 + 2*‖y‖^2 := by
  have htriangle : ‖x-y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have hsquare : ‖x-y‖^2 ≤ (‖x‖+‖y‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  have hyoung : 0 ≤ (‖x‖-‖y‖)^2 := sq_nonneg _
  nlinarith

/-- 由 (8.6)–(8.8) 推出，原文未单列：实际乘子的平方范数界。
先应用已有 L² 乘法算子范数估计，再平方；下游保留论文的精确 S²、S⁴。 -/
theorem coefficient_operator_norm_sq_le (ν : Measure α) (m : BoundedCoefficient α)
    (f : ScalarL2 ν) :
    ‖m.operator ν f‖^2 ≤ m.bound^2 * ‖f‖^2 := by
  have hnorm : ‖m.operator ν f‖ ≤ m.bound * ‖f‖ :=
    norm_boundedMul_le ν m.value m.measurable m.bound m.abs_le f
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simpa only [mul_pow] using hsquare

/-- 由 p≤S 推出，原文未单列：p 乘子的平方界为 S²。
内部保存的幅度界是 |S|，平方后正好成为 S²，不额外假设空间非空。 -/
theorem p_operator_norm_sq_le (ν : Measure α) (C : SpatialAbsorption α)
    (f : ScalarL2 ν) :
    ‖C.pCoeff.operator ν f‖^2 ≤ C.S^2 * ‖f‖^2 := by
  simpa only [SpatialAbsorption.pCoeff, sq_abs] using
    coefficient_operator_norm_sq_le ν C.pCoeff f

/-- 同一实际乘子估计用于 r。 -/
theorem r_operator_norm_sq_le (ν : Measure α) (C : SpatialAbsorption α)
    (f : ScalarL2 ν) :
    ‖C.rCoeff.operator ν f‖^2 ≤ C.S^2 * ‖f‖^2 := by
  simpa only [SpatialAbsorption.rCoeff, sq_abs] using
    coefficient_operator_norm_sq_le ν C.rCoeff f

/-- 由 b=pr、p,r≤S 推出：b 的平方乘子界为 S⁴。
没有除以 p、r、a；零吸收与单向吸收均保留。 -/
theorem b_operator_norm_sq_le (ν : Measure α) (C : SpatialAbsorption α)
    (f : ScalarL2 ν) :
    ‖C.bCoeff.operator ν f‖^2 ≤ C.S^4 * ‖f‖^2 := by
  have hbound := coefficient_operator_norm_sq_le ν C.bCoeff f
  have hfour : (|C.S| * |C.S|)^2 = C.S^4 := by
    rw [mul_pow, sq_abs]
    ring
  simpa only [SpatialAbsorption.bCoeff, BoundedCoefficient.mul,
    SpatialAbsorption.pCoeff, SpatialAbsorption.rCoeff, hfour] using hbound

/-- V7 (6.10)、(8.4)–(8.8) 的结论包：所有槽是具体 L² 重构，
右侧使用已定义的两层能量及论文 K。字段是待证明的输出，不能作为模型输入。 -/
structure PhysicalControlBounds (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (U₀ U₁ : FieldState ν C.wx C.wy) : Prop where
  physical :
    ε * ‖U₀.V‖^2 +
      μ * (‖reconstructHx μ U₀‖^2 + ‖reconstructHy μ U₀‖^2) +
      κ⁻¹ * ‖U₀.R‖^2 ≤
        (4/μ) * twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP) U₀ U₁
  displacement :
    ‖U₀.v‖^2 ≤ 8*CP^2 * twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP) U₀ U₁
  auxiliary :
    ‖physicalX ν C U₀.ψx‖^2 + ‖physicalY ν C U₀.ψy‖^2 ≤
      4 * twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP) U₀ U₁
  primitivePolar :
    ‖reconstructQ κ τ U₀‖^2 ≤ (16*κ^2*CP^2 + 8*κ*τ^2/μ) *
      twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP) U₀ U₁
  electricMemory :
    ‖reconstructZ1 ν C ε U₀‖^2 ≤ 8*ε^2*C.S^4*CP^2 *
      twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP) U₀ U₁
  polarMemory :
    ‖reconstructZ2 ν C κ τ U₀‖^2 ≤
      C.S^4*(16*κ^2*CP^2 + 8*κ*τ^2/μ) *
      twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP) U₀ U₁
  magneticAuxiliary :
    ‖reconstructAuxX ν C U₀‖^2 + ‖reconstructAuxY ν C U₀‖^2 ≤
      4*C.S^2 * twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP) U₀ U₁

/-- V7 §8.3 的控制计算层：从 N₀²≤4E₇ 和 (8.3) 推出全部重构界。
输入 hgraph、hdisplacement 是前一节已证估计的中间结果；后面的条件性主入口
会从原参数、空间约束及 Poincaré 调出它们，不把这两个目标界留作最终假设。 -/
theorem physicalControl_of_graph_bound (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (U₀ U₁ : FieldState ν C.wx C.wy)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ) (hμ_pos : 0 < μ)
    (hgraph : graphSquare ε κ μ U₀ ≤
      4 * twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP) U₀ U₁)
    (hdisplacement : ‖U₀.v‖^2 ≤
      2*CP^2*(‖U₀.Λx‖^2+‖U₀.Λy‖^2+‖U₀.ψx‖^2+‖U₀.ψy‖^2)) :
    PhysicalControlBounds ν C ε κ τ μ CP U₀ U₁ := by
  let E7 := twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP) U₀ U₁
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
  have hκ_ne : κ ≠ 0 := ne_of_gt hκ_pos
  have hvelocity_nonneg : 0 ≤ μ*ε*‖U₀.V‖^2 :=
    mul_nonneg (mul_nonneg hμ_pos.le hε_pos.le) (sq_nonneg _)
  have hpolar_nonneg : 0 ≤ μ/κ*‖U₀.R‖^2 :=
    mul_nonneg (div_nonneg hμ_pos.le hκ_pos.le) (sq_nonneg _)
  have hbudget_le : ‖U₀.Λx‖^2+‖U₀.Λy‖^2+‖U₀.ψx‖^2+‖U₀.ψy‖^2 ≤
      4*E7 := by
    unfold graphSquare at hgraph
    dsimp only [E7]
    linarith
  have hR_weighted : μ/κ*‖U₀.R‖^2 ≤ 4*E7 := by
    unfold graphSquare at hgraph
    nlinarith [sq_nonneg ‖U₀.Λx‖, sq_nonneg ‖U₀.Λy‖,
      sq_nonneg ‖U₀.ψx‖, sq_nonneg ‖U₀.ψy‖]
  -- κ、μ 为正，才能以 κ/μ 保持不等号方向并消去分母。
  have hR_bound : ‖U₀.R‖^2 ≤ (4*κ/μ)*E7 := by
    calc
      ‖U₀.R‖^2 = (κ/μ)*(μ/κ*‖U₀.R‖^2) := by field_simp
      _ ≤ (κ/μ)*(4*E7) :=
        mul_le_mul_of_nonneg_left hR_weighted (div_nonneg hκ_pos.le hμ_pos.le)
      _ = (4*κ/μ)*E7 := by ring
  have hu_bound : ‖U₀.v‖^2 ≤ 8*CP^2*E7 := by
    calc
      ‖U₀.v‖^2 ≤ 2*CP^2*
          (‖U₀.Λx‖^2+‖U₀.Λy‖^2+‖U₀.ψx‖^2+‖U₀.ψy‖^2) := hdisplacement
      _ ≤ 2*CP^2*(4*E7) :=
        mul_le_mul_of_nonneg_left hbudget_le (by positivity)
      _ = 8*CP^2*E7 := by ring
  -- 在零吸收区 ψ=0 的信息已由 physicalX/Y 的构造保证；
  -- 此处使用的是已证加权嵌入，未要求零区的 w≥1。
  have hx_embedding : ‖physicalX ν C U₀.ψx‖^2 ≤ ‖U₀.ψx‖^2 :=
    physicalL2_norm_sq_le ν C.wx C.wx_measurable C.wx_gap U₀.ψx
  have hy_embedding : ‖physicalY ν C U₀.ψy‖^2 ≤ ‖U₀.ψy‖^2 :=
    physicalL2_norm_sq_le ν C.wy C.wy_measurable C.wy_gap U₀.ψy
  have hφ_bound : ‖physicalX ν C U₀.ψx‖^2+‖physicalY ν C U₀.ψy‖^2 ≤ 4*E7 := by
    nlinarith [sq_nonneg ‖U₀.Λx‖, sq_nonneg ‖U₀.Λy‖]
  have hq_young : ‖reconstructQ κ τ U₀‖^2 ≤
      2*κ^2*‖U₀.v‖^2 + 2*τ^2*‖U₀.R‖^2 := by
    simpa only [reconstructQ, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      mul_assoc] using norm_sub_sq_le_two (κ • U₀.v) (τ • U₀.R)
  have hq_bound : ‖reconstructQ κ τ U₀‖^2 ≤
      (16*κ^2*CP^2+8*κ*τ^2/μ)*E7 := by
    calc
      ‖reconstructQ κ τ U₀‖^2 ≤
          2*κ^2*‖U₀.v‖^2+2*τ^2*‖U₀.R‖^2 := hq_young
      _ ≤ 2*κ^2*(8*CP^2*E7)+2*τ^2*((4*κ/μ)*E7) :=
        add_le_add (mul_le_mul_of_nonneg_left hu_bound (by positivity))
          (mul_le_mul_of_nonneg_left hR_bound (by positivity))
      _ = (16*κ^2*CP^2+8*κ*τ^2/μ)*E7 := by ring
  constructor
  · -- λ 的旋转缩放恒等式先单独核对，再除以正数 μ。
    have hmagnetic :
        μ^2*(‖reconstructHx μ U₀‖^2+‖reconstructHy μ U₀‖^2) =
          ‖U₀.Λx‖^2+‖U₀.Λy‖^2 := by
      simp only [reconstructHx, reconstructHy, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs, neg_sq]
      field_simp
      ring
    have hphysical_weighted :
        μ*(ε*‖U₀.V‖^2+μ*(‖reconstructHx μ U₀‖^2+‖reconstructHy μ U₀‖^2)+
          κ⁻¹*‖U₀.R‖^2) ≤ 4*E7 := by
      unfold graphSquare at hgraph
      have hκ_inv : μ*κ⁻¹ = μ/κ := by rw [div_eq_mul_inv]
      nlinarith [sq_nonneg ‖U₀.ψx‖, sq_nonneg ‖U₀.ψy‖]
    have hscaled := mul_le_mul_of_nonneg_left hphysical_weighted (inv_nonneg.mpr hμ_pos.le)
    have hcancel : μ⁻¹*μ = 1 := inv_mul_cancel₀ hμ_ne
    dsimp only [E7] at hscaled
    simpa only [← mul_assoc, hcancel, one_mul, div_eq_mul_inv, mul_comm 4 μ⁻¹]
      using hscaled
  · exact hu_bound
  · exact hφ_bound
  · exact hq_bound
  · -- b 的算子界给 S⁴；ε 的常数缩放再给 ε²。
    calc
      ‖reconstructZ1 ν C ε U₀‖^2 =
          ε^2*‖C.bCoeff.operator ν U₀.v‖^2 := by
        simp only [reconstructZ1, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
      _ ≤ ε^2*(C.S^4*‖U₀.v‖^2) :=
        mul_le_mul_of_nonneg_left (b_operator_norm_sq_le ν C U₀.v) (sq_nonneg ε)
      _ ≤ ε^2*(C.S^4*(8*CP^2*E7)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hu_bound (by positivity)) (sq_nonneg ε)
      _ = 8*ε^2*C.S^4*CP^2*E7 := by ring
  · calc
      ‖reconstructZ2 ν C κ τ U₀‖^2 =
          ‖C.bCoeff.operator ν (reconstructQ κ τ U₀)‖^2 := by
        simp only [reconstructZ2, norm_neg]
      _ ≤ C.S^4*‖reconstructQ κ τ U₀‖^2 :=
        b_operator_norm_sq_le ν C (reconstructQ κ τ U₀)
      _ ≤ C.S^4*((16*κ^2*CP^2+8*κ*τ^2/μ)*E7) :=
        mul_le_mul_of_nonneg_left hq_bound (by positivity)
      _ = C.S^4*(16*κ^2*CP^2+8*κ*τ^2/μ)*E7 := by ring
  · calc
      ‖reconstructAuxX ν C U₀‖^2+‖reconstructAuxY ν C U₀‖^2 ≤
          C.S^2*‖physicalY ν C U₀.ψy‖^2+C.S^2*‖physicalX ν C U₀.ψx‖^2 := by
        simpa only [reconstructAuxX, reconstructAuxY, norm_neg] using
          add_le_add (p_operator_norm_sq_le ν C (physicalY ν C U₀.ψy))
            (r_operator_norm_sq_le ν C (physicalX ν C U₀.ψx))
      _ = C.S^2*(‖physicalX ν C U₀.ψx‖^2+‖physicalY ν C U₀.ψy‖^2) := by ring
      _ ≤ C.S^2*(4*E7) := mul_le_mul_of_nonneg_left hφ_bound (sq_nonneg _)
      _ = 4*C.S^2*E7 := by ring

/-- V7 (6.10)、(8.4)–(8.8) 的正式入口：在同源两层上，由原材料条件、
吸收幅度、极化/空间兼容及零迹 Poincaré 接口推出全部原状态控制。
阈值与双层正定界由 Coercivity 真正证明；输入中没有待证的能量控制式。
结论针对兼容提升的重构场，尚不包含原 PDE 的完整模型等价或提升唯一性。 -/
theorem physicalControl_Conditional (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ CP : ℝ) (hp : CoercivityParameters C ε κ τ μ CP)
    (spatial : ConditionalSpatialDomain ν) (poincare : ConditionalPoincare spatial CP)
    {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I) (t : ℝ)
    (hbase : StateCoercivityConstraints ν C spatial poincare κ τ (path.base t))
    (hfirst : StateCoercivityConstraints ν C spatial poincare κ τ (path.first t)) :
    PhysicalControlBounds ν C ε κ τ μ CP (path.base t) (path.first t) := by
  have htwoLayer := energy7_bounds_Conditional ν C ε κ τ μ CP hp
    spatial poincare path t hbase hfirst
  have hK_nonneg : 0 ≤ scaleK ε κ μ CP :=
    (scaleK_pos ε κ μ CP hp.ε_pos hp.κ_pos hp.μ_pos hp.CP_pos).le
  have hfirst_nonneg : 0 ≤ graphSquare ε κ μ (path.first t) :=
    graphSquare_nonneg ε κ μ hp.ε_pos.le hp.κ_pos.le hp.μ_pos.le _
  have hfirst_weighted_nonneg : 0 ≤
      scaleK ε κ μ CP * graphSquare ε κ μ (path.first t) :=
    mul_nonneg hK_nonneg hfirst_nonneg
  have hgraph : graphSquare ε κ μ (path.base t) ≤
      4 * twoLayerEnergy ν C ε κ τ μ (scaleK ε κ μ CP)
        (path.base t) (path.first t) := by
    unfold graphSquare7 twoLayerGraphSquare energy7 at htwoLayer
    linarith [htwoLayer.1]
  have hdisplacement := state_norm_sq_le_spatialBudget ν C spatial CP poincare
    κ τ (path.base t) hbase
  exact physicalControl_of_graph_bound ν C ε κ τ μ CP (path.base t) (path.first t)
    hp.ε_pos hp.κ_pos hp.μ_pos hgraph hdisplacement

end LeanPML.PML

