import LeanPML.PML.SpatialBalance

/-!
# V7 (7.1)、(7.3)、(7.4) 的实际 L² 块组合

这里把既有点态代数接到 v0.3.1 的内积表达式，不进行时间/积分交换。
U 和 dU 是实际空间坐标；上层 BalanceAbstract 通过 StateHasDerivAt 绑定导数。
无界权重只出现在加权内积中，不能当作普通 L² 乘子。
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open LeanPML.Analysis

namespace LeanPML.Analysis.BoundedCoefficient
variable {α : Type*} [MeasurableSpace α]

/-- 有界系数乘法的代表函数等式，只在几乎处处意义下使用。 -/
theorem coe_operator (k : BoundedCoefficient α) (ν : Measure α) (f : ScalarL2 ν) :
    ⇑(k.operator ν f) =ᵐ[ν] fun x => k.value x * f x :=
  coeFn_boundedMul ν k.value k.measurable k.bound k.abs_le f

/-- 实系数乘法在实际 L² 内积中自伴；由可积乘积的交换律推出。 -/
theorem inner_swap (k : BoundedCoefficient α) (ν : Measure α) (f g : ScalarL2 ν) :
    ⟪k.operator ν f, g⟫_ℝ = ⟪k.operator ν g, f⟫_ℝ := by
  rw [k.inner_operator, k.inner_operator]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- 系数相加对应实际算子相加。供块恒等式逐项展开使用。 -/
theorem operator_add (k m : BoundedCoefficient α) (ν : Measure α) (f : ScalarL2 ν) :
    (k.add m).operator ν f = k.operator ν f + m.operator ν f := by
  apply Lp.ext
  filter_upwards [(k.add m).coe_operator ν f, k.coe_operator ν f,
    m.coe_operator ν f, Lp.coeFn_add (k.operator ν f) (m.operator ν f)]
    with x hsum hk hm hrep
  simp only [Pi.add_apply] at hrep
  rw [hsum, hrep, hk, hm, add_value, add_mul]

/-- 系数相减同样在等价类上成立；不以逐点选代表元代替证明。 -/
theorem operator_sub (k m : BoundedCoefficient α) (ν : Measure α) (f : ScalarL2 ν) :
    (k.sub m).operator ν f = k.operator ν f - m.operator ν f := by
  apply Lp.ext
  filter_upwards [(k.sub m).coe_operator ν f, k.coe_operator ν f,
    m.coe_operator ν f, Lp.coeFn_sub (k.operator ν f) (m.operator ν f)]
    with x hsum hk hm hrep
  simp only [Pi.sub_apply] at hrep
  rw [hsum, hrep, hk, hm, sub_value, sub_mul]

/-- 常数系数乘法就是 L² 的实标量乘法。 -/
theorem operator_const (ν : Measure α) (k : ℝ) (f : ScalarL2 ν) :
    (const k).operator ν f = k • f := by
  apply Lp.ext
  filter_upwards [(const k).coe_operator ν f, Lp.coeFn_smul k f] with x hk hs
  simpa only [const_value, Pi.smul_apply, smul_eq_mul] using hk.trans hs.symm

/-- 有界系数乘常数；这里的系数有界，无界 w 从不调用本引理。 -/
theorem operator_mul_const (k : BoundedCoefficient α) (ν : Measure α)
    (r : ℝ) (f : ScalarL2 ν) :
    (k.mul (const r)).operator ν f = r • k.operator ν f := by
  apply Lp.ext
  filter_upwards [(k.mul (const r)).coe_operator ν f, k.coe_operator ν f,
    Lp.coeFn_smul r (k.operator ν f)] with x hprod hk hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hprod, hs, hk, mul_value, const_value]
  ring

theorem operator_const_mul (k : BoundedCoefficient α) (ν : Measure α)
    (r : ℝ) (f : ScalarL2 ν) :
    ((const r).mul k).operator ν f = r • k.operator ν f := by
  apply Lp.ext
  filter_upwards [((const r).mul k).coe_operator ν f, k.coe_operator ν f,
    Lp.coeFn_smul r (k.operator ν f)] with x hprod hk hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hprod, hs, hk, mul_value, const_value]
  ring

end LeanPML.Analysis.BoundedCoefficient

namespace LeanPML.PML
variable {α : Type*} [MeasurableSpace α]

/-- V7 (7.3) 的实际 L² 代数版。dv=V 是速度关系；真实时间证据由上层提供。
变系数展开、内积双线性及实乘子自伴，把已求得的能量率整理为主方程乘子。 -/
theorem electricRate_add_remainder (ν : Measure α) (C : SpatialAbsorption α)
    (ε : ℝ) (U dU : FieldState ν C.wx C.wy) (hv : dU.v = U.V) :
    electricRate ν C ε U dU + fieldElectricRemainder ν C ε U =
      ε * ⟪dU.V + C.aCoeff.operator ν U.V + C.bCoeff.operator ν U.v,
        U.V + C.c • U.v⟫_ℝ := by
  simp only [electricRate, fieldElectricRemainder, electricCoefficient, bcCoefficient, hv,
    BoundedCoefficient.operator_add, BoundedCoefficient.operator_sub,
    BoundedCoefficient.operator_const, BoundedCoefficient.operator_mul_const,
    inner_add_left, inner_add_right, inner_sub_left, real_inner_smul_left,
    real_inner_smul_right]
  rw [C.aCoeff.inner_swap ν U.V U.v, C.bCoeff.inner_swap ν U.V U.v]
  simp only [real_inner_comm]
  ring


/-- V7 (7.4) 的实际 L² 代数版。兼容及其导数关系已在这里作为低层输入；
上层从邻域真实路径求导得到后者。κ≠0 只用于把 v、V 写成极化坐标。
整个推理用有界乘子和内积，不把逐点求导自动提升成 L² 求导。 -/
theorem polarRate_add_remainder (ν : Measure α) (C : SpatialAbsorption α)
    (κ τ : ℝ) (U dU : FieldState ν C.wx C.wy)
    (hκ_ne : κ ≠ 0) (hv : dU.v = U.V) (hz : dU.z = U.R)
    (hcompat : PolarConstraint κ τ U) (hderived : PolarConstraint κ τ dU) :
    polarRate ν C κ τ U dU + fieldPolarRemainder ν C κ τ U dU.R =
      ⟪dU.R + C.aCoeff.operator ν U.R + C.bCoeff.operator ν U.z,
        U.V + C.c • U.v⟫_ℝ := by
  have hposition : U.v = κ⁻¹ • (U.z + τ • U.R) := by
    rw [show U.z + τ • U.R = κ • U.v from hcompat]
    simp [smul_smul, hκ_ne]
  have hvelocity : U.V = κ⁻¹ • (U.R + τ • dU.R) := by
    have hconstraint : U.R + τ • dU.R = κ • U.V := by
      simpa only [PolarConstraint, hv, hz] using hderived
    rw [hconstraint]
    simp [smul_smul, hκ_ne]
  -- 先消元，再展开有界系数及内积；每次交换乘子均由已证自伴性支撑。
  simp only [polarRate, fieldPolarRemainder, polarRCoefficient,
    polarCrossCoefficient, polarZCoefficient, polarRemainderCoefficient,
    bcCoefficient, hz, hposition, hvelocity,
    BoundedCoefficient.operator_add, BoundedCoefficient.operator_sub,
    BoundedCoefficient.operator_const, BoundedCoefficient.operator_mul_const,
    BoundedCoefficient.operator_const_mul,
    inner_add_left, inner_add_right, inner_sub_left,
    real_inner_smul_left, real_inner_smul_right, ← real_inner_self_eq_norm_sq]
  rw [C.aCoeff.inner_swap ν dU.R U.R,
    C.aCoeff.inner_swap ν U.z U.R,
    C.bCoeff.inner_swap ν dU.R U.z,
    C.bCoeff.inner_swap ν U.z U.R]
  simp only [real_inner_comm]
  -- 分母只有 κ、2κ，hκ_ne 保证清除分母合法；ring 只整理实数系数。
  field_simp
  ring


/-- V7 (7.1)–(7.4) 合成的实际空间恒等式。三个块均沿用 (6.2)/(7.7)
已有定义；μ 只乘电块、极化块。这里还保留主方程乘子和全部空间配对，
下一步才调用 Green，不能把它们提前设零。
输入中的导数槽与已求导约束是低层数据；BalanceAbstract 从真实路径推出它们。 -/
theorem fieldEnergyRate_blocks (ν : Measure α) (C : SpatialAbsorption α)
    (ε κ τ μ : ℝ) (U dU : FieldState ν C.wx C.wy) (gx gy : ScalarL2 ν)
    (hκ_ne : κ ≠ 0) (hv : dU.v = U.V) (hz : dU.z = U.R)
    (hcompat : PolarConstraint κ τ U) (hderived : PolarConstraint κ τ dU)
    (hψx : physicalX ν C dU.ψx =
      C.rCoeff.operator ν (spatialComponentX U) - C.pCoeff.operator ν U.Λx)
    (hψy : physicalY ν C dU.ψy =
      C.pCoeff.operator ν (spatialComponentY U) - C.rCoeff.operator ν U.Λy)
    (hΛx : dU.Λx = gx + physicalX ν C dU.ψx)
    (hΛy : dU.Λy = gy + physicalY ν C dU.ψy) :
    fieldEnergyRate ν C ε κ τ μ U dU + fieldDissipation ν C ε κ τ μ U dU.R =
      ⟪primitiveMain ν C ε μ U dU, U.V + C.c • U.v⟫_ℝ +
      ⟪gx + C.c • spatialComponentX U, U.Λx⟫_ℝ +
      ⟪gy + C.c • spatialComponentY U, U.Λy⟫_ℝ := by
  have helectric := electricRate_add_remainder ν C ε U dU hv
  have hpolar := polarRate_add_remainder ν C κ τ U dU hκ_ne hv hz hcompat hderived
  have hspatial := spatialRate_add_dissipation ν C U dU gx gy hψx hψy hΛx hΛy
  -- 内积双线性把主方程左侧分成 μ ε 电项与 μ 极化项；
  -- 三条已证明的块恒等式相加，空间零区项已经包含在 hspatial 中。
  simp only [primitiveMain, inner_add_left, real_inner_smul_left]
  have hμelectric := congrArg (fun value : ℝ => μ * value) helectric
  have hμpolar := congrArg (fun value : ℝ => μ * value) hpolar
  simp only [inner_add_left] at hμelectric hμpolar
  simp only [inner_add_left, real_inner_smul_left] at hspatial
  unfold fieldEnergyRate fieldDissipation
  linarith

end LeanPML.PML
