import LeanPML.PML.WeightedMemoryBound
import LeanPML.Examples.WeakAnalysis

/-!
# 加权成员传播的非零实际场调用

在整个 (-1,1)² 上，取不对称系数 c=4,p=1,r=0,S=1。
本例验证辅助演化接口，不是材料阈值证书或完整 PDE 解。
φ(t)=exp(-t) f，h=0，l=φ，满足 l=h+φ；f 是已有非零光滑紧支场的 L² 类。
加权历史由新定理构造并识别，不预先输入全时段加权成员。
-/
noncomputable section
open MeasureTheory Set
open LeanPML.Analysis LeanPML.PML LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
namespace LeanPML.Examples.WeightedEvolution

/-- 单向吸收实例。只核验本文件用到的幅度条件，不冒充最终阈值实例。 -/
def coefficients : SpatialAbsorption (ℝ × ℝ) where
  c := 4
  S := 1
  c_pos := by norm_num
  p := fun _ => 1
  r := fun _ => 0
  p_measurable := measurable_const
  r_measurable := measurable_const
  p_nonneg := fun _ => by norm_num
  r_nonneg := fun _ => by norm_num
  p_le_S := fun _ => le_rfl
  r_le_S := fun _ => by norm_num
  S_le_quarter := by norm_num

/-- 真实非零空间场，不是一个普通实数命名的 L² 范数。 -/
def f : ScalarL2 unitSquare.measure := SmoothField.toL2 unitSquare WeakSpaces.physicalTest.field

/-- 从一个普通 L² 场构造初始加权成员。p=1，故物理恢复就是原 f。 -/
def initial : WeightedL2 unitSquare.measure coefficients.wx :=
  coefficients.xAbsorptionLift unitSquare.measure false f

private theorem p_operator (g : ScalarL2 unitSquare.measure) :
    coefficients.pCoeff.operator unitSquare.measure g = g := by
  change (BoundedCoefficient.const 1).operator unitSquare.measure g = g
  rw [BoundedCoefficient.operator_const, one_smul]

theorem initial_physical :
    physicalL2 unitSquare.measure coefficients.wx coefficients.wx_measurable
      coefficients.wx_gap initial = f := by
  rw [initial, coefficients.physical_xAbsorptionLift]
  exact p_operator f

/-- 非恒定普通 L² 路径，其真实导数由实指数求导与常向量数乘得到。 -/
def path (t : ℝ) : ScalarL2 unitSquare.measure := Real.exp (-t) • f

theorem path_derivative (t : ℝ) :
    HasDerivAt path
      (coefficients.rCoeff.operator unitSquare.measure 0 -
        coefficients.pCoeff.operator unitSquare.measure (path t)) t := by
  rw [map_zero, p_operator, zero_sub]
  have hderiv := ((hasDerivAt_id t).neg.exp).smul_const f
  convert hderiv using 1 <;> first | rfl | simp [path]

/-- 非零指数场调用新成员传播定理，结论在整个有限闭区间成立。
同时保留非零证据，避免只以零场检验接口。 -/
theorem nonzero_weighted_propagation (T t : ℝ) (ht : t ∈ Icc 0 T) :
    f ≠ 0 ∧ MemLp (fun x => Real.sqrt (coefficients.wx x) * path t x) 2 unitSquare.measure ∧
      (∀ᵐ x ∂unitSquare.measure, coefficients.wx x = 0 → path t x = 0) := by
  have hpath : Continuous path :=
    (Real.continuous_exp.comp continuous_neg).smul continuous_const
  have hinit : physicalL2 unitSquare.measure coefficients.wx coefficients.wx_measurable
      coefficients.wx_gap initial = path 0 := by simpa [path] using initial_physical
  exact ⟨WeakSpaces.physicalTest_nonzero_member.2,
    coefficients.auxiliary_weighted_membership unitSquare.measure initial path
      (fun _ => 0) path T hpath.continuousOn continuousOn_const hpath.continuousOn hinit
      (fun s _ => path_derivative s) ht⟩

/-- 同一非零场的加权历史真实可导；导数由通量右端构造。
这次调用与上一条的普通路径识别使用相同初值、h、l。 -/
theorem nonzero_weighted_path_derivative (T t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (coefficients.auxiliaryWeightedHistory unitSquare.measure initial (fun _ => 0) path)
      (coefficients.auxiliaryRateX unitSquare.measure 0 (path t)) t := by
  have hpath : Continuous path :=
    (Real.continuous_exp.comp continuous_neg).smul continuous_const
  exact coefficients.hasDerivAt_auxiliaryWeightedHistory unitSquare.measure initial
    (fun _ => 0) path T t continuousOn_const hpath.continuousOn ht

/-- 非零例的导数层右端也真实可导，并实际调用同一加权平方估计。
这里输入 dh=0、dl=−φ(t) 来自已证 path_derivative，不是自由导数数据。 -/
theorem nonzero_rate_derivative (t : ℝ) :
    HasDerivAt (fun s => coefficients.auxiliaryRateX unitSquare.measure 0 (path s))
      (coefficients.auxiliaryRateX unitSquare.measure 0 (-path t)) t ∧
    ‖coefficients.auxiliaryRateX unitSquare.measure 0 (-path t)‖ ^ 2 ≤
      2 * coefficients.c * coefficients.S * (‖(0 : ScalarL2 unitSquare.measure)‖ ^ 2 +
        ‖-path t‖ ^ 2) := by
  have hpath : HasDerivAt path (-path t) t := by
    simpa only [map_zero, p_operator, zero_sub] using path_derivative t
  exact coefficients.hasDerivAt_auxiliaryRateX unitSquare.measure (fun _ => 0) path
    0 (-path t) t (hasDerivAt_const t 0) hpath

/-- 非零实际 L² 指数路径调用 (5.8) 的单方向定理。
本例 h=0，故右端梯度积分为零；此处保留一般定理给出的常数 2，
不是通过代入指数公式另证一个无关估计。原路径与加权历史的识别见前面的传播调用。 -/
theorem nonzero_memory_bound (T t : ℝ) (ht : t ∈ Icc 0 T) :
    f ≠ 0 ∧
    ‖coefficients.auxiliaryWeightedHistory unitSquare.measure initial (fun _ => 0) path t‖ ^ 2 ≤
      2 * ‖initial‖ ^ 2 := by
  have hpath : Continuous path :=
    (Real.continuous_exp.comp continuous_neg).smul continuous_const
  have hinit : physicalL2 unitSquare.measure coefficients.wx coefficients.wx_measurable
      coefficients.wx_gap initial = path 0 := by simpa [path] using initial_physical
  have hbound := coefficients.auxiliary_weighted_memory_bound unitSquare.measure initial
    path (fun _ => 0) path T hpath.continuousOn continuousOn_const hpath.continuousOn hinit
    (fun s _ => path_derivative s) (fun s _ => by simp) ht
  exact ⟨WeakSpaces.physicalTest_nonzero_member.2, by simpa using hbound⟩

end LeanPML.Examples.WeightedEvolution

