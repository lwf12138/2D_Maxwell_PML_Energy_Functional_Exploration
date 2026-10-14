import LeanPML.PML.MainSmoothRectangle
import LeanPML.Examples.PathHelpers
import LeanPML.Examples.FullDomainProfile

/-!
# v0.5.3：最终入口的四种吸收分支回归

来源：V7 (5.3)/(5.5) 与 §11.3 允许的退化子类，原文未单列以下调用测试。
原函数与实际历史取零，但系数分别为全零、仅x、仅y和双向非均匀剖面。
这用于检查同一具体主定理能接受所有分支，不代替 StaticMode 的非零静态解。
不增加 a 的正下界，也不对内部截回代表求空间导数。
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Topology ContDiff
open LeanPML.Rectangle LeanPML.PML LeanPML.PML.Concrete LeanPML.PML.SmoothRectangle
open LeanPML.Rectangle.ParameterCertificate
namespace LeanPML.Examples.Degenerate

/-- 全部为零的实际原八变量，仍逐项给出导数与原方程证据。 -/
def zeroFields : OriginalFields where
  E:=fun _ _=>0
  Hx:=fun _ _=>0
  Hy:=fun _ _=>0
  P:=fun _ _=>0
  Z1:=fun _ _=>0
  Z2:=fun _ _=>0
  Qx:=fun _ _=>0
  Qy:=fun _ _=>0

/-- 零场不是通过空方程得到的：任意时空点都有真实时间可导证据及八式。 -/
theorem zero_originalAt (ε κ τ μ : ℝ) (p r : ℝ→ℝ) (t : ℝ) (X : Point) :
    OriginalAt ε κ τ μ p r zeroFields t X := by
  refine
    { toOriginalHasDerivAt := ?_
      electric := ?_
      magneticX := ?_
      magneticY := ?_
      debye := ?_
      memory1 := ?_
      memory2 := ?_
      auxiliaryX := ?_
      auxiliaryY := ?_ }
  · constructor <;> simp only [zeroFields,dt,deriv_const] <;> exact hasDerivAt_const t 0
  all_goals simp [zeroFields,dt,spaceDx,spaceDy]

/-- 整个零历史函数相等，而非只有某点值相等。
因此在 fderiv 内也可以合法改写为常函数，不能直接把一个点值等式求导。 -/
@[simp] theorem integralLift_zero_function :
    integralLift (fun _ _ => 0) (fun _ => 0) = (fun _ _ => (0:ℝ)) := by
  funext t X
  simp [integralLift]

/-- 原历史与其零初始原函数也为零，给出后续光滑坐标识别。 -/
theorem zero_integralLift (t : ℝ) (X : Point) :
    integralLift zeroFields.E (fun _=>0) t X=0 := by simp [integralLift,zeroFields]

/-- 零快照的八个实际光滑分量。 -/
def zeroCoordinates : SmoothStateCoordinates := ⟨0,0,0,0,0,0,0,0⟩
def zeroData : SmoothStateData := constantStateData zeroCoordinates

/-- 对任意合法区域系数构造具体主定理输入；权重无界也可用，因辅助量确为零。
这里只输入真实原条件与原阈值，不把能量结论或完成的问题对象传入。 -/
def zeroSolution {D : Rect} (R : RegionalAbsorption D) (T : ℝ) (hT : 0≤T)
    (hc : R.c≤threshold 1 1 1 1 (poincareConstant D)) :
    SmoothCompatibleSolution R 1 1 1 1 T where
  ε_pos:=by norm_num
  κ_pos:=by norm_num
  τ_pos:=by norm_num
  μ_pos:=by norm_num
  c_le_threshold:=hc
  F:=zeroFields
  u0:=fun _=>0
  q0:=fun _=>0
  B:=zeroData
  regular:=constantStateRegular D R.coefficients zeroCoordinates
    (weighted_zero_memLp D R.coefficients.wx) (weighted_zero_memLp D R.coefficients.wy)
  identified:=by
    constructor <;> funext t X <;>
      simp [zeroData,constantStateData,constantJet,zeroCoordinates,lift,zeroFields,
        spaceDx,spaceDy]
  T_nonneg:=hT
  history_regular:=by
    constructor
    all_goals first
      | intro X; exact continuous_const
      | simp only [zeroFields,integralLift_zero_function]
        exact contDiff_const
  equations:=fun t _ X _=>zero_originalAt 1 1 1 1 R.p R.r t X
  initial:=by
    intro X _
    constructor <;> simp [invariantD,invariantZ1,invariantZ2,invariantX,invariantY,
      lift,zeroFields,spaceDx,spaceDy]
  zero_initial:=by
    intro X _ _
    simp [lift,zeroFields,spaceDx,spaceDy]
  PEC:=by
    intro t _
    simp [ZeroBoundary,zeroFields]
  u0_boundary:=by simp [ZeroBoundary]
  degenerate:=by
    intro _
    constructor <;> intro X _
    all_goals simp [zeroData,constantStateData,constantJet,zeroCoordinates]

/-- 全零吸收分支，空间域仍是整个(-1,1)²。 -/
def zeroRegional : RegionalAbsorption unitSquare :=
  { FullDomain.regional with
    p := fun _ => 0
    r := fun _ => 0
    p_smooth := contDiff_const
    r_smooth := contDiff_const
    p_bounds := fun _ _ => ⟨le_rfl,amplitudeS_pos.le⟩
    r_bounds := fun _ _ => ⟨le_rfl,amplitudeS_pos.le⟩ }
/-- 不对称x方向吸收：p为真实剖面，r全零。 -/
def xRegional : RegionalAbsorption unitSquare :=
  { FullDomain.regional with
    r := fun _ => 0
    r_smooth := contDiff_const
    r_bounds := fun _ _ => ⟨le_rfl,amplitudeS_pos.le⟩ }
/-- 交换方向后的y吸收；没有沿用错误的x/y耗散系数次序。 -/
def yRegional : RegionalAbsorption unitSquare :=
  { FullDomain.regional with
    p := fun _ => 0
    p_smooth := contDiff_const
    p_bounds := fun _ _ => ⟨le_rfl,amplitudeS_pos.le⟩ }

/-- 同一小量证书可用于四种吸收形状，阈值与幅度不是从零场推出来的。 -/
theorem branch_thresholds :
    zeroRegional.c≤threshold 1 1 1 1 (poincareConstant unitSquare) ∧
    xRegional.c≤threshold 1 1 1 1 (poincareConstant unitSquare) ∧
    yRegional.c≤threshold 1 1 1 1 (poincareConstant unitSquare) ∧
    FullDomain.regional.c≤threshold 1 1 1 1 (poincareConstant unitSquare) :=
  ⟨unitSquare_le_threshold,unitSquare_le_threshold,unitSquare_le_threshold,unitSquare_le_threshold⟩

/-- 两个单向入口的系数确实不同：在各自边层点只对应方向为正。
这与仅测p=r的对称数值例不同，系数是实际非均匀函数。 -/
theorem asymmetric_directions :
    0<xRegional.p (7/8) ∧ xRegional.r 0=0 ∧
    yRegional.p 0=0 ∧ 0<yRegional.r (7/8) := by
  have hpositive : 0<FullDomain.profile (7/8) :=
    (FullDomain.profile_pos_iff _).mpr (by norm_num)
  exact ⟨hpositive,rfl,rfl,hpositive⟩

/-- 四个具体区域入口全部实际调用本轮最终定理，包括T=0。
输出含图界、真实能量律、积分平衡和原场控制，不只测试参数结构可构造。 -/
theorem four_branches_main (T : ℝ) (hT : 0≤T) :
    SmoothEnergyConclusions (zeroSolution zeroRegional T hT branch_thresholds.1) ∧
    SmoothEnergyConclusions (zeroSolution xRegional T hT branch_thresholds.2.1) ∧
    SmoothEnergyConclusions (zeroSolution yRegional T hT branch_thresholds.2.2.1) ∧
    SmoothEnergyConclusions (zeroSolution FullDomain.regional T hT branch_thresholds.2.2.2) :=
  ⟨main_energy_estimate_smoothRectangle _,main_energy_estimate_smoothRectangle _,
    main_energy_estimate_smoothRectangle _,main_energy_estimate_smoothRectangle _⟩

end LeanPML.Examples.Degenerate
