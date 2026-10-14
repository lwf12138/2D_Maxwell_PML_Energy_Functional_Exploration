import LeanPML.Examples.PathHelpers
import LeanPML.Examples.FullDomainProfile

/-!
# v0.5.2：物理区内的非平凡兼容初始数据

对应 V7 §11.1：材料均取1，u₀=0，E₀=P₀=f，q₀=-f，磁场与原辅助初值为0。
下方提供真实时间延拓以核验原方程在t=0所确定的导数以及两层L²图数据。
只证明 OriginalAt(...,0,X)，绝不将这个延拓称为全时间PDE解或存在性证明。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open LeanPML.Analysis LeanPML.Rectangle LeanPML.PML LeanPML.PML.Concrete
open LeanPML.Rectangle.ParameterCertificate
namespace LeanPML.Examples.CompatibleData

/-- 实际时间延拓：E=P=f保持常值，磁场一阶项取(-t f_y,t f_x)。
这只实现初始导数资料；一般t≠0时电方程未必成立。 -/
def initialExtension (f : SmoothField) : OriginalFields where
  E:=fun _ X=>f X
  P:=fun _ X=>f X
  Hx:=fun t X=> -t*dy f X
  Hy:=fun t X=> t*dx f X
  Z1:=fun _ _=>0
  Z2:=fun _ _=>0
  Qx:=fun _ _=>0
  Qy:=fun _ _=>0

/-- §11.1指定的八变量初值：只有E与P允许非零，四个原辅助初值为零。
这是具体数据的值核对，不能当作全时间方程或解存在性。 -/
theorem initial_values (f : SmoothField) (X : Point) :
    (initialExtension f).E 0 X=f X ∧ (initialExtension f).P 0 X=f X ∧
    (initialExtension f).Hx 0 X=0 ∧ (initialExtension f).Hy 0 X=0 ∧
    (initialExtension f).Z1 0 X=0 ∧ (initialExtension f).Z2 0 X=0 ∧
    (initialExtension f).Qx 0 X=0 ∧ (initialExtension f).Qy 0 X=0 := by
  simp [initialExtension]

/-- 电磁空间导数确有可导性，避免只依赖fderiv的总定义。
此处全时间C∞只描述技术延拓；原方程仍只在t=0核验。 -/
theorem spatial_regular (f : SmoothField) (t : ℝ) :
    ContDiff ℝ ∞ ((initialExtension f).E t) ∧
    ContDiff ℝ ∞ ((initialExtension f).Hx t) ∧
    ContDiff ℝ ∞ ((initialExtension f).Hy t) := by
  exact ⟨f.contDiff,contDiff_const.mul f.derivativeY.contDiff,
    contDiff_const.mul f.derivativeX.contDiff⟩

/-- 初始值和实际导数分开：u/q来自历史积分，λ=t∇f，所以φ=0。 -/
theorem lift_values (f : SmoothField) (t : ℝ) (X : Point) :
    (lift (initialExtension f) 1 (fun _=>0) (fun X=>-f X)).u t X=t*f X ∧
    (lift (initialExtension f) 1 (fun _=>0) (fun X=>-f X)).q t X=(t-1)*f X ∧
    (lift (initialExtension f) 1 (fun _=>0) (fun X=>-f X)).φx t X=0 ∧
    (lift (initialExtension f) 1 (fun _=>0) (fun X=>-f X)).φy t X=0 := by
  have hhistory : integralLift (initialExtension f).E (fun _=>0) t = fun Y=>t*f Y := by
    funext Y
    simp [integralLift,initialExtension]
  have hdx : spaceDx (integralLift (initialExtension f).E (fun _=>0)) t X=t*dx f X := by
    rw [spaceDx,hhistory,fderiv_const_mul f.differentiable.differentiableAt]
    rfl
  have hdy : spaceDy (integralLift (initialExtension f).E (fun _=>0)) t X=t*dy f X := by
    rw [spaceDy,hhistory,fderiv_const_mul f.differentiable.differentiableAt]
    rfl
  refine ⟨congrFun hhistory X,?_,?_,?_⟩
  · simp [lift,integralLift,initialExtension]; ring
  · change 1*(t*dx f X)-spaceDx (integralLift (initialExtension f).E (fun _=>0)) t X=0
    rw [hdx,one_mul,sub_self]
  · change -1*(-t*dy f X)-spaceDy (integralLift (initialExtension f).E (fun _=>0)) t X=0
    rw [hdy]; ring

/-- 真正HasDerivAt：E_t=P_t=0，H_x,t=-f_y，H_y,t=f_x。
由常函数及t的乘常数求导，普通符号Et/Pt没有被当作证据。 -/
theorem initial_derivatives (f : SmoothField) (X : Point) :
    HasDerivAt (fun t=>(initialExtension f).E t X) 0 0 ∧
    HasDerivAt (fun t=>(initialExtension f).P t X) 0 0 ∧
    HasDerivAt (fun t=>(initialExtension f).Hx t X) (-dy f X) 0 ∧
    HasDerivAt (fun t=>(initialExtension f).Hy t X) (dx f X) 0 := by
  refine ⟨hasDerivAt_const _ _,hasDerivAt_const _ _,?_,?_⟩
  · simpa [initialExtension] using ((hasDerivAt_id (0:ℝ)).neg.mul_const (dy f X))
  · simpa [initialExtension] using ((hasDerivAt_id (0:ℝ)).mul_const (dx f X))

/-- (2.1)仅在初始时刻核验全部八条方程；f的支撑位于零吸收区使pf=rf=0。
电与Debye方程确定E_t=P_t=0，并非额外假设一般PML满足教学子系统。 -/
theorem original_at_initial (p r : ℝ→ℝ) (f : SmoothField)
    (hpf : ∀ X,p X.1*f X=0) (hrf : ∀ X,r X.2*f X=0) (X : Point) :
    OriginalAt 1 1 1 1 p r (initialExtension f) 0 X := by
  have hd := initial_derivatives f X
  have hEt := hd.1.deriv
  have hPt := hd.2.1.deriv
  have hHx := hd.2.2.1.deriv
  have hHy := hd.2.2.2.deriv
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · constructor
    · exact hd.1.congr_deriv hEt.symm
    · exact hd.2.2.1.congr_deriv hHx.symm
    · exact hd.2.2.2.congr_deriv hHy.symm
    · exact hd.2.1.congr_deriv hPt.symm
    all_goals simpa [initialExtension,dt] using hasDerivAt_const (0:ℝ) (0:ℝ)
  all_goals simp [dt,initialExtension,spaceDx,spaceDy]
  all_goals try first | rfl | solve | nlinarith only [hpf X,hrf X]
  all_goals rcases mul_eq_zero.mp (hpf X) with hp|hf
  all_goals simp_all

/-- (2.4)的五个初始不变量为零；特别q₀=-f抵消P₀=f，而非要求所有原量为零。 -/
theorem compatible_initial (p r : ℝ→ℝ) (f : SmoothField)
    (hpf : ∀ X,p X.1*f X=0) (X : Point) :
    InitialCompatible (initialExtension f)
      (lift (initialExtension f) 1 (fun _=>0) (fun X=>-f X)) 1 1 1 p r X := by
  have hφ := lift_values f 0 X
  constructor
  · simp [invariantD,lift,integralLift,initialExtension]
  · simp [invariantZ1,lift,integralLift,initialExtension]
  · change 0+(p X.1*r X.2)*(integralLift (initialExtension f).P (fun X=>-f X) 0 X)=0
    rw [integralLift_initial]
    calc
      _ = -r X.2*(p X.1*f X) := by ring
      _ = 0 := by rw [hpf X,mul_zero]
  · change 0-p X.1*(lift (initialExtension f) 1 (fun _=>0) (fun X=>-f X)).φy 0 X=0
    rw [hφ.2.2.2]; ring
  · change 0+r X.2*(lift (initialExtension f) 1 (fun _=>0) (fun X=>-f X)).φx 0 X=0
    rw [hφ.2.2.1]; ring

/-- 历史和导数层的真实光滑数据：v=tf,z=(t-1)f,λ=t∇f,φ=0。 -/
def data (f : SmoothField) : SmoothStateData where
  v:=affineJet 0 1 f
  V:=constantJet f
  R:=constantJet f
  z:=affineJet (-1) 1 f
  Λx:=affineJet 0 1 f.derivativeX
  Λy:=affineJet 0 1 f.derivativeY
  φx:=constantJet 0
  φy:=constantJet 0

/-- 所有时间槽与真实历史提升逐函数识别，保证两层图数据来自同一历史。
这一证明不使用全时间PDE，所以不会把初值证书误包装为解的存在。 -/
theorem identified (f : SmoothField) :
    LiftIdentified (data f) (initialExtension f) 1 (fun _=>0) (fun X=>-f X) := by
  constructor
  · funext t X
    simpa [data,affineJet] using (lift_values f t X).1.symm
  · rfl
  · rfl
  · funext t X
    simpa [data,affineJet,sub_eq_add_neg,add_comm] using (lift_values f t X).2.1.symm
  · funext t X; simp [data,affineJet,lift,initialExtension]
  · funext t X; simp [data,affineJet,lift,initialExtension]
  · funext t X
    exact (lift_values f t X).2.2.1.symm
  · funext t X
    exact (lift_values f t X).2.2.2.symm

/-- 普通与加权两层均有实际成员和真实时间正则性。
φ=0，所以无界权重下仍有√wφ=0；没有对普通场删除零吸收区域。 -/
def regular (D : Rect) (C : SpatialAbsorption Point) (f : SmoothField) :
    SmoothStateRegular D C (data f) where
  v:=affineJet_regular D 0 1 f
  V:=constantJet_regular D f
  R:=constantJet_regular D f
  z:=affineJet_regular D (-1) 1 f
  Λx:=affineJet_regular D 0 1 f.derivativeX
  Λy:=affineJet_regular D 0 1 f.derivativeY
  φx:=constantJet_regular D 0
  φy:=constantJet_regular D 0
  weightedX:=constantJet_weightedRegular D C.wx 0 (weighted_zero_memLp D C.wx)
  weightedY:=constantJet_weightedRegular D C.wy 0 (weighted_zero_memLp D C.wy)

/-- 两层图平方确为有限实数：其底层每一项已由真实L²/加权L²成员构造。
这里给出可调用表达式，并不宣称这个时间延拓在内部满足PDE。 -/
def initialGraphSquare (D : Rect) (C : SpatialAbsorption Point) (K : ℝ) (f : SmoothField) : ℝ :=
  twoLayerGraphSquare 1 1 1 K
    (smoothStateBase D C (data f) (regular D C f) 0)
    (smoothStateFirst D C (data f) (regular D C f) 0)

/-- 初始图平方的精确有限表达式。
第一层V=R=f，第二层λ=∇f；ψ及其时间导数均为零。 -/
theorem initialGraphSquare_formula (D : Rect) (C : SpatialAbsorption Point)
    (K : ℝ) (f : SmoothField) :
    initialGraphSquare D C K f = 2*‖SmoothField.toL2 D f‖^2 +
      K*(‖SmoothField.toL2 D f.derivativeX‖^2+‖SmoothField.toL2 D f.derivativeY‖^2) := by
  simp [initialGraphSquare,twoLayerGraphSquare,LeanPML.PML.graphSquare,
    smoothStateBase,smoothStateFirst,data,affineJet,constantJet]
  ring

/-- 非零性发生于矩形内部，连续代表唯一性保证实际L²类也非零。 -/
theorem physicalBump_L2_ne_zero : SmoothField.toL2 unitSquare FullDomain.physicalBump≠0 := by
  intro hzero
  have heq := SmoothField.eqOn_open_of_toL2_eq unitSquare FullDomain.physicalBump 0
    (hzero.trans (map_zero _).symm)
  have hcenter := heq (show ((0:ℝ),0)∈unitSquare.openSet by
    norm_num [Rect.openSet,rectangleDomain,unitSquare])
  exact FullDomain.physicalBump_center_pos.ne' hcenter

/-- 支撑性质推出pf=rf=0，计算域仍是整个矩形；函数外部仅因f=0而乘积消失。 -/
theorem absorption_times_bump (X : Point) :
    FullDomain.profile X.1*FullDomain.physicalBump X=0 ∧
    FullDomain.profile X.2*FullDomain.physicalBump X=0 := by
  by_cases hzero : FullDomain.physicalBump X=0
  · simp [hzero]
  have hsupport : X∈tsupport (⇑FullDomain.physicalBump) := subset_closure hzero
  have hcoeff := FullDomain.physicalBump_support_zero hsupport
  simp [hcoeff.1,hcoeff.2]

/-- 具体非零物理区初值满足全部八条初始方程；不声称这一延拓为OriginalOn。 -/
theorem physical_initial_equations (X : Point) :
    OriginalAt 1 1 1 1 FullDomain.profile FullDomain.profile
      (initialExtension FullDomain.physicalBump) 0 X :=
  original_at_initial _ _ _ (fun X=>(absorption_times_bump X).1)
    (fun X=>(absorption_times_bump X).2) X

/-- 具体物理区数据的五个初始兼容关系。 -/
theorem physical_initial_compatible (X : Point) :
    InitialCompatible (initialExtension FullDomain.physicalBump)
      (lift (initialExtension FullDomain.physicalBump) 1 (fun _=>0)
        (fun X=>-FullDomain.physicalBump X)) 1 1 1 FullDomain.profile FullDomain.profile X :=
  compatible_initial _ _ _ (fun X=>(absorption_times_bump X).1) X

/-- 物理区紧支函数在四条外边界为零，满足全矩形PEC初值。 -/
theorem physical_bump_boundary : ZeroBoundary unitSquare FullDomain.physicalBump := by
  have hzero (X : Point) (hout : X∉Icc (-(1:ℝ)/4) (1/4) ×ˢ Icc (-(1:ℝ)/4) (1/4)) :
      FullDomain.physicalBump X=0 := by
    by_contra hne
    exact hout (FullDomain.physicalBump_tsupport_subset (subset_closure hne))
  constructor
  · intro y hy; apply hzero; norm_num [unitSquare]
  constructor
  · intro y hy; apply hzero; norm_num [unitSquare]
  constructor
  · intro x hx; apply hzero; norm_num [unitSquare]
  · intro x hx; apply hzero; norm_num [unitSquare]

/-- 提升辅助初值φ为零，故包括零吸收区在内都满足正确的零区兼容。 -/
theorem physical_zero_initial (X : Point) :
    (lift (initialExtension FullDomain.physicalBump) 1 (fun _=>0)
      (fun X=>-FullDomain.physicalBump X)).φx 0 X=0 ∧
    (lift (initialExtension FullDomain.physicalBump) 1 (fun _=>0)
      (fun X=>-FullDomain.physicalBump X)).φy 0 X=0 :=
  (lift_values FullDomain.physicalBump 0 X).2.2

/-- 原文§11.1初值的两层图平方严格为正且每项来自实际L²成员。
K使用本矩形保守Poincaré常数的证书，不引用未证明的解存在性。 -/
theorem physical_initial_graph_pos :
    0 < initialGraphSquare unitSquare FullDomain.regional.coefficients
      (scaleK 1 1 1 (poincareConstant unitSquare)) FullDomain.physicalBump := by
  rw [initialGraphSquare_formula]
  have hnorm : 0<‖SmoothField.toL2 unitSquare FullDomain.physicalBump‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr physicalBump_L2_ne_zero)
  have hK : 0≤scaleK 1 1 1 (poincareConstant unitSquare) := by
    unfold scaleK materialA
    positivity
  have hgradient : 0≤scaleK 1 1 1 (poincareConstant unitSquare)*
      (‖SmoothField.toL2 unitSquare FullDomain.physicalBump.derivativeX‖^2+
       ‖SmoothField.toL2 unitSquare FullDomain.physicalBump.derivativeY‖^2) :=
    mul_nonneg hK (add_nonneg (sq_nonneg _) (sq_nonneg _))
  linarith only [hnorm,hgradient]

/-- 初始导数层兼容是直接核验，尤其T=0时不能从空的内部方程推出。
这里q_t=f、P_t=0、u_t=f，φ_t=0，来自上面的真实jet。 -/
theorem initial_derivative_compatible (D : Rect) (C : SpatialAbsorption Point) (f : SmoothField) :
    InitialDerivativeCompatible D C (data f) 1 1 := by
  constructor <;> intros <;> simp [data,affineJet,constantJet]

/-- §11.1两层所需初始外边界迹：u₀=0、E₀=f、E_t(0)=0。
E的零迹来自物理区紧支；另两条来自实际定义和已核验的真实导数。 -/
theorem physical_initial_traces :
    ZeroBoundary unitSquare (fun _=> (0:ℝ)) ∧
    ZeroBoundary unitSquare ((initialExtension FullDomain.physicalBump).E 0) ∧
    ZeroBoundary unitSquare (fun X=>dt (initialExtension FullDomain.physicalBump).E 0 X) := by
  refine ⟨?_,physical_bump_boundary,?_⟩
  · simp [ZeroBoundary]
  · simpa [initialExtension,dt] using (show ZeroBoundary unitSquare (fun _=>(0:ℝ)) by
      simp [ZeroBoundary])

/-- 非平凡兼容数据证书：实际紧支、非零L²、初始八方程、五兼容、两层迹、
零区条件、初始导数层与正有限图平方一起核验。它不含OriginalOn或解存在性。
实际普通/加权成员的可调用证据是上面的regular。 -/
theorem physical_data_certificate :
    HasCompactSupport (⇑FullDomain.physicalBump) ∧
    SmoothField.toL2 unitSquare FullDomain.physicalBump≠0 ∧
    (∀ X, OriginalAt 1 1 1 1 FullDomain.profile FullDomain.profile
      (initialExtension FullDomain.physicalBump) 0 X) ∧
    (∀ X, InitialCompatible (initialExtension FullDomain.physicalBump)
      (lift (initialExtension FullDomain.physicalBump) 1 (fun _=>0)
        (fun X=>-FullDomain.physicalBump X)) 1 1 1 FullDomain.profile FullDomain.profile X) ∧
    ZeroBoundary unitSquare FullDomain.physicalBump ∧
    (∀ X, (lift (initialExtension FullDomain.physicalBump) 1 (fun _=>0)
      (fun X=>-FullDomain.physicalBump X)).φx 0 X=0 ∧
      (lift (initialExtension FullDomain.physicalBump) 1 (fun _=>0)
      (fun X=>-FullDomain.physicalBump X)).φy 0 X=0) ∧
    InitialDerivativeCompatible unitSquare FullDomain.regional.coefficients
      (data FullDomain.physicalBump) 1 1 ∧
    0 < initialGraphSquare unitSquare FullDomain.regional.coefficients
      (scaleK 1 1 1 (poincareConstant unitSquare)) FullDomain.physicalBump :=
  ⟨FullDomain.physicalBump_hasCompactSupport,physicalBump_L2_ne_zero,
    physical_initial_equations,physical_initial_compatible,physical_bump_boundary,
    physical_zero_initial,initial_derivative_compatible _ _ _,physical_initial_graph_pos⟩

end LeanPML.Examples.CompatibleData
