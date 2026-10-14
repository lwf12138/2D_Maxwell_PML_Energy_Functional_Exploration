import LeanPML.Examples.PathHelpers
import LeanPML.PML.MainSmoothRectangle
import LeanPML.Examples.FullDomainProfile

/-!
# v0.5.3：单向边层内的非零静态模态

V7 的静态模态回归：r=0，F仅依赖x，u=E=P=q=0，λ=φ=(0,F)。
磁场Hx=-F与辅助Qx=pF恰好抵消。以下从真实函数、导数、历史提升构造
主定理的输入；不是把能量恒定或耗散为零作为原解假设。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open LeanPML.Analysis LeanPML.Rectangle LeanPML.PML LeanPML.PML.Concrete
open LeanPML.PML.SmoothRectangle
namespace LeanPML.Examples.StaticMode

/-- 静态模态的八个原场；材料参数取1。F是实际光滑空间场。 -/
def original (p : ℝ→ℝ) (f : SmoothField) : OriginalFields where
  E := fun _ _ => 0
  Hx := fun _ X => -f X
  Hy := fun _ _ => 0
  P := fun _ _ => 0
  Z1 := fun _ _ => 0
  Z2 := fun _ _ => 0
  Qx := fun _ X => p X.1*f X
  Qy := fun _ _ => 0

/-- 零场历史的全函数等式，供实际空间导数改写使用。 -/
theorem history_zero : integralLift (fun _ _=>0) (fun _=>0) = (fun _ _=>0) := by
  funext t X
  simp [integralLift]

/-- 实际历史积分为零，λ与φ的y分量为F；没有任意选择历史函数。 -/
theorem lift_values (p : ℝ→ℝ) (f : SmoothField) :
    lift (original p f) 1 (fun _=>0) (fun _=>0) =
      ⟨(fun _ _=>0),(fun _ _=>0),(fun _ _=>0),(fun _ _=>0),
        (fun _ _=>0),(fun _ X=>f X),(fun _ _=>0),(fun _ X=>f X)⟩ := by
  simp only [lift,original]
  congr 1 <;> funext t X <;> simp [spaceDx,spaceDy,history_zero]

/-- 由(2.1)直接验证八条方程。唯一空间条件dyF=0使电方程的curlH为零。
所有HasDerivAt来自恒定时间函数；空间导数仍是实际fderiv。 -/
theorem equations_at (p : ℝ→ℝ) (f : SmoothField)
    (hdy : ∀ X, dy f X=0) (t : ℝ) (X : Point) :
    OriginalAt 1 1 1 1 p (fun _=>0) (original p f) t X := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simpa [original,dt] using hasDerivAt_const t _
  all_goals simp [original,dt,spaceDx,spaceDy,show fderiv ℝ (f : Point→ℝ) X (0,1)=0 from hdy X]
  all_goals ring

/-- 初始兼容的五个值均为零；F非零不会破坏兼容。 -/
theorem compatible_initial (p : ℝ→ℝ) (f : SmoothField) (X : Point) :
    InitialCompatible (original p f) (lift (original p f) 1 (fun _=>0) (fun _=>0))
      1 1 1 p (fun _=>0) X := by
  rw [lift_values]
  constructor <;> simp [invariantD,invariantZ1,invariantZ2,invariantX,invariantY,original]

/-- 八槽均为真实光滑函数；加权分量φy随后用√wy F的实际成员证据构造。 -/
def coordinates (f : SmoothField) : SmoothStateCoordinates where
  v:=0; V:=0; R:=0; z:=0; Λx:=0; Λy:=f; ψx:=0; ψy:=f

def data (f : SmoothField) : SmoothStateData := constantStateData (coordinates f)

/-- 坐标逐一等于历史提升，满足主定理要求的同源识别。 -/
theorem identified (p : ℝ→ℝ) (f : SmoothField) :
    LiftIdentified (data f) (original p f) 1 (fun _=>0) (fun _=>0) := by
  constructor <;> rw [lift_values] <;> rfl

/-- 实际时间常值给出普通与历史联合C∞正则性。 -/
theorem history_regular (p : ℝ→ℝ) (f : SmoothField) :
    OriginalLiftRegular (original p f) (fun _=>0) := by
  constructor
  all_goals try { intro X; exact continuous_const }
  change ContDiff ℝ ∞ (Function.uncurry (integralLift (fun _ _=>0) (fun _=>0)))
  rw [history_zero]
  exact contDiff_const

/-- 所有普通槽的C(K)/L²正则性以及实际加权路径正则性。
这里hweighted是可积性辅助接口，具体边层函数将在下方证明满足它。 -/
def regular (D : Rect) (C : SpatialAbsorption Point) (f : SmoothField)
    (hweighted : MemLp (fun X=>Real.sqrt (C.wy X)*f X) 2 D.measure) :
    SmoothStateRegular D C (data f) :=
  constantStateRegular D C (coordinates f) (weighted_zero_memLp D C.wx) hweighted

/-- 主定理的正式调用入口。原始假设只要求材料阈值、r=0、F的方向与支撑，
以及实际加权成员；真实方程、历史、五兼容和退化端点条件均由证明体填入。 -/
def solution {D : Rect} (R : RegionalAbsorption D) (f : SmoothField)
    (hr : R.r=fun _=>0) (hdy : ∀ X,dy f X=0)
    (hzero : ∀ X∈D.openSet,R.p X.1=0 → f X=0)
    (hweighted : MemLp (fun X=>Real.sqrt (R.coefficients.wy X)*f X) 2 D.measure)
    (hthreshold : R.c≤threshold 1 1 1 1 (poincareConstant D))
    (T : ℝ) (hT : 0≤T) : SmoothCompatibleSolution R 1 1 1 1 T where
  ε_pos := by norm_num
  κ_pos := by norm_num
  τ_pos := by norm_num
  μ_pos := by norm_num
  c_le_threshold := hthreshold
  F := original R.p f
  u0 := fun _=>0
  q0 := fun _=>0
  B := data f
  regular := regular D R.coefficients f hweighted
  identified := identified R.p f
  T_nonneg := hT
  history_regular := history_regular R.p f
  equations := by
    rw [hr]
    intro t ht X hX
    exact equations_at R.p f hdy t X
  initial := by
    rw [hr]
    intro X hX
    exact compatible_initial R.p f X
  zero_initial := by
    intro X hX ha
    rw [hr] at ha
    simp only [add_zero] at ha
    rw [lift_values]
    exact ⟨rfl,hzero X hX ha⟩
  PEC := by intro t ht; simp [ZeroBoundary,original]
  u0_boundary := by simp [ZeroBoundary]
  degenerate := by
    intro hTzero
    constructor <;> intros <;> simp [data,constantStateData,constantJet]

/-- (6.9)在非零静态模式上的正式调用：主定理确实被实例化，而非只验证数值恒等式。 -/
theorem energy_antitone {D : Rect} (R : RegionalAbsorption D) (f : SmoothField)
    (hr : R.r=fun _=>0) (hdy : ∀ X,dy f X=0)
    (hzero : ∀ X∈D.openSet,R.p X.1=0 → f X=0)
    (hweighted : MemLp (fun X=>Real.sqrt (R.coefficients.wy X)*f X) 2 D.measure)
    (hthreshold : R.c≤threshold 1 1 1 1 (poincareConstant D)) (T : ℝ) (hT : 0≤T) :
    AntitoneOn (solution R f hr hdy hzero hweighted hthreshold T hT).energy (Icc 0 T) :=
  (solution R f hr hdy hzero hweighted hthreshold T hT).energy_antitone

open LeanPML.Rectangle.ParameterCertificate

/-- 真实单向系数：保留物理区p=0，r在全域为0；不是全域正吸收的简化模型。 -/
def regional : RegionalAbsorption unitSquare where
  c:=smallC
  S:=amplitudeS
  c_pos:=smallC_pos
  p:=FullDomain.profile
  r:=fun _=>0
  p_smooth:=FullDomain.profile_contDiff
  r_smooth:=contDiff_const
  p_bounds:=fun x _=>FullDomain.profile_bounds x
  r_bounds:=fun _ _=>⟨le_rfl,amplitudeS_pos.le⟩
  S_le_quarter:=amplitudeS_eq_quarter.le

/-- y方向恒定、x方向位于正吸收平台的实际非零光滑场。 -/
def sideField : SmoothField :=
  ⟨fun X=>FullDomain.sideBump1D X.1,FullDomain.sideBump1D_contDiff.comp contDiff_fst⟩

/-- 偏导来自常值y切片的真实导数唯一性，不能仅以命名断言dyF=0。 -/
theorem sideField_dy (X : Point) : dy sideField X=0 := by
  exact (sideField.hasDerivAt_sliceY X).unique (hasDerivAt_const X.2 (FullDomain.sideBump1D X.1))

/-- p=0时F=0，故本例在零吸收区满足真实辅助兼容。 -/
theorem sideField_zero (X : Point) (hp : FullDomain.profile X.1=0) : sideField X=0 := by
  by_contra hne
  have hplateau := FullDomain.sideBump1D_support_plateau (subset_closure hne)
  exact amplitudeS_pos.ne' (hplateau.symm.trans hp)

/-- 平台支撑使√wy F等于固定常数倍F。该等式只在整个矩形测度a.e.使用，
没有宣称wy全域有界，也没有忽略p=0区域。 -/
theorem sideField_weighted_identity :
    (fun X=>Real.sqrt (regional.coefficients.wy X)*sideField X) =ᵐ[unitSquare.measure]
      (fun X=>Real.sqrt ((smallC-amplitudeS)/amplitudeS)*sideField X) := by
  filter_upwards [regional.weights_ae.2] with X hweights
  by_cases hzero : sideField X=0
  · simp [hzero]
  have hplateau : FullDomain.profile X.1=amplitudeS :=
    FullDomain.sideBump1D_support_plateau (subset_closure hzero)
  rw [hweights]
  change Real.sqrt (energyWeightY smallC (FullDomain.profile X.1) 0)*sideField X=_
  rw [hplateau]
  simp [energyWeightY,absorptionSum,amplitudeS_pos]

/-- 真正加权L²成员：用上一a.e.等式与普通L²常数倍，不是假设权重有界。 -/
theorem sideField_weighted :
    MemLp (fun X=>Real.sqrt (regional.coefficients.wy X)*sideField X) 2 unitSquare.measure := by
  have hmem := (sideField.memLp unitSquare).const_smul
    (Real.sqrt ((smallC-amplitudeS)/amplitudeS))
  exact MemLp.ae_eq sideField_weighted_identity.symm hmem

/-- 内部点(7/8,0)处非零，故普通L²等价类并非零元。 -/
theorem sideField_L2_ne_zero : SmoothField.toL2 unitSquare sideField≠0 := by
  intro hzero
  have heq := SmoothField.eqOn_open_of_toL2_eq unitSquare sideField 0
    (hzero.trans (map_zero _).symm)
  have hpoint := heq (show ((7/8:ℝ),0)∈unitSquare.openSet by
    norm_num [Rect.openSet,rectangleDomain,unitSquare])
  exact FullDomain.sideBump1D_center_pos.ne' hpoint

/-- 非零静态模式的完整具体原解输入。各正则性与兼容条件已经逐项证明，
参数阈值使用同一矩形CP=4证书；允许任意T≥0。 -/
def concreteSolution (T : ℝ) (hT : 0≤T) :
    SmoothCompatibleSolution regional 1 1 1 1 T :=
  solution regional sideField rfl sideField_dy (fun X _=>sideField_zero X)
    sideField_weighted unitSquare_le_threshold T hT

/-- 非零静态原场确实调用正式积分平衡定理，而非只检查点态代数。 -/
theorem concrete_integral_balance (T : ℝ) (hT : 0≤T) {t₁ t₂ : ℝ}
    (ht₁ : 0≤t₁) (ht₁₂ : t₁≤t₂) (ht₂ : t₂≤T) :
    (concreteSolution T hT).energy t₂ +
      ∫ t in t₁..t₂,(concreteSolution T hT).dissipation t =
      (concreteSolution T hT).energy t₁ :=
  (concreteSolution T hT).energy_integral_balance ht₁ ht₁₂ ht₂

/-- 时间常值由实际状态的定义给出；这个等式不作为原解输入。 -/
theorem concrete_energy_constant (T : ℝ) (hT : 0≤T) (t s : ℝ) :
    (concreteSolution T hT).energy t=(concreteSolution T hT).energy s := by
  rfl

/-- 能量图平方只剩非零磁通量及加权辅助场。普通场F不会因零区处理被删除。 -/
theorem concrete_graph_formula (T : ℝ) (hT : 0≤T) (t : ℝ) :
    (concreteSolution T hT).graphSquare t=
      ‖SmoothField.toL2 unitSquare sideField‖^2 +
      ‖weightedOfFunction unitSquare.measure regional.coefficients.wy sideField sideField_weighted‖^2 := by
  change twoLayerGraphSquare 1 1 1 (scaleK 1 1 1 (poincareConstant unitSquare))
    (smoothStateBase unitSquare regional.coefficients (data sideField)
      (regular unitSquare regional.coefficients sideField sideField_weighted) t)
    (smoothStateFirst unitSquare regional.coefficients (data sideField)
      (regular unitSquare regional.coefficients sideField sideField_weighted) t)=_
  simp [twoLayerGraphSquare,LeanPML.PML.graphSquare,smoothStateBase,smoothStateFirst,
    data,constantStateData,constantJet,coordinates]

/-- 在t=0应用正式主定理的图下界，得到严格正能量；全时间恒定性来自实际路径。 -/
theorem concrete_energy_pos (T : ℝ) (hT : 0≤T) (t : ℝ) :
    0<(concreteSolution T hT).energy t := by
  have hnorm : 0<‖SmoothField.toL2 unitSquare sideField‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr sideField_L2_ne_zero)
  have hgraph := (concreteSolution T hT).energy_graph_bounds (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT⟩)
  rw [concrete_graph_formula] at hgraph
  have hweighted_nonneg := sq_nonneg
    ‖weightedOfFunction unitSquare.measure regional.coefficients.wy sideField sideField_weighted‖
  rw [concrete_energy_constant T hT t 0]
  linarith only [hgraph.1,hnorm,hweighted_nonneg]

/-- 零耗散由正式能量律与真实常值路径的导数唯一性推出。
先在辅助时间区间[0,1]内部调用主定理，再利用同一常值状态的定义识别任意T，
所以T=0没有从空的内部方程偷推出导数。 -/
theorem concrete_dissipation_zero (T : ℝ) (hT : 0≤T) (t : ℝ) :
    (concreteSolution T hT).dissipation t=0 := by
  let s := concreteSolution 1 (by norm_num)
  have hlaw : HasDerivAt s.energy (-s.dissipation (1/2)) (1/2) :=
    (s.energy_law_and_closure (by norm_num : (1/2:ℝ)∈Ioo 0 1)).1
  have hconstant : HasDerivAt s.energy 0 (1/2) := by
    have heq : s.energy=(fun _=>s.energy 0) := funext (fun t=>concrete_energy_constant 1 (by norm_num) t 0)
    rw [heq]
    exact hasDerivAt_const _ _
  have hd : s.dissipation (1/2)=0 := neg_eq_zero.mp (hlaw.unique hconstant)
  exact hd

/-- 回归结论：实际非零原解有正的常值能量和零耗散。
它说明主定理是单调不增，不能无条件加强为严格递减。 -/
theorem nonzero_static_regression (T : ℝ) (hT : 0≤T) (t : ℝ) :
    0<(concreteSolution T hT).energy t ∧
    (concreteSolution T hT).energy t=(concreteSolution T hT).energy 0 ∧
    (concreteSolution T hT).dissipation t=0 :=
  ⟨concrete_energy_pos T hT t,concrete_energy_constant T hT t 0,
    concrete_dissipation_zero T hT t⟩

end LeanPML.Examples.StaticMode
