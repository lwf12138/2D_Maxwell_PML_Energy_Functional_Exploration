import LeanPML.PML.MainWeakRectangle
import LeanPML.PML.WeakLiftCompatibility

/-!
# V7 §11.3：实际弱原八式的非零静态回归

整个 (-1,1)²，p=S=1/65536，r=0，c=1/16384，材料参数为 1。
取 λ=(0,1)，Hx=-1，Qx=S，其余原场为零。没有要求磁场外边界为零。
以下构造真实 H(div)、实际普通/加权 L² 及常值时间路径，逐条核验八式。
这是 §11.3 同一机制的明确静态 PDE 解：本例 F=1 未取紧支，因为 p 在全域为正，
加权可积性可直接证明，且 PEC 不限制磁场边界。它与仅给初始数据的可容许性例不同。
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ContDiff InnerProductSpace
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
open LeanPML.PML LeanPML.PML.Weak
namespace LeanPML.Examples.WeakStaticMode

/-- 与已证保守 Poincaré 参数证书相同的常系数单向吸收。 -/
def coefficients : SpatialAbsorption (ℝ × ℝ) where
  c := smallC
  S := amplitudeS
  c_pos := smallC_pos
  p := fun _ => amplitudeS
  r := fun _ => 0
  p_measurable := measurable_const
  r_measurable := measurable_const
  p_nonneg := fun _ => amplitudeS_pos.le
  r_nonneg := by intros;norm_num
  p_le_S := fun _ => le_rfl
  r_le_S := fun _ => amplitudeS_pos.le
  S_le_quarter := amplitudeS_eq_quarter.le

/-- 实际全矩形常数场 1 的 L² 商类。 -/
def oneField : ScalarL2 unitSquare.measure := SmoothField.toL2 unitSquare weakCoefficientOne

/-- 常数 1 的两真实偏导都为零。 -/
theorem one_derivatives : weakCoefficientOne.derivativeX = 0 ∧ weakCoefficientOne.derivativeY = 0 := by
  constructor <;> apply Subtype.ext <;> funext x
  all_goals simp [SmoothField.derivativeX_apply,SmoothField.derivativeY_apply,dx,dy,weakCoefficientOne]

/-- λ=(0,1) 的弱散度为零，使用真实光滑→弱 H(div) 桥接。 -/
def flux : weakHDivGraph unitSquare := smoothToWeakHDiv unitSquare 0 weakCoefficientOne

@[simp] theorem flux_x : flux.val 0 = 0 := by simp [flux,smoothToWeakHDiv]
@[simp] theorem flux_y : flux.val 1 = oneField := rfl
@[simp] theorem flux_div : flux.val 2 = 0 := by
  have hz : (0 : SmoothField).derivativeX = 0 := by
    apply Subtype.ext;funext x
    simp [SmoothField.derivativeX_apply,dx]
  simp [flux,smoothToWeakHDiv,one_derivatives.2,hz]

/-- 系数乘法确为 p=S；不是给坐标变量随意取数。 -/
@[simp] theorem p_operator (f : ScalarL2 unitSquare.measure) :
    coefficients.pCoeff.operator unitSquare.measure f = amplitudeS • f := by
  apply Lp.ext
  filter_upwards [coefficients.pCoeff.coe_operator unitSquare.measure f,Lp.coeFn_smul amplitudeS f]
    with x hp hs
  rw [hp,hs]
  rfl

@[simp] theorem r_operator (f : ScalarL2 unitSquare.measure) :
    coefficients.rCoeff.operator unitSquare.measure f = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [coefficients.rCoeff.coe_operator unitSquare.measure f] with x hr
  simpa [coefficients,SpatialAbsorption.rCoeff] using hr

/-- 非零原八变量静态状态，Hx=-1 是允许的磁静态分量。 -/
def state : OriginalState unitSquare where
  E := 0
  Hx := -oneField
  Hy := 0
  P := 0
  Z1 := 0
  Z2 := 0
  Qx := amplitudeS • oneField
  Qy := 0

/-- 常值时间路径的实际导数数据。 -/
def zeroState : OriginalState unitSquare := ⟨0,0,0,0,0,0,0,0⟩

/-- 八式均逐条核验；所有时间导数由 HasDerivAt 常值规则提供。
原场空间导数来自 H₀¹ 零电场与上述真实弱散度，不由名称暗示。 -/
theorem originalAt (t : ℝ) :
    OriginalAt unitSquare coefficients 1 1 1 1 (fun _ => state) zeroState t 0 flux := by
  refine {
    E := hasDerivAt_const t _
    Hx := hasDerivAt_const t _
    Hy := hasDerivAt_const t _
    P := hasDerivAt_const t _
    Z1 := hasDerivAt_const t _
    Z2 := hasDerivAt_const t _
    Qx := hasDerivAt_const t _
    Qy := hasDerivAt_const t _
    electric_value := by simp [state]
    flux_x := by simp [state]
    flux_y := by simp [state]
    electric := ?_
    magneticX := ?_
    magneticY := ?_
    debye := ?_
    memory1 := ?_
    memory2 := ?_
    auxiliaryX := ?_
    auxiliaryY := ?_ }
  all_goals simp [state,zeroState,neg_smul,smul_neg]


/-- 原八式与五个初始兼容构成实际有限时间原解；T=0 单独合法。 -/
def solution (T : ℝ) (hT : 0 ≤ T) : OriginalInterval unitSquare coefficients 1 1 1 1 T where
  nonneg_time := hT
  fields := fun _ => state
  derivatives := fun _ => zeroState
  electric := fun _ => 0
  flux := fun _ => flux
  u₀ := 0
  q₀ := 0
  continuous_fields := ⟨continuousOn_const,continuousOn_const,continuousOn_const,
    continuousOn_const,continuousOn_const,continuousOn_const,continuousOn_const,continuousOn_const⟩
  continuous_electric := continuousOn_const
  continuous_flux := continuousOn_const
  electric_value := by intros;rfl
  flux_x := by intros;simp [state]
  flux_y := by intros;simp [state]
  equations := fun t _ => originalAt t
  initial_compatible := by
    intro i
    fin_cases i <;> simp [invariants,historyU,historyQ,LeanPML.Time.banachHistory,
      phiX,phiY,state,neg_smul,smul_neg]

@[simp] theorem history_u (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (solution T hT).u t = 0 := by
  simp [OriginalInterval.u,historyU,LeanPML.Time.banachHistory,solution]

@[simp] theorem history_q (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (solution T hT).q t = 0 := by
  simp [OriginalInterval.q,historyQ,LeanPML.Time.banachHistory,solution,state]

@[simp] theorem auxiliary_x (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (solution T hT).φx t = 0 := by
  simp [OriginalInterval.φx,phiX,solution,state,OriginalInterval.u,historyU,LeanPML.Time.banachHistory]

@[simp] theorem auxiliary_y (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (solution T hT).φy t = oneField := by
  simp [OriginalInterval.φy,phiY,solution,state,OriginalInterval.u,historyU,LeanPML.Time.banachHistory]

/-- 同一原解的真实一、二阶时间导数，全部为零；没有输入导数层 PDE。 -/
def jet (T : ℝ) (hT : 0 ≤ T) : OriginalJet (solution T hT) where
  electricDot := fun _ => 0
  fluxDot := fun _ => 0
  electricDDot := fun _ => 0
  polarDDot := fun _ => 0
  fluxDDotX := fun _ => 0
  fluxDDotY := fun _ => 0
  electric_deriv := by
    intro t ht
    change HasDerivAt (fun _ : ℝ => (0 : zeroBoundaryGraph unitSquare)) 0 t
    exact hasDerivAt_const t (0 : zeroBoundaryGraph unitSquare)
  flux_deriv := fun t _ => hasDerivAt_const t _
  electricDot_value := by intros;rfl
  electric_second := fun t _ => hasDerivAt_const t _
  polar_second := fun t _ => hasDerivAt_const t _
  flux_second_x := fun t _ => hasDerivAt_const t _
  flux_second_y := fun t _ => hasDerivAt_const t _
  continuous_electricDot := continuousOn_const
  continuous_fluxDot := continuousOn_const
  continuous_polarDot := continuousOn_const
  continuous_polarDDot := continuousOn_const

/-- 本实例 y 权重为常数 3；仅此实例有限，未给一般无界权重添加上界。 -/
@[simp] theorem weight_y (x : ℝ × ℝ) : coefficients.swap.wx x = 3 := by
  norm_num [SpatialAbsorption.swap,SpatialAbsorption.wx,coefficients,energyWeightX,
    absorptionSum,smallC,amplitudeS]

/-- 非零初始辅助场 1 在实际加权空间中，由有限矩形上的常数平方可积获得。 -/
def initialY : WeightedL2 unitSquare.measure coefficients.swap.wx :=
  weightedOfFunction unitSquare.measure coefficients.swap.wx (fun _ => 1)
    (by simpa only [weight_y,mul_one] using
      unitSquare.memLp_of_continuous (f := fun _ : ℝ × ℝ => Real.sqrt 3) continuous_const 2)

/-- 非零加权初值恢复为实际物理常数场；不是仅假设某个加权坐标存在。 -/
theorem physical_initialY : physicalL2 unitSquare.measure coefficients.swap.wx
    coefficients.swap.wx_measurable coefficients.swap.wx_gap initialY = oneField := by
  apply Lp.ext
  have hrecover := physicalL2_weightedOfFunction unitSquare.measure coefficients.swap.wx
    (fun _ => (1 : ℝ)) coefficients.swap.wx_measurable coefficients.swap.wx_gap
    (by simpa only [weight_y,mul_one] using
      unitSquare.memLp_of_continuous (f := fun _ : ℝ × ℝ => Real.sqrt 3) continuous_const 2)
    (by filter_upwards [] with x; simp only [weight_y]; norm_num)
  filter_upwards [hrecover,SmoothField.coe_toL2 unitSquare weakCoefficientOne] with x hr ho
  dsimp only [initialY,oneField]
  rw [hr,ho]
  rfl

/-- 原始非零磁场的严格 L² 非零性，从连续代表在矩形内部点取值 1 推出。 -/
theorem oneField_ne_zero : oneField ≠ 0 := by
  intro hzero
  have heq : SmoothField.toL2 unitSquare weakCoefficientOne = SmoothField.toL2 unitSquare 0 := by
    simpa [oneField] using hzero
  have hpoint := SmoothField.eqOn_open_of_toL2_eq unitSquare weakCoefficientOne 0 heq
    (show (0,0) ∈ unitSquare.openSet by norm_num [Rect.openSet,rectangleDomain,unitSquare])
  norm_num [weakCoefficientOne] at hpoint

/-- T=0 所需导数层兼容来自本静态数据的直接核验，而非空内部方程。 -/
def degenerate (T : ℝ) (hT : 0 ≤ T) :
    DegenerateJetCompatibility (solution T hT) (jet T hT) where
  polar := by intros;simp [solution,state,zeroState]
  spatialX := by intros;simp [jet,solution,OriginalInterval.u,historyU,LeanPML.Time.banachHistory]
  spatialY := by intros;simp [jet,solution,OriginalInterval.u,historyU,LeanPML.Time.banachHistory]

/-- 所有材料及阈值使用真实矩形的已有精确参数证书。 -/
def parameters : CoercivityParameters coefficients 1 1 1 1 (poincareConstant unitSquare) :=
  ⟨by norm_num,by norm_num,by norm_num,by norm_num,
    poincareConstant_pos unitSquare,unitSquare_le_threshold⟩

/-- 非零静态原八式实际调用新的弱主定理，包含能量律、单调性与积分平衡。 -/
theorem main_call (T : ℝ) (hT : 0 ≤ T) :
    OriginalInterval.EnergyConclusions (solution T hT) (jet T hT) 0 initialY := by
  apply (solution T hT).main_energy_estimate_WeakOriginal (jet T hT) 0 initialY parameters
  · simp only [map_zero,auxiliary_x]
  · rw [physical_initialY,auxiliary_y]
  · exact degenerate T hT

/-- 新主定理控制输入原磁场，非零 Hx 迫使静态能量严格为正。 -/
theorem energy_pos (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    0 < (solution T hT).energy (jet T hT) 0 initialY t := by
  have hcontrol := (main_call T hT).physical t ht
  have hnorm : 0 < ‖oneField‖ := norm_pos_iff.mpr oneField_ne_zero
  simp only [solution,state,norm_zero,norm_neg,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,inv_one,one_mul,zero_add,add_zero,div_one] at hcontrol
  change ‖oneField‖ ^ 2 ≤ 4 * (solution T hT).energy (jet T hT) 0 initialY t at hcontrol
  nlinarith [sq_pos_of_pos hnorm]

/-- 静态辅助右端在实际加权空间为零；靠已证物理恢复单射，而非把加权范数设零。 -/
@[simp] theorem rate_x_zero : coefficients.auxiliaryRateX unitSquare.measure 0 0 = 0 := by
  simp [SpatialAbsorption.auxiliaryRateX]

@[simp] theorem rate_y_zero : coefficients.swap.auxiliaryRateX unitSquare.measure 0 oneField = 0 := by
  apply physicalL2_injective unitSquare.measure coefficients.swap.wx
    coefficients.swap.wx_measurable coefficients.swap.wx_gap
  rw [coefficients.swap.physical_auxiliaryRateX,map_zero,map_zero,zero_sub]
  apply neg_eq_zero.mpr
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [coefficients.swap.pCoeff.coe_operator unitSquare.measure oneField] with x hx
  simpa [coefficients,SpatialAbsorption.swap,SpatialAbsorption.pCoeff] using hx

@[simp] theorem weighted_x_zero (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (solution T hT).weightedX 0 t = 0 := by
  unfold OriginalInterval.weightedX SpatialAbsorption.auxiliaryWeightedHistory
  simp only [history_u]
  simp [solution,rate_x_zero]

/-- 加权历史右端为零，故非零初值完整保留，未删除单向吸收辅助分量。 -/
@[simp] theorem weighted_y_constant (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (solution T hT).weightedY initialY t =
      weightedCongr unitSquare.measure coefficients.swap_wx_eq_wy initialY := by
  unfold OriginalInterval.weightedY SpatialAbsorption.auxiliaryWeightedHistory
  simp only [history_u]
  simp [solution,rate_y_zero]

/-- 实际原层状态与导数层状态都不随时间变化，接通自动历史构造。 -/
theorem states_constant (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (solution T hT).baseState 0 initialY t = (solution T hT).baseState 0 initialY 0 ∧
    (solution T hT).firstState (jet T hT) t = (solution T hT).firstState (jet T hT) 0 := by
  constructor
  · unfold OriginalInterval.baseState
    simp only [history_u,history_q,weighted_x_zero,weighted_y_constant]
    rfl
  · unfold OriginalInterval.firstState
    simp only [history_u]
    rfl

/-- 实际新弱主定理的能量入口恒定；不是另设一个自由常数能量。 -/
theorem energy_constant (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (solution T hT).energy (jet T hT) 0 initialY t =
      (solution T hT).energy (jet T hT) 0 initialY 0 := by
  unfold OriginalInterval.energy energy7
  change twoLayerEnergy _ _ _ _ _ _ _ ((solution T hT).baseState 0 initialY t)
    ((solution T hT).firstState (jet T hT) t) = _
  rw [(states_constant T hT t).1,(states_constant T hT t).2]
  rfl

/-- 在内部时刻，真实主能量律与常值导数唯一性共同给出耗散为零。
因此正的静态能量不会严格递减；这不否定单调不增。 -/
theorem dissipation_zero (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    (solution T hT).dissipation (jet T hT) 0 initialY t = 0 := by
  have hlaw := ((main_call T hT).law t ht).1
  have hconstant : HasDerivAt ((solution T hT).energy (jet T hT) 0 initialY) 0 t := by
    have hfunction : (solution T hT).energy (jet T hT) 0 initialY =
        fun _ => (solution T hT).energy (jet T hT) 0 initialY 0 :=
      funext (energy_constant T hT)
    rw [hfunction]
    exact hasDerivAt_const t _
  exact neg_eq_zero.mp (hlaw.unique hconstant)

/-- 非零静态解回归的联合结论，准确使用内部耗散与全闭区间能量入口。 -/
theorem nonzero_static_regression (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    0 < (solution T hT).energy (jet T hT) 0 initialY t ∧
    (solution T hT).energy (jet T hT) 0 initialY t =
      (solution T hT).energy (jet T hT) 0 initialY 0 ∧
    (solution T hT).dissipation (jet T hT) 0 initialY t = 0 :=
  ⟨energy_pos T hT (Ioo_subset_Icc_self ht),energy_constant T hT t,dissipation_zero T hT ht⟩

end LeanPML.Examples.WeakStaticMode
