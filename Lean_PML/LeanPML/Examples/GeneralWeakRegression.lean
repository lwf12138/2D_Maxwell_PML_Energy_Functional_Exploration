import LeanPML.PML.MainGeneralWeak
import LeanPML.Examples.OriginalPowerProfile
import LeanPML.Examples.SharpWeak
import LeanPML.Examples.WeakBranchRegression

/-!
# 一般弱代表入口的实际调用

原文 (10.2) 全剖面调用主定理的系数入口；非零静态八变量解沿同一入口搬运。
前者验证系数可容许及条件主定理调用，不声称从初值证明一般存在性。
后者复用已证非零原解，保证新入口不是只能用于零函数。
-/
noncomputable section
open MeasureTheory Set Filter
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
open LeanPML.PML LeanPML.PML.Weak
namespace LeanPML.Examples.GeneralWeak

/-- 已有具体系数证书去掉连续性字段；新入口必须自行重建代表。
这是回归数据构造，不是主定理对一般输入的额外连续性要求。 -/
def forgetContinuous {D : Rect} (A : WeakRegionalAbsorption D) : RawWeakRegionalAbsorption D where
  coefficients := A.coefficients
  c := A.c
  S := A.S
  c_pos := A.c_pos
  S_nonneg := A.S_nonneg
  S_le_quarter := A.S_le_quarter
  profileX_bounds := A.profileX_bounds
  profileY_bounds := A.profileY_bounds

/-- 与旧非零静态解相同的区域常值单向吸收，保留 r=0。 -/
def staticAbsorption : RawWeakRegionalAbsorption unitSquare :=
  forgetContinuous (WeakRegionalAbsorption.constant unitSquare smallC amplitudeS amplitudeS 0
    smallC_pos amplitudeS_pos.le amplitudeS_eq_quarter.le ⟨amplitudeS_pos.le,le_rfl⟩
    ⟨le_rfl,amplitudeS_pos.le⟩)

/-- 原系数与区域零延拓在实际矩形测度下一致，域外常值/零值无物理意义。 -/
theorem static_coefficients_ae :
    WeakStaticMode.coefficients.p =ᵐ[unitSquare.measure] staticAbsorption.rawSpatial.p ∧
    WeakStaticMode.coefficients.r =ᵐ[unitSquare.measure] staticAbsorption.rawSpatial.r := by
  constructor
  · filter_upwards [ae_restrict_mem unitSquare.openSet_open.measurableSet] with z hz
    change z ∈ unitSquare.openSet at hz
    change amplitudeS = unitSquare.openSet.indicator _ z
    rw [indicator_of_mem hz]
    rfl
  · filter_upwards [ae_restrict_mem unitSquare.openSet_open.measurableSet] with z hz
    change z ∈ unitSquare.openSet at hz
    change 0 = unitSquare.openSet.indicator _ z
    rw [indicator_of_mem hz]
    rfl

/-- 原八条方程逐条搬运，输入原场不变。 -/
def staticSolution (T : ℝ) (hT : 0 ≤ T) : OriginalInterval unitSquare staticAbsorption.rawSpatial 1 1 1 1 T :=
  (WeakStaticMode.solution T hT).changeCoefficients static_coefficients_ae.1 static_coefficients_ae.2

/-- 真实静态导数槽全部继承已有证据，没有重新假设导数层 PDE。 -/
def staticJet (T : ℝ) (hT : 0 ≤ T) : OriginalJet (staticSolution T hT) :=
  { WeakStaticMode.jet T hT with }

/-- 正长度 Cᵏ 入口的正则性来自同一个常值图路径。 -/
def staticCore (T : ℝ) (hT : 0 ≤ T) : V7ClosedCkCore (staticSolution T hT) :=
  { WeakStaticMode.canonicalCore T hT with }

/-- 静态初始导数兼容包括 T=0；系数搬运已经证明原八式保持。 -/
theorem static_degenerate (T : ℝ) (hT : 0 ≤ T) :
    DegenerateJetCompatibility (staticSolution T hT) (staticJet T hT) := by
  obtain ⟨hp,hr,_,_⟩ := spatial_operators_eq_ae WeakStaticMode.coefficients staticAbsorption.rawSpatial
    static_coefficients_ae.1 static_coefficients_ae.2
  have h := WeakStaticMode.degenerate T hT
  refine ⟨h.polar,?_,?_⟩
  · intro ht
    simpa only [staticJet,staticSolution,OriginalInterval.changeCoefficients,OriginalInterval.u,← hp,← hr] using h.spatialX ht
  · intro ht
    simpa only [staticJet,staticSolution,OriginalInterval.changeCoefficients,OriginalInterval.u,← hp,← hr] using h.spatialY ht

/-- 非零加权 y 初值沿 a.e. 权重识别搬运。 -/
theorem static_weight_ae : WeakStaticMode.coefficients.swap.wx =ᵐ[unitSquare.measure]
    staticAbsorption.rawSpatial.swap.wx := by
  filter_upwards [static_coefficients_ae.1,static_coefficients_ae.2] with z hp hr
  change energyWeightX smallC (WeakStaticMode.coefficients.r z) (WeakStaticMode.coefficients.p z) =
    energyWeightX smallC (staticAbsorption.rawSpatial.r z) (staticAbsorption.rawSpatial.p z)
  rw [hp,hr]

def staticInitialY : WeightedL2 unitSquare.measure staticAbsorption.rawSpatial.swap.wx :=
  weightedChangeRepresentative unitSquare.measure _ _ static_weight_ae WeakStaticMode.initialY

/-- 物理初值仍是原非零常数场 1；不是将辅助量全设为零。 -/
theorem static_initial_physical :
    physicalL2 unitSquare.measure staticAbsorption.rawSpatial.swap.wx
      staticAbsorption.rawSpatial.swap.wx_measurable staticAbsorption.rawSpatial.swap.wx_gap staticInitialY =
      WeakStaticMode.oneField := by
  unfold staticInitialY
  rw [physical_changeRepresentative]
  exact WeakStaticMode.physical_initialY

/-- 同一精确矩形阈值，不改变旧实例的实际 c。 -/
theorem static_threshold : staticAbsorption.c ≤ threshold 1 1 1 1 (sharpPoincareConstant unitSquare) :=
  WeakStaticMode.sharpParameters.c_le_threshold

/-- 非零实际原解调用新的“一般弱代表构造→主定理”链，覆盖 T=0。 -/
theorem static_main_call (T : ℝ) (hT : 0 ≤ T) :
    OriginalInterval.SharpEnergyConclusions (staticSolution T hT).representedInterval
      ((staticSolution T hT).representedJet (staticJet T hT))
      (staticAbsorption.initialX 0) (staticAbsorption.initialY staticInitialY) := by
  apply (staticSolution T hT).main_energy_GeneralWeakJet (staticJet T hT) (static_degenerate T hT)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) static_threshold
  · rw [map_zero]
    change (0 : ScalarL2 unitSquare.measure) = (WeakStaticMode.solution T hT).φx 0
    exact (WeakStaticMode.auxiliary_x T hT 0).symm
  · rw [static_initial_physical]
    change WeakStaticMode.oneField = (WeakStaticMode.solution T (by linarith)).φy 0
    exact (WeakStaticMode.auxiliary_y T (by linarith) 0).symm

/-- 同一非零原解也调用正长度 Cᵏ 入口；无需额外端点 PDE。 -/
theorem static_ck_call (T : ℝ) (hT : 0 < T) :
    let O := V7ClosedCkCore.canonicalInterval (O := (staticSolution T hT.le).representedInterval) hT
    let J := ((((staticSolution T hT.le).representedCk (staticCore T hT.le)).regularity hT).toTimeRegularity hT).toOriginalJet
    OriginalInterval.SharpEnergyConclusions O J (staticAbsorption.initialX 0) (staticAbsorption.initialY staticInitialY) ∧
      ∀ t ∈ Icc 0 T, OriginalInterval.SharpOriginalAuxiliaryBounds O
        (O.sharpEnergy J (staticAbsorption.initialX 0) (staticAbsorption.initialY staticInitialY) 0) t := by
  apply (staticSolution T hT.le).main_energy_GeneralWeakCk (staticCore T hT.le) hT
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) static_threshold
  · rw [map_zero]
    change (0 : ScalarL2 unitSquare.measure) = (WeakStaticMode.solution T hT.le).φx 0
    exact (WeakStaticMode.auxiliary_x T hT.le 0).symm
  · rw [static_initial_physical]
    change WeakStaticMode.oneField = (WeakStaticMode.solution T (by linarith)).φy 0
    exact (WeakStaticMode.auxiliary_y T (by linarith) 0).symm

/-- 新入口能量严格正来自原非零 Hx 的实际 L² 控制，不另定义常数能量。 -/
theorem static_energy_positive (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    0 < (staticSolution T hT).representedInterval.sharpEnergy
      ((staticSolution T hT).representedJet (staticJet T hT))
      (staticAbsorption.initialX 0) (staticAbsorption.initialY staticInitialY) t := by
  have hcontrol := (static_main_call T hT).physical t ht
  have hnorm : 0 < ‖WeakStaticMode.oneField‖ := norm_pos_iff.mpr WeakStaticMode.oneField_ne_zero
  change (1:ℝ)*‖WeakStaticMode.state.E‖^2 + 1*(‖WeakStaticMode.state.Hx‖^2+‖WeakStaticMode.state.Hy‖^2) +
    (1:ℝ)⁻¹*‖WeakStaticMode.state.P‖^2 ≤ (4/1)*_ at hcontrol
  simp only [WeakStaticMode.state,norm_zero,norm_neg,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,inv_one,one_mul,zero_add,add_zero,div_one] at hcontrol
  nlinarith [sq_pos_of_pos hnorm]


/-- 构造出的新代表保留 r=0 的实际 L² 乘子；不读取任意指定点。 -/
theorem represented_r_zero (f : ScalarL2 unitSquare.measure) :
    staticAbsorption.represented.spatial.rCoeff.operator unitSquare.measure f = 0 := by
  have hp := static_coefficients_ae.1.trans staticAbsorption.rawSpatial_ae.1
  have hr := static_coefficients_ae.2.trans staticAbsorption.rawSpatial_ae.2
  have hops := spatial_operators_eq_ae WeakStaticMode.coefficients staticAbsorption.represented.spatial hp hr
  rw [← hops.2.1]
  exact WeakStaticMode.r_operator f

/-- 静态 y 辅助演化为零，但其加权初值非零，因而保留静态能量。 -/
theorem represented_rate_y_zero :
    staticAbsorption.represented.spatial.swap.auxiliaryRateX unitSquare.measure 0 WeakStaticMode.oneField = 0 := by
  let C := staticAbsorption.represented.spatial
  apply physicalL2_injective unitSquare.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap
  rw [C.swap.physical_auxiliaryRateX,map_zero,map_zero,zero_sub]
  apply neg_eq_zero.mpr
  exact represented_r_zero _

/-- 原历史在换代表后仍为零；保留的是非零磁/辅助场而非非零 u。 -/
theorem represented_u_zero (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (staticSolution T hT).representedInterval.u t = 0 :=
  WeakStaticMode.history_u T hT t

theorem represented_q_zero (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (staticSolution T hT).representedInterval.q t = 0 :=
  WeakStaticMode.history_q T hT t

/-- 真实加权 Bochner 历史在静态右端下恒定，实际调用非零加权初值。 -/
theorem represented_weighted_constant (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (staticSolution T hT).representedInterval.weightedX (staticAbsorption.initialX 0) t = 0 ∧
    (staticSolution T hT).representedInterval.weightedY (staticAbsorption.initialY staticInitialY) t =
      weightedCongr unitSquare.measure staticAbsorption.represented.spatial.swap_wx_eq_wy
        (staticAbsorption.initialY staticInitialY) := by
  let C := staticAbsorption.represented.spatial
  have hxrate : C.auxiliaryRateX unitSquare.measure 0 0 = 0 := by
    apply physicalL2_injective unitSquare.measure C.wx C.wx_measurable C.wx_gap
    rw [C.physical_auxiliaryRateX,map_zero,map_zero,map_zero,sub_self]
  constructor
  · unfold OriginalInterval.weightedX SpatialAbsorption.auxiliaryWeightedHistory
    simp only [represented_u_zero]
    change staticAbsorption.initialX 0 + ∫ s in 0..t, C.auxiliaryRateX unitSquare.measure 0 0 = 0
    rw [hxrate]
    simp only [intervalIntegral.integral_zero,add_zero]
    rfl
  · unfold OriginalInterval.weightedY SpatialAbsorption.auxiliaryWeightedHistory
    simp only [represented_u_zero]
    change weightedCongr _ _ (staticAbsorption.initialY staticInitialY +
      ∫ s in 0..t, C.swap.auxiliaryRateX unitSquare.measure 0 WeakStaticMode.oneField) = _
    rw [represented_rate_y_zero]
    simp only [intervalIntegral.integral_zero,add_zero]

/-- 新入口的两层实际状态恒定；第一层仍来自原解真实导数。 -/
theorem represented_states_constant (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (staticSolution T hT).representedInterval.baseState (staticAbsorption.initialX 0)
      (staticAbsorption.initialY staticInitialY) t =
    (staticSolution T hT).representedInterval.baseState (staticAbsorption.initialX 0)
      (staticAbsorption.initialY staticInitialY) 0 ∧
    (staticSolution T hT).representedInterval.firstState ((staticSolution T hT).representedJet (staticJet T hT)) t =
    (staticSolution T hT).representedInterval.firstState ((staticSolution T hT).representedJet (staticJet T hT)) 0 := by
  constructor
  · unfold OriginalInterval.baseState
    simp only [represented_u_zero,represented_q_zero,(represented_weighted_constant T hT t).1,
      (represented_weighted_constant T hT t).2,(represented_weighted_constant T hT 0).1,
      (represented_weighted_constant T hT 0).2]
    rfl
  · unfold OriginalInterval.firstState
    simp only [represented_u_zero]
    rfl

/-- 新主定理使用的实际 E₇ 为正的常值；并非另设一个自由常数能量。 -/
theorem static_energy_constant (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (staticSolution T hT).representedInterval.sharpEnergy ((staticSolution T hT).representedJet (staticJet T hT))
      (staticAbsorption.initialX 0) (staticAbsorption.initialY staticInitialY) t =
    (staticSolution T hT).representedInterval.sharpEnergy ((staticSolution T hT).representedJet (staticJet T hT))
      (staticAbsorption.initialX 0) (staticAbsorption.initialY staticInitialY) 0 := by
  unfold OriginalInterval.sharpEnergy energy7
  change twoLayerEnergy _ _ _ _ _ _ _
    ((staticSolution T hT).representedInterval.baseState _ _ t)
    ((staticSolution T hT).representedInterval.firstState _ t) = _
  rw [(represented_states_constant T hT t).1,(represented_states_constant T hT t).2]
  rfl

/-- 非零静态解的 D₇=0 由新主定理能量律与真实常值求导的唯一性推出。 -/
theorem static_dissipation_zero (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    (staticSolution T hT).representedInterval.sharpDissipation ((staticSolution T hT).representedJet (staticJet T hT))
      (staticAbsorption.initialX 0) (staticAbsorption.initialY staticInitialY) t = 0 := by
  have hlaw := ((static_main_call T hT).law t ht).1
  have hconst := hasDerivAt_const t
    ((staticSolution T hT).representedInterval.sharpEnergy ((staticSolution T hT).representedJet (staticJet T hT))
      (staticAbsorption.initialX 0) (staticAbsorption.initialY staticInitialY) 0)
  have heq := funext (static_energy_constant T hT)
  rw [heq] at hlaw
  exact neg_eq_zero.mp (hlaw.unique hconst)

/-- 任意合法一般弱吸收都能调用实际零解；该回归单独覆盖退化吸收，
不代替上面的非零解调用。 -/
theorem zero_main (A : RawWeakRegionalAbsorption unitSquare)
    (hs : A.c ≤ threshold 1 1 1 1 (sharpPoincareConstant unitSquare)) (T : ℝ) (hT : 0 ≤ T) :
    let O := WeakBranchRegression.zeroInterval unitSquare A.rawSpatial 1 1 1 1 T hT
    let J := WeakBranchRegression.zeroJet unitSquare A.rawSpatial 1 1 1 1 T hT
    OriginalInterval.SharpEnergyConclusions O.representedInterval (O.representedJet J)
      (A.initialX 0) (A.initialY 0) := by
  dsimp only
  have hinitial := WeakBranchRegression.zero_initial_weighted unitSquare A.rawSpatial 1 1 1 1 T hT
  exact OriginalInterval.main_energy_GeneralWeakJet _ _
    (WeakBranchRegression.zero_degenerate unitSquare A.rawSpatial 1 1 1 1 T hT)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs 0 0 hinitial.1 hinitial.2

/-- 原文整族剖面以原 π 常数、c=1/128、S=1/512 实际接入新原系统主定理。
证明系数与入口可用，不声称任意非零初值产生解。 -/
theorem original_profile_main (m : ℕ) (ηx ηy : ℝ) (hηx : 0 < ηx) (hηy : 0 < ηy)
    (hxS : ηx ≤ (1:ℝ)/512) (hyS : ηy ≤ (1:ℝ)/512) (T : ℝ) (hT : 0 ≤ T) :
    let A := OriginalPower.absorption m ηx ηy hηx hηy hxS hyS
    let O := WeakBranchRegression.zeroInterval unitSquare A.rawSpatial 1 1 1 1 T hT
    let J := WeakBranchRegression.zeroJet unitSquare A.rawSpatial 1 1 1 1 T hT
    OriginalInterval.SharpEnergyConclusions O.representedInterval (O.representedJet J)
      (A.initialX 0) (A.initialY 0) :=
  zero_main _ (OriginalPower.absorption_threshold m ηx ηy hηx hηy hxS hyS) T hT

/-- 全零、x 单向、y 单向、双向四个布尔配置均调用新代表主入口。
两个非对称方向都被量化，不只检查 p=r。 -/
theorem four_branch_main (xActive yActive : Bool) (T : ℝ) (hT : 0 ≤ T) :
    let A := forgetContinuous (WeakRegionalAbsorption.certificateConfiguration xActive yActive)
    let O := WeakBranchRegression.zeroInterval unitSquare A.rawSpatial 1 1 1 1 T hT
    let J := WeakBranchRegression.zeroJet unitSquare A.rawSpatial 1 1 1 1 T hT
    OriginalInterval.SharpEnergyConclusions O.representedInterval (O.representedJet J)
      (A.initialX 0) (A.initialY 0) := by
  apply zero_main
  exact WeakStaticMode.sharpParameters.c_le_threshold

end LeanPML.Examples.GeneralWeak
