import LeanPML.Rectangle.RegionalCoefficients

/-!
# v0.5.1：光滑兼容解类的全域先验能量定理

来源：V7 (2.1)–(2.6)、(5.2)–(5.3)、(6.4)、(6.6)–(6.10)。
输入仍是原八变量、整个矩形 PEC、初始兼容与明确的技术正则性。
证明体调用区域系数入口，生成真实历史的同源 L²/加权路径，再使用已经证明的
具体 Green、保守 Poincaré 与抽象能量估计；这些结论均不作为最终输入。

本文件使用 C_P=2Lx。联合 C∞ 延拓、C(K) 路径、实际加权成员与可微性
是强于 V7 弱空间表述的技术条件。原 PDE 只在 (0,T)×Ω 成立。
建议先读 SmoothCompatibleSolution → energy_law_and_closure →
main_energy_estimate_smoothRectangle；最后核对 physical_current_bound 的原场识别。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open LeanPML.Analysis LeanPML.Rectangle LeanPML.PML.Concrete
namespace LeanPML.PML.SmoothRectangle

/-- 所选光滑兼容原解的输入包。
材料字段只含正性与 (5.3) 的阈值；B/regular/identified 识别实际历史及其强正则性。
equations 是八条原方程，initial/zero_initial 只在 t=0；不含全时段保持或能量目标。
T=0 的初始导数层兼容单列，不能由空的内部演化推出。 -/
structure SmoothCompatibleSolution {D : Rect} (R : RegionalAbsorption D)
    (ε κ τ μ T : ℝ) where
  ε_pos : 0<ε
  κ_pos : 0<κ
  τ_pos : 0<τ
  μ_pos : 0<μ
  c_le_threshold : R.c≤threshold ε κ τ μ (poincareConstant D)
  F : OriginalFields
  u0 : Point→ℝ
  q0 : Point→ℝ
  B : SmoothStateData
  regular : SmoothStateRegular D R.coefficients B
  identified : LiftIdentified B F μ u0 q0
  T_nonneg : 0≤T
  history_regular : OriginalLiftRegular F u0
  equations : OriginalOn D.openSet T ε κ τ μ R.p R.r F
  initial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u0 q0) ε κ τ R.p R.r X
  zero_initial : ∀ X∈D.openSet, R.p X.1+R.r X.2=0 →
    (lift F μ u0 q0).φx 0 X=0 ∧ (lift F μ u0 q0).φy 0 X=0
  PEC : OriginalRectPEC D T F
  u0_boundary : ZeroBoundary D u0
  degenerate : T=0 → InitialDerivativeCompatible D R.coefficients B κ τ

namespace SmoothCompatibleSolution
variable {D : Rect} {R : RegionalAbsorption D} {ε κ τ μ T : ℝ}
variable (s : SmoothCompatibleSolution R ε κ τ μ T)

/-- 原参数条件接入旧强制性参数包，C_P 正性由实际矩形证明。
(8.2)、图范数界及耗散闭合都不是这里的字段。 -/
def parameters : CoercivityParameters R.coefficients ε κ τ μ (poincareConstant D) :=
  ⟨s.ε_pos,s.κ_pos,s.τ_pos,s.μ_pos,poincareConstant_pos D,s.c_le_threshold⟩

/-- 由原模型构造具体有限区间问题；返回对象是证明体的产物，不是原解输入。
调用推荐的区域入口，保留整个 Ω 和原 p/r 的域内幅度范围。 -/
def problem : FiniteIntervalProblemConditional (greenDomain D) R.coefficients
    ε κ τ μ (poincareConstant D) T (poincare_estimate D) :=
  R.originalRegionalFiniteIntervalProblem ε κ τ μ T s.F s.u0 s.q0 s.B s.regular
    s.identified s.T_nonneg (ne_of_gt s.μ_pos) s.history_regular s.equations
    s.initial s.zero_initial s.PEC s.u0_boundary s.degenerate

/-- V7 (6.4)：能量命名入口，直接沿用旧 energy7。
U₀=(u,E,P,q,λ,φ)，U₁ 使用同一真实场的第一导数；没有独立选择第二层。 -/
def energy (t : ℝ) : ℝ :=
  energy7 D.measure R.coefficients ε κ τ μ (poincareConstant D) s.problem.path t
/-- (7.8) 的真实 D₇。R_t 在两层分别对应实际 P_t、P_tt。 -/
def dissipation (t : ℝ) : ℝ :=
  dissipation7 D.measure R.coefficients ε κ τ μ (poincareConstant D) s.problem.path t
/-- (6.5) 两层图平方表达式；不宣称对任意八变量安装裸 L² 范数等价。 -/
def graphSquare (t : ℝ) : ℝ :=
  graphSquare7 D.measure R.coefficients ε κ μ (poincareConstant D) s.problem.path t

/-- 积分平衡额外用到的真实 P_tt 连续性，来自 regular，而非另设目标假设。 -/
theorem second_R_continuous :
    ContinuousOn (fun t => (s.problem.path.second t).R) (Icc 0 T) :=
  R.originalRegionalFiniteIntervalProblem_second_R_continuous ε κ τ μ T s.F s.u0 s.q0
    s.B s.regular s.identified s.T_nonneg (ne_of_gt s.μ_pos) s.history_regular
    s.equations s.initial s.zero_initial s.PEC s.u0_boundary s.degenerate

/-- (6.2)/(6.4) 的实际积分表示接回原 p/r。
前两条密度可积性使这里不是不可积积分总定义造成的形式等式。 -/
theorem energy_eq_original_integrals (t : ℝ) :
    s.energy t =
      (∫ X, R.energyDensity ε κ τ μ (s.problem.path.base t) X ∂D.measure) +
      scaleK ε κ μ (poincareConstant D) *
      (∫ X, R.energyDensity ε κ τ μ (s.problem.path.first t) X ∂D.measure) := by
  unfold energy energy7 twoLayerEnergy
  rw [R.fieldEnergy_eq_regional_integral,R.fieldEnergy_eq_regional_integral]

/-- 两层原系数能量密度的可积性；权重可无界，由实际加权成员条件承担。 -/
theorem energy_densities_integrable (t : ℝ) :
    Integrable (R.energyDensity ε κ τ μ (s.problem.path.base t)) D.measure ∧
    Integrable (R.energyDensity ε κ τ μ (s.problem.path.first t)) D.measure :=
  ⟨R.energyDensity_integrable ε κ τ μ _,R.energyDensity_integrable ε κ τ μ _⟩

/-- (7.7)/(7.8) 的实际耗散积分也使用原 p/r；零区 c|∇v|² 由旧分支保留。 -/
theorem dissipation_eq_original_integrals (t : ℝ) :
    s.dissipation t =
      (∫ X, R.dissipationDensity ε κ τ μ (s.problem.path.base t)
        (s.problem.path.first t).R X ∂D.measure) +
      scaleK ε κ μ (poincareConstant D) *
      (∫ X, R.dissipationDensity ε κ τ μ (s.problem.path.first t)
        (s.problem.path.second t).R X ∂D.measure) := by
  unfold dissipation dissipation7 twoLayerDissipation
  rw [R.fieldDissipation_eq_regional_integral,R.fieldDissipation_eq_regional_integral]

/-- 原系数耗散密度可积；没有假设单层耗散非负。 -/
theorem dissipation_densities_integrable (t : ℝ) :
    Integrable (R.dissipationDensity ε κ τ μ (s.problem.path.base t)
      (s.problem.path.first t).R) D.measure ∧
    Integrable (R.dissipationDensity ε κ τ μ (s.problem.path.first t)
      (s.problem.path.second t).R) D.measure :=
  ⟨R.dissipationDensity_integrable ε κ τ μ _ _,R.dissipationDensity_integrable ε κ τ μ _ _⟩

/-- V7 (6.7)：从原模型、初值与正则性推出闭区间图平方双边界，包含 T=0。 -/
theorem energy_graph_bounds {t : ℝ} (ht : t∈Icc 0 T) :
    s.graphSquare t/4≤s.energy t ∧ s.energy t≤s.graphSquare t :=
  energy7_bounds_on_Icc_Conditional (greenDomain D) R.coefficients ε κ τ μ
    (poincareConstant D) T s.parameters (poincare_estimate D) s.problem ht

/-- (6.8)：内部真实求导与准确耗散预算并列。
保留空间耗散的1/2和Debye平方的μτ/(4κ)；不是由单调性倒推能量律。 -/
theorem energy_law_and_closure {t : ℝ} (ht : t∈Ioo 0 T) :
    HasDerivAt s.energy (-s.dissipation t) t ∧
    (fieldSpatialDissipation D.measure R.coefficients (s.problem.path.base t) +
      scaleK ε κ μ (poincareConstant D) *
        fieldSpatialDissipation D.measure R.coefficients (s.problem.path.first t))/2 +
      μ*τ/(4*κ) * (‖(s.problem.path.first t).R‖^2 +
        scaleK ε κ μ (poincareConstant D)*‖(s.problem.path.second t).R‖^2)≤
      s.dissipation t ∧ 0≤s.dissipation t :=
  energy7_law_and_closure_Conditional (greenDomain D) R.coefficients ε κ τ μ
    (poincareConstant D) T s.parameters (poincare_estimate D) s.problem ht

/-- (6.9)：闭区间单调不增，仅内部需要原方程及导数；端点比较使用连续性。 -/
theorem energy_antitone : AntitoneOn s.energy (Icc 0 T) :=
  energy7_antitoneOn_Conditional (greenDomain D) R.coefficients ε κ τ μ
    (poincareConstant D) T s.parameters (poincare_estimate D) s.problem

/-- 能量非负来自静态强制性，初值上界来自上一单调性。 -/
theorem energy_initial_bounds {t : ℝ} (ht : t∈Icc 0 T) :
    0≤s.energy t ∧ s.energy t≤s.energy 0 :=
  energy7_initial_bounds_Conditional (greenDomain D) R.coefficients ε κ τ μ
    (poincareConstant D) T s.parameters (poincare_estimate D) s.problem ht

/-- FTC 需要的实际耗散时间可积性：由真实 P_tt 连续与二次型连续性推出。 -/
theorem dissipation_intervalIntegrable {t₁ t₂ : ℝ}
    (ht₁ : 0≤t₁) (ht₁₂ : t₁≤t₂) (ht₂ : t₂≤T) :
    IntervalIntegrable s.dissipation volume t₁ t₂ :=
  intervalIntegrable_dissipation7_Conditional (greenDomain D) R.coefficients ε κ τ μ
    (poincareConstant D) T (poincare_estimate D) s.problem s.second_R_continuous ht₁ ht₁₂ ht₂

/-- (6.9) 的积分平衡独立于单调性，实际调用内部HasDerivAt与FTC。
t₁=t₂、0和T端点、T=0均由同一接口覆盖，不额外要求端点普通导数。 -/
theorem energy_integral_balance {t₁ t₂ : ℝ}
    (ht₁ : 0≤t₁) (ht₁₂ : t₁≤t₂) (ht₂ : t₂≤T) :
    s.energy t₂ + ∫ t in t₁..t₂, s.dissipation t = s.energy t₁ :=
  energy7_integral_balance_Conditional (greenDomain D) R.coefficients ε κ τ μ
    (poincareConstant D) T s.parameters (poincare_estimate D) s.problem
    s.second_R_continuous ht₁ ht₁₂ ht₂

/-- 光滑坐标与原E的全函数识别。它只识别技术代表，不要求域外PDE。 -/
theorem electric_identified (t : ℝ) :
    (s.B.V.value t : Point→ℝ)=s.F.E t := congrFun s.identified.V t
/-- 同一实际极化场的识别。 -/
theorem polar_identified (t : ℝ) :
    (s.B.R.value t : Point→ℝ)=s.F.P t := congrFun s.identified.R t

/-- 磁场由真实λ光滑代表识别；μ>0提供非零证据才能反缩放。 -/
theorem magneticX_identified (t : ℝ) :
    (fun X => (-1/μ)*s.B.Λy.value t X)=s.F.Hx t := by
  have hμ_ne : μ≠0 := ne_of_gt s.μ_pos
  funext X
  have hflux := congrFun (congrFun s.identified.Λy t) X
  change s.B.Λy.value t X = -μ*s.F.Hx t X at hflux
  rw [hflux]
  field_simp

/-- Hy的反缩放方向为+λx/μ，与(2.3)一致。 -/
theorem magneticY_identified (t : ℝ) :
    (fun X => (1/μ)*s.B.Λx.value t X)=s.F.Hy t := by
  have hμ_ne : μ≠0 := ne_of_gt s.μ_pos
  funext X
  have hflux := congrFun (congrFun s.identified.Λx t) X
  change s.B.Λx.value t X = μ*s.F.Hy t X at hflux
  rw [hflux]
  field_simp

/-- 原E本身属于整个矩形L²，证据由实际光滑识别产生。 -/
theorem electric_memLp (t : ℝ) : MemLp (s.F.E t) 2 D.measure := by
  rw [←s.electric_identified t]
  exact (s.B.V.value t).memLp D
/-- 原P的实际L²成员。 -/
theorem polar_memLp (t : ℝ) : MemLp (s.F.P t) 2 D.measure := by
  rw [←s.polar_identified t]
  exact (s.B.R.value t).memLp D
/-- 原Hx的实际L²成员，使用常数缩放的光滑代表。 -/
theorem magneticX_memLp (t : ℝ) : MemLp (s.F.Hx t) 2 D.measure := by
  rw [←s.magneticX_identified t]
  exact ((s.B.Λy.value t).memLp D).const_smul (-1/μ)
/-- 原Hy的实际L²成员。 -/
theorem magneticY_memLp (t : ℝ) : MemLp (s.F.Hy t) 2 D.measure := by
  rw [←s.magneticY_identified t]
  exact ((s.B.Λx.value t).memLp D).const_smul (1/μ)

/-- 原函数的实际L²商类；不是仅将瞬时坐标改名。 -/
def electricL2 (t : ℝ) : ScalarL2 D.measure := (s.electric_memLp t).toLp (s.F.E t)
def polarL2 (t : ℝ) : ScalarL2 D.measure := (s.polar_memLp t).toLp (s.F.P t)
def magneticXL2 (t : ℝ) : ScalarL2 D.measure := (s.magneticX_memLp t).toLp (s.F.Hx t)
def magneticYL2 (t : ℝ) : ScalarL2 D.measure := (s.magneticY_memLp t).toLp (s.F.Hy t)

/-- 通过a.e.代表识别原E与能量状态的速度槽。 -/
theorem electricL2_eq (t : ℝ) : s.electricL2 t=(s.problem.path.base t).V := by
  change s.electricL2 t=SmoothField.toL2 D (s.B.V.value t)
  dsimp only [electricL2]
  apply Lp.ext
  filter_upwards [(s.electric_memLp t).coeFn_toLp,
    SmoothField.coe_toL2 D (s.B.V.value t)] with X hE hV
  rw [hE,hV]
  exact (congrFun (s.electric_identified t) X).symm

/-- 同一方法识别原P与极化槽。 -/
theorem polarL2_eq (t : ℝ) : s.polarL2 t=(s.problem.path.base t).R := by
  change s.polarL2 t=SmoothField.toL2 D (s.B.R.value t)
  dsimp only [polarL2]
  apply Lp.ext
  filter_upwards [(s.polar_memLp t).coeFn_toLp,
    SmoothField.coe_toL2 D (s.B.R.value t)] with X hP hR
  rw [hP,hR]
  exact (congrFun (s.polar_identified t) X).symm

/-- Hx与λ的实际L²缩放识别，保留旋转符号。 -/
theorem magneticXL2_eq (t : ℝ) :
    s.magneticXL2 t=reconstructHx μ (s.problem.path.base t) := by
  change s.magneticXL2 t=(-μ⁻¹) • SmoothField.toL2 D (s.B.Λy.value t)
  dsimp only [magneticXL2]
  apply Lp.ext
  filter_upwards [(s.magneticX_memLp t).coeFn_toLp,
    coe_smul_of D (-μ⁻¹) (SmoothField.coe_toL2 D (s.B.Λy.value t))] with X hH hΛ
  rw [hH,hΛ]
  simpa only [neg_div,one_div] using (congrFun (s.magneticX_identified t) X).symm

/-- Hy与λ的实际L²识别。 -/
theorem magneticYL2_eq (t : ℝ) :
    s.magneticYL2 t=reconstructHy μ (s.problem.path.base t) := by
  change s.magneticYL2 t=μ⁻¹ • SmoothField.toL2 D (s.B.Λx.value t)
  dsimp only [magneticYL2]
  apply Lp.ext
  filter_upwards [(s.magneticY_memLp t).coeFn_toLp,
    coe_smul_of D μ⁻¹ (SmoothField.coe_toL2 D (s.B.Λx.value t))] with X hH hΛ
  rw [hH,hΛ]
  simpa only [one_div] using (congrFun (s.magneticY_identified t) X).symm

/-- V7(6.10)真正回到输入的原E/H/P：先用既有兼容重构控制，再用上方L²等式。
右端是同一时刻的两层能量；一般裸八变量L²双向等价没有由此得到。 -/
theorem physical_current_bound {t : ℝ} (ht : t∈Icc 0 T) :
    ε*‖s.electricL2 t‖^2 + μ*(‖s.magneticXL2 t‖^2+‖s.magneticYL2 t‖^2) +
      κ⁻¹*‖s.polarL2 t‖^2≤(4/μ)*s.energy t := by
  have hcontrol := physicalControl_Conditional D.measure R.coefficients ε κ τ μ
    (poincareConstant D) s.parameters (greenDomain D).spatial
    (ConditionalPoincare.ofGreenTrace (greenDomain D) (poincareConstant D) (poincare_estimate D))
    s.problem.path t (s.problem.static_base t ht) (s.problem.static_first t ht)
  rw [s.electricL2_eq,s.magneticXL2_eq,s.magneticYL2_eq,s.polarL2_eq]
  exact hcontrol.physical

/-- 原物理场进一步受初能量控制，系数4/μ非负由μ>0取得。 -/
theorem physical_initial_bound {t : ℝ} (ht : t∈Icc 0 T) :
    ε*‖s.electricL2 t‖^2 + μ*(‖s.magneticXL2 t‖^2+‖s.magneticYL2 t‖^2) +
      κ⁻¹*‖s.polarL2 t‖^2≤(4/μ)*s.energy 0 := by
  have hμ_pos : 0<μ := s.μ_pos
  calc
    _ ≤ (4/μ)*s.energy t := s.physical_current_bound ht
    _ ≤ (4/μ)*s.energy 0 :=
      mul_le_mul_of_nonneg_left (s.energy_initial_bounds ht).2 (by positivity)

/-- (8.4)–(8.8)的兼容重构控制作为直接推论接入；原模型对应由真实提升识别保证。 -/
theorem auxiliary_initial_bounds {t : ℝ} (ht : t∈Icc 0 T) :
    PhysicalInitialControlBounds D.measure R.coefficients ε κ τ μ
      (poincareConstant D) s.problem.path t :=
  physicalControl_initial_Conditional (greenDomain D) R.coefficients ε κ τ μ
    (poincareConstant D) T s.parameters (poincare_estimate D) s.problem ht

end SmoothCompatibleSolution

/-- 主定理的输出包。这里每个字段都是待证明结论，不能把该包作为原解输入。 -/
structure SmoothEnergyConclusions {D : Rect} {R : RegionalAbsorption D}
    {ε κ τ μ T : ℝ} (s : SmoothCompatibleSolution R ε κ τ μ T) : Prop where
  antitone : AntitoneOn s.energy (Icc 0 T)
  law : ∀ t∈Ioo 0 T,
    HasDerivAt s.energy (-s.dissipation t) t ∧
    (fieldSpatialDissipation D.measure R.coefficients (s.problem.path.base t) +
      scaleK ε κ μ (poincareConstant D)*
        fieldSpatialDissipation D.measure R.coefficients (s.problem.path.first t))/2 +
      μ*τ/(4*κ)*(‖(s.problem.path.first t).R‖^2+
        scaleK ε κ μ (poincareConstant D)*‖(s.problem.path.second t).R‖^2)≤
      s.dissipation t ∧ 0≤s.dissipation t
  graph_bounds : ∀ t∈Icc 0 T, s.graphSquare t/4≤s.energy t ∧ s.energy t≤s.graphSquare t
  initial_bounds : ∀ t∈Icc 0 T, 0≤s.energy t ∧ s.energy t≤s.energy 0
  physical : ∀ t∈Icc 0 T,
    ε*‖s.electricL2 t‖^2+μ*(‖s.magneticXL2 t‖^2+‖s.magneticYL2 t‖^2)+
      κ⁻¹*‖s.polarL2 t‖^2≤(4/μ)*s.energy t
  physical_initial : ∀ t∈Icc 0 T,
    ε*‖s.electricL2 t‖^2+μ*(‖s.magneticXL2 t‖^2+‖s.magneticYL2 t‖^2)+
      κ⁻¹*‖s.polarL2 t‖^2≤(4/μ)*s.energy 0
  balance : ∀ t₁ t₂, 0≤t₁ → t₁≤t₂ → t₂≤T →
    s.energy t₂+∫ t in t₁..t₂, s.dissipation t=s.energy t₁

/-- 光滑兼容解类的全域先验能量定理，对应V7定理6.1的本轮已核验版本。
所有Green/Poincaré/交换/兼容保持在证明链内产生；输入仅为原模型和明确强正则性。
这是给定解的先验结论，包含两端点与T=0；不附带一般解存在唯一性或严格衰减。 -/
theorem main_energy_estimate_smoothRectangle {D : Rect} {R : RegionalAbsorption D}
    {ε κ τ μ T : ℝ} (s : SmoothCompatibleSolution R ε κ τ μ T) :
    SmoothEnergyConclusions s := by
  -- 下面各条分别调用已由原方程装配出的具体问题，不能把输出包回填为输入。
  exact ⟨s.energy_antitone,fun _ ht => s.energy_law_and_closure ht,
    fun _ ht => s.energy_graph_bounds ht,fun _ ht => s.energy_initial_bounds ht,
    fun _ ht => s.physical_current_bound ht,fun _ ht => s.physical_initial_bound ht,
    fun _ _ ht₁ ht₁₂ ht₂ => s.energy_integral_balance ht₁ ht₁₂ ht₂⟩

end LeanPML.PML.SmoothRectangle
