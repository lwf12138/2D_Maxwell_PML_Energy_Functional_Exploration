import LeanPML.PML.ClassicalSystem

/-!
# v0.4 对齐：幅度条件只施加于实际计算矩形

对应 V7 §1、(5.3)、(5.5) 及 (6.2)。原始 p(x)、r(y) 可在矩形邻域光滑延拓，
但非负和幅度界只要求在各自的闭区间上成立。为复用旧 L² 乘子实现，内部先把
坐标截回该区间，再读取原系数；这样得到全空间有界可测代表，而非增加全轴物理假设。
闭矩形内代表逐点等于原系数，故矩形测度下系数、权重及能量密度几乎处处相等。
截回后的代表无需在端点光滑；原 PDE 始终使用原 p、r 的真实域内取值。

阅读顺序：RegionalAbsorption → coefficients_eq_closed → fieldEnergy_eq_regional_integral。
本文件不修改域、不加吸收正下界，不把任何能量结论或全时段兼容放入系数结构。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open LeanPML.Analysis LeanPML.PML LeanPML.PML.Concrete
namespace LeanPML.Rectangle

/-- 只保存 V7 (5.3) 在实际闭矩形上的原始系数条件。
p/r 的 C∞ 是本轮技术延拓正则性；幅度约束明确只在 Icc xlo xhi / Icc ylo yhi。
S 的非负性无需另设字段，可由非空区间上的 p≥0、p≤S 推出。 -/
structure RegionalAbsorption (D : Rect) where
  c : ℝ
  S : ℝ
  c_pos : 0<c
  p : ℝ→ℝ
  r : ℝ→ℝ
  p_smooth : ContDiff ℝ ∞ p
  r_smooth : ContDiff ℝ ∞ r
  p_bounds : ∀ x∈Icc D.xlo D.xhi, 0≤p x ∧ p x≤S
  r_bounds : ∀ y∈Icc D.ylo D.yhi, 0≤r y ∧ r y≤S
  S_le_quarter : S≤c/4

/-- 把实数坐标截回闭区间；它只服务于实际 L² 代表，不是坐标拉伸模型。 -/
def clampInterval (lo hi x : ℝ) : ℝ := max lo (min hi x)

/-- 截回坐标确在闭区间内，保证只调用区域内的原始幅度假设。 -/
theorem clampInterval_mem (lo hi : ℝ) (hlohi : lo≤hi) (x : ℝ) :
    clampInterval lo hi x ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le hlohi (min_le_left _ _)⟩

/-- 区间内截回恒等；包括两个端点，因而四边上的系数也没有被修改。 -/
theorem clampInterval_eq (lo hi x : ℝ) (hx : x∈Icc lo hi) :
    clampInterval lo hi x=x := by
  simp only [clampInterval,min_eq_right hx.2,max_eq_right hx.1]

namespace RegionalAbsorption
variable {D : Rect}

/-- 内部有界代表 p∘clamp，外部值只为旧乘子 API 提供实现数据。 -/
def pExtend (R : RegionalAbsorption D) (x : ℝ) : ℝ :=
  R.p (clampInterval D.xlo D.xhi x)
/-- y 向同一处理，保留原分离形式。 -/
def rExtend (R : RegionalAbsorption D) (y : ℝ) : ℝ :=
  R.r (clampInterval D.ylo D.yhi y)

/-- 截回函数连续，所以内部 p 代表可测；不声称截回在端点可微。 -/
theorem pExtend_continuous (R : RegionalAbsorption D) : Continuous R.pExtend :=
  R.p_smooth.continuous.comp (continuous_const.max (continuous_const.min continuous_id))
/-- r 代表连续可测，供 y 向 L² 乘子使用。 -/
theorem rExtend_continuous (R : RegionalAbsorption D) : Continuous R.rExtend :=
  R.r_smooth.continuous.comp (continuous_const.max (continuous_const.min continuous_id))

/-- 有界可测实现从区域内条件构造；调用者没有提供全轴幅度界。 -/
def coefficients (R : RegionalAbsorption D) : SpatialAbsorption (ℝ×ℝ) :=
  SpatialAbsorption.separated R.c R.S R.c_pos R.pExtend R.rExtend
    R.pExtend_continuous.measurable R.rExtend_continuous.measurable
    (fun x => (R.p_bounds _ (clampInterval_mem _ _ D.x_lt.le x)).1)
    (fun y => (R.r_bounds _ (clampInterval_mem _ _ D.y_lt.le y)).1)
    (fun x => (R.p_bounds _ (clampInterval_mem _ _ D.x_lt.le x)).2)
    (fun y => (R.r_bounds _ (clampInterval_mem _ _ D.y_lt.le y)).2)
    R.S_le_quarter

/-- S≥0 来自真实非空闭区间上的原假设，而非无说明的平方步骤。 -/
theorem S_nonneg (R : RegionalAbsorption D) : 0≤R.S :=
  (R.p_bounds D.xlo ⟨le_rfl,D.x_lt.le⟩).1.trans
    (R.p_bounds D.xlo ⟨le_rfl,D.x_lt.le⟩).2

/-- 内部代表与原 p 在闭 x 区间逐点相同。 -/
theorem pExtend_eq (R : RegionalAbsorption D) {x : ℝ} (hx : x∈Icc D.xlo D.xhi) :
    R.pExtend x=R.p x := by rw [pExtend,clampInterval_eq _ _ _ hx]
/-- 内部代表与原 r 在闭 y 区间逐点相同。 -/
theorem rExtend_eq (R : RegionalAbsorption D) {y : ℝ} (hy : y∈Icc D.ylo D.yhi) :
    R.rExtend y=R.r y := by rw [rExtend,clampInterval_eq _ _ _ hy]

/-- 整个闭矩形（含四边）内的系数完全不变；后续 PDE 仍是原方程。 -/
theorem coefficients_eq_closed (R : RegionalAbsorption D) {X : ℝ×ℝ}
    (hX : X∈D.closedSet) :
    R.coefficients.p X=R.p X.1 ∧ R.coefficients.r X=R.r X.2 :=
  ⟨R.pExtend_eq hX.1,R.rExtend_eq hX.2⟩

/-- 计算域测度下 a.e. 一致。矩形以外没有物理积分，不需控制原延拓的幅度。 -/
theorem coefficients_ae (R : RegionalAbsorption D) :
    R.coefficients.p =ᵐ[D.measure] (fun X => R.p X.1) ∧
    R.coefficients.r =ᵐ[D.measure] (fun X => R.r X.2) := by
  have hclosed : ∀ᵐ X ∂D.measure, X∈D.closedSet := by
    rw [D.measure_eq_closed]
    exact ae_restrict_mem D.closedSet_compact.measurableSet
  exact ⟨hclosed.mono (fun _ hX => (R.coefficients_eq_closed hX).1),
    hclosed.mono (fun _ hX => (R.coefficients_eq_closed hX).2)⟩

/-- 原始能量权重与内部实现 a.e. 相同，包括零区两者均取 0。
不需要权重本质有界，也不除以吸收系数。 -/
theorem weights_ae (R : RegionalAbsorption D) :
    R.coefficients.wx =ᵐ[D.measure] (fun X => energyWeightX R.c (R.p X.1) (R.r X.2)) ∧
    R.coefficients.wy =ᵐ[D.measure] (fun X => energyWeightY R.c (R.p X.1) (R.r X.2)) := by
  constructor <;> filter_upwards [R.coefficients_ae.1,R.coefficients_ae.2] with X hp hr
  · change energyWeightX R.c (R.coefficients.p X) (R.coefficients.r X)=_
    rw [hp,hr]
  · change energyWeightY R.c (R.coefficients.p X) (R.coefficients.r X)=_
    rw [hp,hr]

/-- 原加权成员条件与内部代表条件等价；不是新增的全空间加权积分要求。
具体的加权范数仍由旧 WeightedL2 承载，积分测度始终为整个 D.measure。 -/
theorem weighted_memLp_iff (R : RegionalAbsorption D) (f : ℝ×ℝ→ℝ) :
    (MemLp (fun X => Real.sqrt (R.coefficients.wx X)*f X) 2 D.measure ↔
      MemLp (fun X => Real.sqrt (energyWeightX R.c (R.p X.1) (R.r X.2))*f X) 2 D.measure) ∧
    (MemLp (fun X => Real.sqrt (R.coefficients.wy X)*f X) 2 D.measure ↔
      MemLp (fun X => Real.sqrt (energyWeightY R.c (R.p X.1) (R.r X.2))*f X) 2 D.measure) := by
  have hx : (fun X => Real.sqrt (R.coefficients.wx X)*f X) =ᵐ[D.measure]
      (fun X => Real.sqrt (energyWeightX R.c (R.p X.1) (R.r X.2))*f X) :=
    R.weights_ae.1.mono (fun X hX => congrArg (fun w : ℝ => Real.sqrt w*f X) hX)
  have hy : (fun X => Real.sqrt (R.coefficients.wy X)*f X) =ᵐ[D.measure]
      (fun X => Real.sqrt (energyWeightY R.c (R.p X.1) (R.r X.2))*f X) :=
    R.weights_ae.2.mono (fun X hX => congrArg (fun w : ℝ => Real.sqrt w*f X) hX)
  exact ⟨memLp_congr_ae hx,memLp_congr_ae hy⟩

/-- 原 p/r 的 V7 (6.2) 密度；只换回原函数系数，状态与物理恢复映射保持同一个。
这是表示定义，不是另一套能量定理。 -/
def energyDensity (R : RegionalAbsorption D) (ε κ τ μ : ℝ)
    (U : FieldState D.measure R.coefficients.wx R.coefficients.wy) (X : ℝ×ℝ) : ℝ :=
  Obstructions.singleLayerEnergy ε κ τ μ R.c (R.p X.1) (R.r X.2)
    (U.v X) (U.V X) (U.R X) (U.z X)
    (U.Λx X-physicalX D.measure R.coefficients U.ψx X)
    (U.Λy X-physicalY D.measure R.coefficients U.ψy X) (U.Λx X) (U.Λy X)

/-- 密度 a.e. 一致，从而同一实际 L² 能量既可使用内部代表，也可使用原 p/r。 -/
theorem energyDensity_ae (R : RegionalAbsorption D) (ε κ τ μ : ℝ)
    (U : FieldState D.measure R.coefficients.wx R.coefficients.wy) :
    fieldEnergyDensity D.measure R.coefficients ε κ τ μ U =ᵐ[D.measure]
      R.energyDensity ε κ τ μ U := by
  filter_upwards [R.coefficients_ae.1,R.coefficients_ae.2] with X hp hr
  change Obstructions.singleLayerEnergy ε κ τ μ R.c (R.coefficients.p X)
    (R.coefficients.r X) _ _ _ _ _ _ _ _ = _
  rw [hp,hr]
  rfl

/-- 原系数密度确实可积：由旧工程的 L² 与加权块可积性沿 a.e. 相等传递。 -/
theorem energyDensity_integrable (R : RegionalAbsorption D) (ε κ τ μ : ℝ)
    (U : FieldState D.measure R.coefficients.wx R.coefficients.wy) :
    Integrable (R.energyDensity ε κ τ μ U) D.measure :=
  (fieldEnergyDensity_integrable D.measure R.coefficients ε κ τ μ U).congr
    (R.energyDensity_ae ε κ τ μ U)

/-- 内积能量等于原始区域系数的真实积分。前条提供可积性，
因此不是利用 Lean 对不可积函数的积分总定义得到一个形式相等。 -/
theorem fieldEnergy_eq_regional_integral (R : RegionalAbsorption D) (ε κ τ μ : ℝ)
    (U : FieldState D.measure R.coefficients.wx R.coefficients.wy) :
    fieldEnergy D.measure R.coefficients ε κ τ μ U=
      ∫ X, R.energyDensity ε κ τ μ U X ∂D.measure := by
  rw [fieldEnergy_eq_integral]
  exact integral_congr_ae (R.energyDensity_ae ε κ τ μ U)



/-- 原 p/r 的单层耗散密度，方向与零区贡献完全沿用既有定义。 -/
def dissipationDensity (R : RegionalAbsorption D) (ε κ τ μ : ℝ)
    (U : FieldState D.measure R.coefficients.wx R.coefficients.wy)
    (Rdot : ScalarL2 D.measure) (X : ℝ×ℝ) : ℝ :=
  Obstructions.singleLayerDissipation ε κ τ μ R.c (R.p X.1) (R.r X.2)
    (U.v X) (U.V X) (U.R X) (U.z X) (Rdot X)
    (spatialComponentX U X) (spatialComponentY U X) (U.Λx X) (U.Λy X)

/-- (7.7) 密度在矩形上 a.e. 不变，包括原零区的 c|∇v|² 项。
没有由系数截回推导 D≥0；这里只证明积分表示一致。 -/
theorem dissipationDensity_ae (R : RegionalAbsorption D) (ε κ τ μ : ℝ)
    (U : FieldState D.measure R.coefficients.wx R.coefficients.wy)
    (Rdot : ScalarL2 D.measure) :
    fieldDissipationDensity D.measure R.coefficients ε κ τ μ U Rdot =ᵐ[D.measure]
      R.dissipationDensity ε κ τ μ U Rdot := by
  filter_upwards [R.coefficients_ae.1,R.coefficients_ae.2] with X hp hr
  change Obstructions.singleLayerDissipation ε κ τ μ R.c (R.coefficients.p X)
    (R.coefficients.r X) _ _ _ _ _ _ _ _ _ = _
  rw [hp,hr]
  rfl

/-- 原耗散密度也确实可积，来自既有实际普通/加权 L² 分析。 -/
theorem dissipationDensity_integrable (R : RegionalAbsorption D) (ε κ τ μ : ℝ)
    (U : FieldState D.measure R.coefficients.wx R.coefficients.wy)
    (Rdot : ScalarL2 D.measure) :
    Integrable (R.dissipationDensity ε κ τ μ U Rdot) D.measure :=
  (fieldDissipationDensity_integrable D.measure R.coefficients ε κ τ μ U Rdot).congr
    (R.dissipationDensity_ae ε κ τ μ U Rdot)

/-- 耗散的实际积分也接回原区域系数；并非另一套抽象实数表达式。 -/
theorem fieldDissipation_eq_regional_integral (R : RegionalAbsorption D) (ε κ τ μ : ℝ)
    (U : FieldState D.measure R.coefficients.wx R.coefficients.wy)
    (Rdot : ScalarL2 D.measure) :
    fieldDissipation D.measure R.coefficients ε κ τ μ U Rdot=
      ∫ X, R.dissipationDensity ε κ τ μ U Rdot X ∂D.measure := by
  rw [fieldDissipation_eq_integral]
  exact integral_congr_ae (R.dissipationDensity_ae ε κ τ μ U Rdot)

/-- 域内系数等式，供逐条原八方程改写；不改变任何空间或时间导数。 -/
theorem coefficients_eq_open (R : RegionalAbsorption D) {X : ℝ×ℝ}
    (hX : X∈D.openSet) :
    R.pExtend X.1=R.p X.1 ∧ R.rExtend X.2=R.r X.2 :=
  ⟨R.pExtend_eq ⟨hX.1.1.le,hX.1.2.le⟩,
    R.rExtend_eq ⟨hX.2.1.le,hX.2.2.le⟩⟩

/-- (2.1) 的八方程只读取当前空间点上的 p/r 值，所以域内可安全换为
内部代表；真正的时空导数证据原样保留，未对截回系数作空间求导。 -/
theorem originalAt_extend (R : RegionalAbsorption D) (ε κ τ μ : ℝ)
    (F : OriginalFields) (t : ℝ) (X : Point) (hX : X∈D.openSet)
    (hODE : OriginalAt ε κ τ μ R.p R.r F t X) :
    OriginalAt ε κ τ μ R.pExtend R.rExtend F t X := by
  obtain ⟨hp,hr⟩ := R.coefficients_eq_open hX
  refine { hODE.toOriginalHasDerivAt with
    electric := ?_, magneticX := ?_, magneticY := ?_, debye := hODE.debye
    memory1 := ?_, memory2 := ?_, auxiliaryX := ?_, auxiliaryY := ?_ }
  · simpa only [hp,hr] using hODE.electric
  · simpa only [hp,hr] using hODE.magneticX
  · simpa only [hp,hr] using hODE.magneticY
  · simpa only [hp,hr] using hODE.memory1
  · simpa only [hp,hr] using hODE.memory2
  · simpa only [hp,hr] using hODE.auxiliaryX
  · simpa only [hp,hr] using hODE.auxiliaryY

/-- 初始五个兼容关系在域内也不变；不增加全时段条件。 -/
theorem initialCompatible_extend (R : RegionalAbsorption D) (ε κ τ : ℝ)
    (F : OriginalFields) (U : PrimitiveFields) (X : Point) (hX : X∈D.openSet)
    (hinit : InitialCompatible F U ε κ τ R.p R.r X) :
    InitialCompatible F U ε κ τ R.pExtend R.rExtend X := by
  obtain ⟨hp,hr⟩ := R.coefficients_eq_open hX
  refine ⟨hinit.debye,?_,?_,?_,?_⟩
  · simpa only [invariantZ1,hp,hr] using hinit.memory1
  · simpa only [invariantZ2,hp,hr] using hinit.memory2
  · simpa only [invariantX,hp] using hinit.magneticX
  · simpa only [invariantY,hr] using hinit.magneticY



/-- 域内换代表保留古典原解：八条真实演化已逐条改写，空间可导证据完全不变。
系数本身不被空间求导，因此无需要求截回代表在端点光滑。 -/
theorem originalClassicalOn_extend (R : RegionalAbsorption D) (ε κ τ μ T : ℝ)
    (F : OriginalFields)
    (hclassical : OriginalClassicalOn D.openSet T ε κ τ μ R.p R.r F) :
    OriginalClassicalOn D.openSet T ε κ τ μ R.pExtend R.rExtend F := by
  refine ⟨?_,hclassical.spatial⟩
  intro t ht X hX
  exact R.originalAt_extend ε κ τ μ F t X hX (hclassical.equations t ht X hX)

/-- 推荐的区域系数原模型入口。物理系数条件只来自 RegionalAbsorption 的
闭区间 bounds；输入的 PDE 仍用原 p/r，只在 `(0,T)×Ω` 成立。
μ≠0 与光滑磁场识别先推出原场真实空间可导，填入 ClassicalSystem 包装；
再在域内改写为内部代表并调用已证明的具体 Green/Poincaré 总装。
全时段兼容、零区保持及所有能量结论都不是输入。T=0 的初始图兼容仍显式保留。 -/
def originalRegionalFiniteIntervalProblem (R : RegionalAbsorption D)
    (ε κ τ μ T : ℝ) (F : OriginalFields) (u₀ q₀ : Point→ℝ)
    (B : SmoothStateData) (reg : SmoothStateRegular D R.coefficients B)
    (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T) (hμ : μ≠0)
    (hregular : OriginalLiftRegular F u₀)
    (hOriginal : OriginalOn D.openSet T ε κ τ μ R.p R.r F)
    (hinitial : ∀ X∈D.openSet,
      InitialCompatible F (lift F μ u₀ q₀) ε κ τ R.p R.r X)
    (hφzero : ∀ X∈D.openSet, R.p X.1+R.r X.2=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀)
    (hdegenerate : T=0 → InitialDerivativeCompatible D R.coefficients B κ τ) :
    FiniteIntervalProblemConditional (greenDomain D) R.coefficients ε κ τ μ
      (poincareConstant D) T (poincare_estimate D) := by
  -- 空间可导由真实光滑代表和 μ≠0 推出，不能利用 fderiv 的总定义充当证据。
  have hclassical : OriginalClassicalOn D.openSet T ε κ τ μ R.p R.r F :=
    originalClassicalOn_of_liftIdentified D.openSet ε κ τ μ T R.p R.r F u₀ q₀
      B hid hμ hOriginal
  have hextended := R.originalClassicalOn_extend ε κ τ μ T F hclassical
  have hinitial_extended : ∀ X∈D.openSet,
      InitialCompatible F (lift F μ u₀ q₀) ε κ τ R.pExtend R.rExtend X := by
    intro X hX
    exact R.initialCompatible_extend ε κ τ F _ X hX (hinitial X hX)
  have hφzero_extended : ∀ X∈D.openSet, R.coefficients.a X=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0 := by
    intro X hX ha
    obtain ⟨hp,hr⟩ := R.coefficients_eq_open hX
    change R.pExtend X.1+R.rExtend X.2=0 at ha
    rw [hp,hr] at ha
    exact hφzero X hX ha
  exact originalClassicalFiniteIntervalProblem D R.coefficients ε κ τ μ T
    R.pExtend R.rExtend F u₀ q₀ B reg hid hT (fun _ => rfl) (fun _ => rfl)
    hregular hextended hinitial_extended hφzero_extended hPEC hu₀ hdegenerate

/-- 区域入口保留实际 P_tt 的闭区间 L² 连续性，供下一阶段时间积分平衡。
不把耗散可积性或积分恒等式追加为输入。 -/
theorem originalRegionalFiniteIntervalProblem_second_R_continuous
    (R : RegionalAbsorption D) (ε κ τ μ T : ℝ)
    (F : OriginalFields) (u₀ q₀ : Point→ℝ)
    (B : SmoothStateData) (reg : SmoothStateRegular D R.coefficients B)
    (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T) (hμ : μ≠0)
    (hregular : OriginalLiftRegular F u₀)
    (hOriginal : OriginalOn D.openSet T ε κ τ μ R.p R.r F)
    (hinitial : ∀ X∈D.openSet,
      InitialCompatible F (lift F μ u₀ q₀) ε κ τ R.p R.r X)
    (hφzero : ∀ X∈D.openSet, R.p X.1+R.r X.2=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀)
    (hdegenerate : T=0 → InitialDerivativeCompatible D R.coefficients B κ τ) :
    ContinuousOn (fun t => ((R.originalRegionalFiniteIntervalProblem ε κ τ μ T F u₀ q₀
      B reg hid hT hμ hregular hOriginal hinitial hφzero hPEC hu₀ hdegenerate).path.second t).R)
      (Icc 0 T) :=
  (continuous_jet_L2 D B.R reg.R).2.2.continuousOn

end RegionalAbsorption
end LeanPML.Rectangle
