import LeanPML.Rectangle.WeakCompactApprox
import LeanPML.Rectangle.SmoothWeakClosure

/-!
# 区域 W¹,∞ 乘 H₀¹：真实图闭包保持

将既有 W¹,∞×H₀¹→H¹ 进一步接到同一 H₀¹ 图闭包。
先对系数乘内部测试函数做真实卷积；用弱测试关系识别两个经典偏导，
再证明三分量同时 L² 收敛，最后以连续线性图映射推广到全部 H₀¹。
不假设目标闭包或存在逼近序列；不要求系数 C∞ 或吸收正下界。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace Convolution
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

local instance rectangleVolumeHaar : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  infer_instance

/-- 区域弱系数乘内部测试函数的全空间零延拓代表。
域外值仅服务卷积，实际矩形 L² 中与原区域乘子相等。 -/
def compactWeakProduct {D : Rect} (m : RegionalWeakCoefficient D) (f : TestFunction D) :
    ℝ × ℝ → ℝ := fun x => m.value.extended x * f.field x

/-- 该粗糙乘积真实可积：紧支光滑因子可积，系数是已证有界可测乘子。 -/
theorem compactWeakProduct_integrable {D : Rect} (m : RegionalWeakCoefficient D)
    (f : TestFunction D) : Integrable (compactWeakProduct m f) volume := by
  apply (f.field.continuous.integrable_of_hasCompactSupport f.compact).bdd_mul
    m.value.extended_measurable.aestronglyMeasurable
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using m.value.extended_bound x

/-- 粗糙乘积的拓扑支撑仍在原测试函数的支撑内，因此严格远离外边界。 -/
theorem compactWeakProduct_support {D : Rect} (m : RegionalWeakCoefficient D)
    (f : TestFunction D) :
    HasCompactSupport (compactWeakProduct m f) ∧
      tsupport (compactWeakProduct m f) ⊆ tsupport (⇑f.field) := by
  exact ⟨f.compact.mul_left, tsupport_mul_subset_right⟩

/-- 粗糙乘积具有真正全局统一界；该事实用于卷积后的平方差支配收敛。
不是假设任何能量权重有界。 -/
theorem compactWeakProduct_bounded {D : Rect} (m : RegionalWeakCoefficient D)
    (f : TestFunction D) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖compactWeakProduct m f x‖ ≤ C := by
  obtain ⟨B, hB⟩ := (f.compact.isCompact_range f.field.continuous).isBounded.exists_norm_le
  refine ⟨m.value.bound * max B 0, mul_nonneg m.value.bound_nonneg (le_max_right _ _), ?_⟩
  intro x
  rw [compactWeakProduct, norm_mul]
  apply mul_le_mul
  · simpa only [Real.norm_eq_abs] using m.value.extended_bound x
  · exact (hB (f.field x) (mem_range_self x)).trans (le_max_left _ _)
  · exact norm_nonneg _
  · exact m.value.bound_nonneg

/-- 零延拓乘积与既有弱乘积函数坐标 a.e. 一致；不读取商类在指定点的值。 -/
theorem compactWeakProduct_ae {D : Rect} (m : RegionalWeakCoefficient D)
    (f : TestFunction D) :
    compactWeakProduct m f =ᵐ[D.measure]
      ⇑(m.value.operator (SmoothField.toL2 D f.field)) := by
  filter_upwards [m.value.operator_ae (SmoothField.toL2 D f.field),
    m.value.extended_ae, SmoothField.coe_toL2 D f.field] with x hop hext hf
  simp only [compactWeakProduct, hext, hop, hf]

/-- 对实际粗糙乘积调用卷积的 L² 收敛，不假设这个乘积属于 H₀¹。
两个偏导的同核识别见下方 compactWeakProduct_mollified_partial。 -/
theorem compactWeakProduct_mollified_value_tendsto {D : Rect}
    (m : RegionalWeakCoefficient D) (f : TestFunction D)
    (ρ : ℕ → ContDiffBump (0 : ℝ × ℝ))
    (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hratio : ∀ᶠ n in atTop, (ρ n).rOut ≤ K*(ρ n).rIn) :
    Tendsto (fun n => SmoothField.toL2 D
      (mollifiedField (ρ n) (compactWeakProduct m f) (compactWeakProduct_integrable m f).locallyIntegrable))
      atTop (𝓝 (m.value.operator (SmoothField.toL2 D f.field))) := by
  obtain ⟨C, hC, hbound⟩ := compactWeakProduct_bounded m f
  exact mollifiedField_toL2_tendsto D ρ hρ hratio (compactWeakProduct m f)
    (compactWeakProduct_integrable m f).locallyIntegrable _ (compactWeakProduct_ae m f) hC hbound

/-- 对上述真实粗糙乘积，卷积核充分小时给出 Ω 内紧支光滑函数。
核的边界余量由实际紧支性推出，没有输入所需逼近序列。 -/
theorem compactWeakProduct_mollified_inside {D : Rect}
    (m : RegionalWeakCoefficient D) (f : TestFunction D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ContDiffBump (0 : ℝ × ℝ), ρ.rOut ≤ δ →
      HasCompactSupport (⇑(mollifiedField ρ (compactWeakProduct m f)
        (compactWeakProduct_integrable m f).locallyIntegrable)) ∧
      tsupport (⇑(mollifiedField ρ (compactWeakProduct m f)
        (compactWeakProduct_integrable m f).locallyIntegrable)) ⊆ D.openSet := by
  exact mollifiedField_support_inside D _ (compactWeakProduct_integrable m f).locallyIntegrable
    (compactWeakProduct_support m f).1 ((compactWeakProduct_support m f).2.trans f.support_inside)

/-- 内部测试函数乘任意光滑函数仍是合法测试函数。
此处第二因子可以是平移卷积核，不要求它的支撑位于 Ω。 -/
def testMultiplySmooth {D : Rect} (f : TestFunction D) (q : SmoothField) : TestFunction D where
  field := smoothProduct f.field q
  compact := f.compact.mul_right
  support_inside := tsupport_mul_subset_left.trans f.support_inside

/-- 粗糙紧支乘积对任意全空间光滑探针满足无边界弱分部积分。
来源是 m 的内部弱导数定义，测试函数取 f·q；q 无需内部紧支。
这是将区域弱导数转移到平移卷积核的关键恒等式，不是一般 Green 假设。 -/
theorem compactWeakProduct_pair_smooth (D : Rect) (m : RegionalWeakCoefficient D)
    (f : TestFunction D) (q : SmoothField) (i : Fin 2) :
    ⟪(m.derivative i).operator (SmoothField.toL2 D f.field) +
        m.value.operator (SmoothField.toL2 D (smoothPartial i f.field)),
      SmoothField.toL2 D q⟫_ℝ =
      -⟪m.value.operator (SmoothField.toL2 D f.field),
        SmoothField.toL2 D (smoothPartial i q)⟫_ℝ := by
  have hweak := m.weak_partial i (testMultiplySmooth f q)
  have hderiv_split :
      ⟪m.value.toL2, SmoothField.toL2 D (smoothPartial i (testMultiplySmooth f q).field)⟫_ℝ =
      ⟪m.value.toL2, SmoothField.toL2 D (smoothProduct (smoothPartial i f.field) q)⟫_ℝ +
      ⟪m.value.toL2, SmoothField.toL2 D (smoothProduct f.field (smoothPartial i q))⟫_ℝ := by
    rw [← inner_add_right, ← map_add]
    congr 2
    apply Subtype.ext
    funext x
    exact smoothPartial_product i f.field q x
  rw [hderiv_split] at hweak
  rw [inner_add_left, inner_regional_smooth, inner_regional_smooth, inner_regional_smooth]
  change ⟪(m.derivative i).toL2, SmoothField.toL2 D (smoothProduct f.field q)⟫_ℝ = _ at hweak
  linarith

/-- 粗糙乘积的弱偏导代表，按既有 Leibniz 公式选取。
系数域外零延拓不声称跨边界可微；紧支因子负责消除边界。 -/
def compactWeakProductDerivative {D : Rect} (m : RegionalWeakCoefficient D)
    (f : TestFunction D) (i : Fin 2) : ℝ × ℝ → ℝ := fun x =>
  (m.derivative i).extended x * f.field x +
    m.value.extended x * smoothPartial i f.field x

/-- 所选弱偏导代表与已有实际图坐标 a.e. 一致。 -/
theorem compactWeakProductDerivative_ae {D : Rect} (m : RegionalWeakCoefficient D)
    (f : TestFunction D) (i : Fin 2) :
    compactWeakProductDerivative m f i =ᵐ[D.measure]
      ⇑((m.derivative i).operator (SmoothField.toL2 D f.field) +
        m.value.operator (SmoothField.toL2 D (smoothPartial i f.field))) := by
  filter_upwards [(m.derivative i).operator_ae (SmoothField.toL2 D f.field),
    m.value.operator_ae (SmoothField.toL2 D (smoothPartial i f.field)),
    (m.derivative i).extended_ae, m.value.extended_ae,
    SmoothField.coe_toL2 D f.field, SmoothField.coe_toL2 D (smoothPartial i f.field),
    Lp.coeFn_add ((m.derivative i).operator (SmoothField.toL2 D f.field))
      (m.value.operator (SmoothField.toL2 D (smoothPartial i f.field)))]
    with x hdm hm hedm hem hf hdf hadd
  simp only [compactWeakProductDerivative, hadd, Pi.add_apply, hdm, hm, hedm, hem, hf, hdf]

/-- 支撑于 Ω 的可测代表与光滑函数的全域积分，等于矩形 L² 配对。
域外为零与域内 a.e. 一致性分开输入；该桥接供卷积核测试使用。 -/
theorem supported_integral_eq_inner (D : Rect) (g : ℝ × ℝ → ℝ)
    (v : ScalarL2 D.measure) (hrep : g =ᵐ[D.measure] ⇑v)
    (hout : ∀ x ∉ D.openSet, g x = 0) (q : SmoothField) :
    (∫ x, g x * q x) = ⟪v, SmoothField.toL2 D q⟫_ℝ := by
  have hind : D.openSet.indicator (fun x => g x*q x) = (fun x => g x*q x) := by
    funext x
    by_cases hx : x ∈ D.openSet
    · simp [hx]
    · simp [hx, hout x hx]
  rw [← hind, integral_indicator D.openSet_open.measurableSet, inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [hrep, SmoothField.coe_toL2 D q] with x hg hq
  rw [hg, hq]

/-- 将已有区域弱导数变成针对任意全空间光滑探针的全域积分恒等式。
这是实际证明的导数转移，不是假设卷积偏导或目标 H₀¹ 成员。 -/
theorem compactWeakProduct_integral_partial (D : Rect) (m : RegionalWeakCoefficient D)
    (f : TestFunction D) (q : SmoothField) (i : Fin 2) :
    (∫ x, compactWeakProductDerivative m f i x * q x) =
      -(∫ x, compactWeakProduct m f x * smoothPartial i q x) := by
  rw [supported_integral_eq_inner D _ _ (compactWeakProductDerivative_ae m f i)
    (fun x hx => by simp [compactWeakProductDerivative, RegionalBounded.extended, hx]) q]
  rw [supported_integral_eq_inner D _ _ (compactWeakProduct_ae m f)
    (fun x hx => by simp [compactWeakProduct, RegionalBounded.extended, hx]) (smoothPartial i q)]
  exact compactWeakProduct_pair_smooth D m f q i

/-- 内部测试函数的一阶实际偏导仍是内部测试函数。 -/
def testPartial {D : Rect} (f : TestFunction D) (i : Fin 2) : TestFunction D where
  field := smoothPartial i f.field
  compact := by
    fin_cases i
    · exact f.compact.fderiv_apply ℝ (1,0)
    · exact f.compact.fderiv_apply ℝ (0,1)
  support_inside := by
    fin_cases i
    · exact (tsupport_fderiv_apply_subset ℝ (1,0)).trans f.support_inside
    · exact (tsupport_fderiv_apply_subset ℝ (0,1)).trans f.support_inside

/-- 弱偏导代表的实际可积性；两个项分别由区域有界系数乘紧支光滑函数得到。 -/
theorem compactWeakProductDerivative_integrable {D : Rect} (m : RegionalWeakCoefficient D)
    (f : TestFunction D) (i : Fin 2) : Integrable (compactWeakProductDerivative m f i) volume := by
  have hfirst : Integrable (fun x => (m.derivative i).extended x*f.field x) volume := by
    apply (f.field.continuous.integrable_of_hasCompactSupport f.compact).bdd_mul
      (m.derivative i).extended_measurable.aestronglyMeasurable
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (m.derivative i).extended_bound x
  have hsecond : Integrable (fun x => m.value.extended x*smoothPartial i f.field x) volume := by
    apply ((testPartial f i).field.continuous.integrable_of_hasCompactSupport
      (testPartial f i).compact).bdd_mul m.value.extended_measurable.aestronglyMeasurable
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using m.value.extended_bound x
  exact hfirst.add hsecond

/-- 弱偏导代表统一有界；为导数卷积的 L² 收敛提供实际支配证据。 -/
theorem compactWeakProductDerivative_bounded {D : Rect} (m : RegionalWeakCoefficient D)
    (f : TestFunction D) (i : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖compactWeakProductDerivative m f i x‖ ≤ C := by
  obtain ⟨B, hB⟩ := (f.compact.isCompact_range f.field.continuous).isBounded.exists_norm_le
  obtain ⟨B', hB'⟩ := ((testPartial f i).compact.isCompact_range
    (testPartial f i).field.continuous).isBounded.exists_norm_le
  let C₀ := (m.derivative i).bound * max B 0
  let C₁ := m.value.bound * max B' 0
  have hC₀ : 0 ≤ C₀ := mul_nonneg (m.derivative i).bound_nonneg (le_max_right _ _)
  have hC₁ : 0 ≤ C₁ := mul_nonneg m.value.bound_nonneg (le_max_right _ _)
  refine ⟨C₀+C₁, add_nonneg hC₀ hC₁, fun x => ?_⟩
  have hfirst : ‖(m.derivative i).extended x*f.field x‖ ≤ C₀ := by
    rw [norm_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using (m.derivative i).extended_bound x)
      ((hB (f.field x) (mem_range_self x)).trans (le_max_left _ _)) (norm_nonneg _) (m.derivative i).bound_nonneg
  have hsecond : ‖m.value.extended x*smoothPartial i f.field x‖ ≤ C₁ := by
    rw [norm_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using m.value.extended_bound x)
      ((hB' ((testPartial f i).field x) (mem_range_self x)).trans (le_max_left _ _)) (norm_nonneg _) m.value.bound_nonneg
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

/-- 关键弱导数转移：粗糙乘积卷积的实际偏导，等于其弱偏导的同核卷积。
先对光滑核真实求导，再以 f·核作为合法测试函数使用区域弱导数定义。
这条恒等式使三份 L² 收敛确实来自同一批光滑函数的 H¹ 图。 -/
theorem compactWeakProduct_mollified_partial {D : Rect} (m : RegionalWeakCoefficient D)
    (f : TestFunction D) (ρ : ContDiffBump (0 : ℝ × ℝ)) (i : Fin 2) (x : ℝ × ℝ) :
    smoothPartial i (mollifiedField ρ (compactWeakProduct m f)
      (compactWeakProduct_integrable m f).locallyIntegrable) x =
    mollifiedField ρ (compactWeakProductDerivative m f i)
      (compactWeakProductDerivative_integrable m f i).locallyIntegrable x := by
  let k : SmoothField := ⟨ρ.normed volume, ρ.contDiff.div_const _⟩
  have hleft : smoothPartial i (mollifiedField ρ (compactWeakProduct m f)
        (compactWeakProduct_integrable m f).locallyIntegrable) x =
      ∫ y, compactWeakProduct m f y * smoothPartial i k (x-y) := by
    fin_cases i
    · exact mollifiedField_fderiv ρ _ (compactWeakProduct_integrable m f).locallyIntegrable x (1,0)
    · exact mollifiedField_fderiv ρ _ (compactWeakProduct_integrable m f).locallyIntegrable x (0,1)
  have hweak := compactWeakProduct_integral_partial D m f (reflectedSmooth k x) i
  simp_rw [smoothPartial_reflected, mul_neg] at hweak
  rw [integral_neg, neg_neg] at hweak
  have hright : mollifiedField ρ (compactWeakProductDerivative m f i)
        (compactWeakProductDerivative_integrable m f i).locallyIntegrable x =
      ∫ y, compactWeakProductDerivative m f i y * k (x-y) := by
    change (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      compactWeakProductDerivative m f i) x = _
    rw [MeasureTheory.convolution_eq_swap]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => mul_comm _ _
  exact hleft.trans (hweak.symm.trans hright.symm)

/-- 一般区域弱系数乘内部测试函数，实际属于 H₀¹ 图闭包。
同一批内部紧支光滑卷积同时逼近函数及两个真实偏导，不输入逼近序列。
这是从测试图推广到任意 H₀¹ 的核心密度步骤。 -/
theorem weakCoefficientMul_test_mem_zeroBoundaryGraph (D : Rect)
    (m : RegionalWeakCoefficient D) (f : TestFunction D) :
    weakCoefficientMul D m ⟨smoothToWeakH1 D f.field, test_mem_zeroBoundaryGraph D f⟩
      ∈ zeroBoundaryGraph D := by
  obtain ⟨δ, hδ, hinside⟩ := compactWeakProduct_mollified_inside m f
  let ρ := shrinkingMollifier δ hδ
  have hρ := shrinkingMollifier_properties δ hδ
  let F : ℕ → SmoothField := fun n => mollifiedField (ρ n) (compactWeakProduct m f)
    (compactWeakProduct_integrable m f).locallyIntegrable
  let tests : ℕ → TestFunction D := fun n =>
    ⟨F n, (hinside (ρ n) (hρ.2.1 n)).1, (hinside (ρ n) (hρ.2.1 n)).2⟩
  let u : zeroBoundaryGraph D := ⟨smoothToWeakH1 D f.field, test_mem_zeroBoundaryGraph D f⟩
  have hvalue := compactWeakProduct_mollified_value_tendsto m f ρ hρ.1
    (Eventually.of_forall hρ.2.2)
  have hpartial (i : Fin 2) :
      Tendsto (fun n => SmoothField.toL2 D (smoothPartial i (F n))) atTop
        (𝓝 ((m.derivative i).operator (SmoothField.toL2 D f.field) +
          m.value.operator (SmoothField.toL2 D (smoothPartial i f.field)))) := by
    obtain ⟨C, hC, hbound⟩ := compactWeakProductDerivative_bounded m f i
    have hconv := mollifiedField_toL2_tendsto D ρ hρ.1 (Eventually.of_forall hρ.2.2)
      (compactWeakProductDerivative m f i) (compactWeakProductDerivative_integrable m f i).locallyIntegrable
      _ (compactWeakProductDerivative_ae m f i) hC hbound
    apply hconv.congr'
    apply Eventually.of_forall
    intro n
    apply congrArg (SmoothField.toL2 D)
    apply Subtype.ext
    funext x
    exact (compactWeakProduct_mollified_partial m f (ρ n) i x).symm
  have hgraph : Tendsto (fun n => smoothToWeakH1 D (tests n).field) atTop
      (𝓝 (weakCoefficientMul D m u)) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact hvalue
    · exact hpartial 0
    · exact hpartial 1
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hgraph
    (Eventually.of_forall fun n => test_mem_zeroBoundaryGraph D (tests n))

/-- 区域 W¹,∞ 系数乘任意 H₀¹ 元素仍属于同一个真实 H₀¹ 图闭包。
先以同核卷积证明测试图的乘积属于闭包，再用乘积图的连续线性性推广。
输入只有真实弱系数及原 H₀¹ 元素；没有目标闭包成员或逼近序列字段。 -/
theorem weakCoefficientMul_mem_zeroBoundaryGraph (D : Rect)
    (m : RegionalWeakCoefficient D) (u : zeroBoundaryGraph D) :
    weakCoefficientMul D m u ∈ zeroBoundaryGraph D := by
  let ambientZero : Submodule ℝ (Fin 3 → ScalarL2 D.measure) :=
    (zeroBoundaryGraph D).map (weakH1Graph D).subtype
  let target : Submodule ℝ (weakH1Graph D) :=
    ambientZero.comap (weakCoefficientGraphMap D m).toLinearMap
  have hzeroClosed : IsClosed (zeroBoundaryGraph D : Set (weakH1Graph D)) :=
    Submodule.isClosed_topologicalClosure _
  have hambientClosed : IsClosed (ambientZero : Set (Fin 3 → ScalarL2 D.measure)) := by
    change IsClosed (Subtype.val '' (zeroBoundaryGraph D : Set (weakH1Graph D)))
    exact (weakH1Graph_isClosed D).isClosedEmbedding_subtypeVal.isClosedMap _ hzeroClosed
  have htargetClosed : IsClosed (target : Set (weakH1Graph D)) :=
    hambientClosed.preimage (weakCoefficientGraphMap D m).continuous
  have hspan : Submodule.span ℝ (Set.range (fun f : TestFunction D =>
      smoothToWeakH1 D f.field)) ≤ target := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact ⟨weakCoefficientMul D m ⟨smoothToWeakH1 D f.field, test_mem_zeroBoundaryGraph D f⟩,
      weakCoefficientMul_test_mem_zeroBoundaryGraph D m f, rfl⟩
  have hclosed := Submodule.topologicalClosure_minimal _ hspan htargetClosed u.property
  obtain ⟨v, hv, hvalue⟩ := hclosed
  have hidentify : weakCoefficientMul D m u = v := by
    apply Subtype.ext
    exact hvalue.symm
  rw [hidentify]
  exact hv

/-- 由已证闭包保持构造真正 H₀¹→H₀¹ 的有界线性乘子。
它可用于后续兼容空间，普通 L² 上仍不把梯度视为有界算子。 -/
def weakZeroCoefficientMulCLM (D : Rect) (m : RegionalWeakCoefficient D) :
    zeroBoundaryGraph D →L[ℝ] zeroBoundaryGraph D :=
  (weakCoefficientMulCLM D m).codRestrict (zeroBoundaryGraph D)
    (fun u => weakCoefficientMul_mem_zeroBoundaryGraph D m u)

/-- 非零实际调用：矩形多项式泡函数原本不是域内紧支函数，
先由一般光滑零迹桥接进入 H₀¹，再调用本文件的 H₀¹ 乘子构造。
常数 1 只使非零性核验简洁；一般定理仍允许真正粗糙的区域弱系数。 -/
theorem weakZeroCoefficientMul_nonzero (D : Rect) :
    (weakZeroCoefficientMulCLM D (weakCoefficientOfSmooth D weakCoefficientOne)
      ⟨smoothToWeakH1 D (rectangleBubble D), (rectangleBubble_weakH01 D).1⟩).val.val 0 ≠ 0 := by
  change (weakCoefficientMul D (weakCoefficientOfSmooth D weakCoefficientOne)
    ⟨smoothToWeakH1 D (rectangleBubble D), (rectangleBubble_weakH01 D).1⟩).val 0 ≠ 0
  rw [weakCoefficient_one_value]
  exact (rectangleBubble_weakH01 D).2

end LeanPML.PML
