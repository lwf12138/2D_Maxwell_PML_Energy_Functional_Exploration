import LeanPML.Rectangle.WeakPoincare

/-!
# 弱偏导在开子域上的局部性

V7 §5.3 的规范论证需要从 g 在吸收区为零推出该区弱梯度为零。
当吸收系数有连续代表时，Ω₊ 是开集；可直接用分布测试局部性，
无需在此先建设任意可测零水平集的 Sobolev 链式法则。
本文件只证明实际弱导数的局部性，不假设提升唯一性。
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace Topology ContDiff
open LeanPML.Analysis
namespace LeanPML.Rectangle

/-- 紧支于开子域 S 的测试函数在 S 外的两个真实偏导为零。
由拓扑支撑外邻域恒零推出 fderiv=0，不从单点零值直接求导。 -/
theorem smoothPartial_zero_outside_support_set (i : Fin 2) (φ : SmoothField)
    {S : Set (ℝ × ℝ)} (hsupport : tsupport (⇑φ) ⊆ S)
    {x : ℝ × ℝ} (hx : x ∉ S) : smoothPartial i φ x = 0 := by
  have hnotSupport : x ∉ tsupport (⇑φ) := fun hmem => hx (hsupport hmem)
  have hderiv : fderiv ℝ (⇑φ) x = 0 := fderiv_of_notMem_tsupport ℝ hnotSupport
  fin_cases i <;> simp [smoothPartial, SmoothField.derivativeX_apply,
    SmoothField.derivativeY_apply, dx, dy, hderiv]

/-- 若 f 的真实弱偏导为 g，且 f 在开子域 S 上 a.e. 为零，则 g 在 S 上 a.e. 为零。
测试函数支撑于 S；弱导数关系把 g 的配对转成 f 的配对，后者由域内 f=0、
域外测试偏导=0 消失。最后调用 mathlib 分布基本引理，结论仍是 a.e.。 -/
theorem HasWeakPartial.zero_on_open {D : Rect} {i : Fin 2}
    {f g : ScalarL2 D.measure} (hpartial : HasWeakPartial D i f g)
    {S : Set (ℝ × ℝ)} (hS_open : IsOpen S) (hS_inside : S ⊆ D.openSet)
    (hf_zero : ∀ᵐ x ∂D.measure, x ∈ S → f x = 0) :
    ∀ᵐ x ∂D.measure, x ∈ S → g x = 0 := by
  have hg_integrable : Integrable (⇑g) D.measure :=
    (Lp.memLp g).integrable (by norm_num)
  apply hS_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hg_integrable.locallyIntegrable.locallyIntegrableOn S)
  intro test htest_smooth htest_compact htest_support
  let φ : TestFunction D :=
    ⟨⟨test, htest_smooth⟩, htest_compact, htest_support.trans hS_inside⟩
  have hpair_zero : ⟪f, SmoothField.toL2 D (smoothPartial i φ.field)⟫_ℝ = 0 := by
    rw [inner_eq_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [hf_zero, SmoothField.coe_toL2 D (smoothPartial i φ.field)]
      with x hzero htest
    change f x * _ = 0
    rw [htest]
    by_cases hx : x ∈ S
    · rw [hzero hx, zero_mul]
    · rw [smoothPartial_zero_outside_support_set i φ.field htest_support hx, mul_zero]
  have hweak : ⟪g, SmoothField.toL2 D φ.field⟫_ℝ = 0 := by
    rw [hpartial φ, hpair_zero, neg_zero]
  rw [inner_eq_integral] at hweak
  calc
    (∫ x, test x • g x ∂D.measure) =
        ∫ x, g x * (SmoothField.toL2 D φ.field) x ∂D.measure := by
      apply integral_congr_ae
      filter_upwards [SmoothField.coe_toL2 D φ.field] with x hx
      simp only [hx, smul_eq_mul]
      exact mul_comm _ _
    _ = 0 := hweak

/-- H¹ 图的两个弱偏导在开子域上的局部性，供吸收区 Ω₊ 使用。
这里没有假设其中任何偏导已为零，只有函数本身在该区为零。 -/
theorem weakGradient_zero_on_open (D : Rect) (g : weakH1Graph D)
    {S : Set (ℝ × ℝ)} (hS_open : IsOpen S) (hS_inside : S ⊆ D.openSet)
    (hg_zero : ∀ᵐ x ∂D.measure, x ∈ S → g.val 0 x = 0) :
    (∀ᵐ x ∂D.measure, x ∈ S → g.val 1 x = 0) ∧
    (∀ᵐ x ∂D.measure, x ∈ S → g.val 2 x = 0) :=
  ⟨g.property.1.zero_on_open hS_open hS_inside hg_zero,
    g.property.2.zero_on_open hS_open hS_inside hg_zero⟩

/-- 规范论证的最后拼合：g 在开集 S 上为零、在其余域内梯度为零 ⇒ g=0。
S 可取 Ω₊；尚须上游从分离系数约束证明 g=0 于 Ω₊，本定理不替代那一步。 -/
theorem weak_zero_of_open_value_and_complement_gradient (D : Rect)
    (g : zeroBoundaryGraph D) {S : Set (ℝ × ℝ)}
    (hS_open : IsOpen S) (hS_inside : S ⊆ D.openSet)
    (hg_zero : ∀ᵐ x ∂D.measure, x ∈ S → g.val.val 0 x = 0)
    (hcomplement : ∀ᵐ x ∂D.measure, x ∉ S →
      g.val.val 1 x = 0 ∧ g.val.val 2 x = 0) : g = 0 := by
  have hlocal := weakGradient_zero_on_open D g.val hS_open hS_inside hg_zero
  have hgradX : g.val.val 1 = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hlocal.1, hcomplement] with x hinside houtside
    by_cases hx : x ∈ S
    · exact hinside hx
    · exact (houtside hx).1
  have hgradY : g.val.val 2 = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hlocal.2, hcomplement] with x hinside houtside
    by_cases hx : x ∈ S
    · exact hinside hx
    · exact (houtside hx).2
  exact weak_zero_of_gradient_zero D g hgradX hgradY

end LeanPML.Rectangle
