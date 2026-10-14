import LeanPML.Rectangle.WeakGreen
import LeanPML.Rectangle.Poincare

/-!
# v1.0.2：图范数闭包上的保守 Poincaré

由 V7 (5.1) 所需估计引出，但常数沿用已证 C_P=2Lx，不是原式的精确 π 常数。
先将有限线性组合识别为真实光滑零迹函数，再用连续性将平方范数估计推广到
H₀¹ 图闭包。此证明不使用“普通 L² 逼近可以控制梯度”的错误推断。
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace Topology
open LeanPML.Analysis
namespace LeanPML.Rectangle

/-- 光滑图映射线性；三槽分别用函数及两个实际导数的线性性。
服务于有限线性组合的 Poincaré 估计，原文未单列。 -/
def smoothGraphLinear (D : Rect) : SmoothField →ₗ[ℝ] weakH1Graph D where
  toFun := smoothToWeakH1 D
  map_add' f g := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact (SmoothField.toL2 D).map_add f g
    · change SmoothField.toL2 D (SmoothField.derivativeXLinear (f + g)) = _
      simp only [map_add]; rfl
    · change SmoothField.toL2 D (SmoothField.derivativeYLinear (f + g)) = _
      simp only [map_add]; rfl
  map_smul' c f := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact (SmoothField.toL2 D).map_smul c f
    · change SmoothField.toL2 D (SmoothField.derivativeXLinear (c • f)) = _
      simp only [map_smul]; rfl
    · change SmoothField.toL2 D (SmoothField.derivativeYLinear (c • f)) = _
      simp only [map_smul]; rfl

/-- 测试图的有限线性组合仍有光滑零边界代表。
这里不声称任意光滑零迹代表可反向逼近；仅证明闭包生成元张成的性质。 -/
theorem span_test_has_smooth_zeroBoundary (D : Rect) (U : weakH1Graph D)
    (hspan : U ∈ Submodule.span ℝ (Set.range (fun φ : TestFunction D =>
      smoothToWeakH1 D φ.field))) :
    ∃ f : SmoothField, ZeroBoundary D f ∧ smoothToWeakH1 D f = U := by
  induction hspan using Submodule.span_induction with
  | mem U hU =>
    rcases hU with ⟨φ, rfl⟩
    exact ⟨φ.field, φ.zeroBoundary, rfl⟩
  | zero =>
    refine ⟨0, ?_, (smoothGraphLinear D).map_zero⟩
    exact (smoothTrace_eq_zero_iff D 0).mp (map_zero _)
  | add U V hU hV ihU ihV =>
    rcases ihU with ⟨f, hf, rfl⟩
    rcases ihV with ⟨g, hg, rfl⟩
    refine ⟨f + g, ?_, (smoothGraphLinear D).map_add f g⟩
    apply (smoothTrace_eq_zero_iff D _).mp
    rw [map_add, (smoothTrace_eq_zero_iff D f).mpr hf,
      (smoothTrace_eq_zero_iff D g).mpr hg, add_zero]
  | smul c U hU ih =>
    rcases ih with ⟨f, hf, rfl⟩
    refine ⟨c • f, ?_, (smoothGraphLinear D).map_smul c f⟩
    apply (smoothTrace_eq_zero_iff D _).mp
    rw [map_smul, (smoothTrace_eq_zero_iff D f).mpr hf, smul_zero]

/-- 弱 H₀¹ 的 Poincaré：‖v‖²≤(2Lx)²(‖∂xv‖²+‖∂yv‖²)。
输入只有原有闭包成员，估计由已证光滑矩形结果和图范数闭包推出。
与 CP=2Lx 的 K/阈值证书一致；不扩大到原文精确常数的参数范围。 -/
theorem weak_poincare (D : Rect) (v : zeroBoundaryGraph D) :
    ‖v.val.val 0‖ ^ 2 ≤ poincareConstant D ^ 2 *
      (‖v.val.val 1‖ ^ 2 + ‖v.val.val 2‖ ^ 2) := by
  have hspan : (Submodule.span ℝ (Set.range (fun φ : TestFunction D =>
      smoothToWeakH1 D φ.field)) : Set (weakH1Graph D)) ⊆
      {U | ‖U.val 0‖ ^ 2 ≤ poincareConstant D ^ 2 *
        (‖U.val 1‖ ^ 2 + ‖U.val 2‖ ^ 2)} := by
    intro U hU
    rcases span_test_has_smooth_zeroBoundary D U hU with ⟨f, hf, rfl⟩
    change ‖SmoothField.toL2 D f‖ ^ 2 ≤ _ *
      (‖SmoothField.toL2 D f.derivativeX‖ ^ 2 + ‖SmoothField.toL2 D f.derivativeY‖ ^ 2)
    simp only [norm_toL2_sq]
    exact poincare_smooth D f hf
  have hcoord (i : Fin 3) : Continuous (fun U : weakH1Graph D => ‖U.val i‖ ^ 2) :=
    (((continuous_apply i).comp continuous_subtype_val).norm).pow 2
  have hclosed : IsClosed {U : weakH1Graph D | ‖U.val 0‖ ^ 2 ≤
      poincareConstant D ^ 2 * (‖U.val 1‖ ^ 2 + ‖U.val 2‖ ^ 2)} :=
    isClosed_le (hcoord 0) (continuous_const.mul ((hcoord 1).add (hcoord 2)))
  -- 最大值图范数同时控制三个坐标，故上述非严格不等式的解集闭。
  exact closure_minimal hspan hclosed v.property

/-- 弱零边界场的零梯度推出零场；由本文件实际 Poincaré 得到。
仅是后续规范唯一性的最后一步，不把规范约束到零梯度的缺口藏在名字里。 -/
theorem weak_zero_of_gradient_zero (D : Rect) (v : zeroBoundaryGraph D)
    (hx : v.val.val 1 = 0) (hy : v.val.val 2 = 0) : v = 0 := by
  have hestimate := weak_poincare D v
  rw [hx, hy] at hestimate
  have hvalue : v.val.val 0 = 0 := by
    have hnorm : ‖v.val.val 0‖ = 0 := by
      simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, mul_zero] at hestimate
      nlinarith [norm_nonneg (v.val.val 0)]
    exact norm_eq_zero.mp hnorm
  apply Subtype.ext
  apply weakValue_injective D
  exact hvalue

/-- 同一估计在现有受限 L² 梯度域上的形式；由图提升填入，不能另传 estimate。 -/
theorem weak_poincare_domain (D : Rect) (v : weakZeroFieldDomain D) :
    ‖v.val‖ ^ 2 ≤ poincareConstant D ^ 2 *
      (‖(weakZeroSpatialDomain D).componentX v‖ ^ 2 +
        ‖(weakZeroSpatialDomain D).componentY v‖ ^ 2) := by
  have hestimate := weak_poincare D (weakZeroLift D v)
  rw [weakZeroLift_value] at hestimate
  exact hestimate

/-- 为旧能量框架构造真实弱 Poincaré 接口；零迹域与 weakGreenDomain 相同。
空间成员本身已经是 H₀¹，故零迹核是全域。保守常数保持 2Lx。
本构造只填空间字段，不自动提供弱原方程、兼容保持或时间正则性。 -/
def weakPoincareDomain (D : Rect) :
    LeanPML.PML.ConditionalPoincare (weakGreenDomain D).spatial (poincareConstant D) :=
  LeanPML.PML.ConditionalPoincare.ofGreenTrace (weakGreenDomain D) (poincareConstant D)
    (fun v _ => weak_poincare_domain D v)

end LeanPML.Rectangle
