import LeanPML.Rectangle.WeakSpaces
import LeanPML.PML.BalanceInterfaces

/-!
# v1.0.2：H₀¹ × H(div) 的弱 Green

对应 V7 (7.5) 的零迹版本。标量空间仍是 v1.0.1 的紧支光滑图闭包，
通量仍是内部测试定义的弱散度图。证明先对测试函数成立，再经线性张成及
图范数闭包推广；不输入一般 Green，不要求通量法向为零。
本文件不构造非零迹的法向配对，也不证明所有旧光滑零迹场属于该闭包。
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace Topology
open LeanPML.Analysis
namespace LeanPML.Rectangle

/-- 由 (7.5) 引出的测试配对，原文未单列。三个内积均为真实 L² 内积。
固定通量后，它是 H¹ 图上的线性泛函；后面证明其在 H₀¹ 上为零。 -/
def weakGreenFunctional (D : Rect) (L : weakHDivGraph D) : weakH1Graph D →ₗ[ℝ] ℝ where
  toFun U := ⟪U.val 1, L.val 0⟫_ℝ + ⟪U.val 2, L.val 1⟫_ℝ + ⟪U.val 0, L.val 2⟫_ℝ
  map_add' U V := by simp only [Submodule.coe_add, Pi.add_apply, inner_add_left]; ring
  map_smul' c U := by simp only [Submodule.coe_smul, Pi.smul_apply, real_inner_smul_left, smul_eq_mul, RingHom.id_apply]; ring

/-- 配对在图范数中连续：同时控制函数和两个弱偏导，而非仅控制函数 L²。 -/
theorem weakGreenFunctional_continuous (D : Rect) (L : weakHDivGraph D) :
    Continuous (weakGreenFunctional D L) := by
  have hcoordinate (i : Fin 3) : Continuous (fun U : weakH1Graph D => U.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  have hx : Continuous (fun U : weakH1Graph D => ⟪U.val 1, L.val 0⟫_ℝ) :=
    (hcoordinate 1).inner continuous_const
  have hy : Continuous (fun U : weakH1Graph D => ⟪U.val 2, L.val 1⟫_ℝ) :=
    (hcoordinate 2).inner continuous_const
  have hdiv : Continuous (fun U : weakH1Graph D => ⟪U.val 0, L.val 2⟫_ℝ) :=
    (hcoordinate 0).inner continuous_const
  exact (hx.add hy).add hdiv

/-- V7 (7.5) 的弱零迹式：任意 H₀¹ 标量和 H(div) 通量满足
⟨∂xv,Λx⟩+⟨∂yv,Λy⟩=−⟨v,divΛ⟩。不限制通量边界值。
输入仅为真实图空间成员；闭包推广使用连续线性泛函的闭核。 -/
theorem weak_green (D : Rect) (v : zeroBoundaryGraph D) (L : weakHDivGraph D) :
    ⟪v.val.val 1, L.val 0⟫_ℝ + ⟪v.val.val 2, L.val 1⟫_ℝ =
      -⟪v.val.val 0, L.val 2⟫_ℝ := by
  have htest : ∀ φ : TestFunction D,
      smoothToWeakH1 D φ.field ∈ (weakGreenFunctional D L).ker := by
    intro φ
    have hdiv := L.property φ
    change ⟪SmoothField.toL2 D φ.field.derivativeX, L.val 0⟫_ℝ +
      ⟪SmoothField.toL2 D φ.field.derivativeY, L.val 1⟫_ℝ +
      ⟪SmoothField.toL2 D φ.field, L.val 2⟫_ℝ = 0
    simp only [real_inner_comm] at hdiv ⊢
    linarith
  have hspan : Submodule.span ℝ (Set.range (fun φ : TestFunction D =>
      smoothToWeakH1 D φ.field)) ≤ (weakGreenFunctional D L).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨φ, rfl⟩
    exact htest φ
  have hclosed : IsClosed ((weakGreenFunctional D L).ker : Set (weakH1Graph D)) :=
    isClosed_eq (weakGreenFunctional_continuous D L) continuous_const
  have hzero := (Submodule.topologicalClosure_minimal _ hspan hclosed) v.property
  change ⟪v.val.val 1, L.val 0⟫_ℝ + ⟪v.val.val 2, L.val 1⟫_ℝ +
    ⟪v.val.val 0, L.val 2⟫_ℝ = 0 at hzero
  linarith

/-- H₀¹ 的 L² 像成员回到其完整图；相同函数的弱偏导唯一，故选择无关。
用于连接旧的受限 L² 算子接口，不从 L² 商类读取边界点。 -/
def weakZeroLift (D : Rect) (v : weakZeroFieldDomain D) : zeroBoundaryGraph D :=
  ⟨weakLift D (Submodule.inclusion (weakZeroFieldDomain_le D) v), by
    rcases v.property with ⟨U, hU⟩
    have heq : weakLift D (Submodule.inclusion (weakZeroFieldDomain_le D) v) = U.val := by
      apply weakValue_injective D
      exact (congrArg Subtype.val
        ((LinearEquiv.ofInjective (weakValue D) (weakValue_injective D)).apply_symm_apply
          (Submodule.inclusion (weakZeroFieldDomain_le D) v))).trans hU.symm
    rw [heq]
    exact U.property⟩

/-- 回到普通 L² 后确为输入函数，保证桥接没有更换状态。 -/
theorem weakZeroLift_value (D : Rect) (v : weakZeroFieldDomain D) :
    (weakZeroLift D v).val.val 0 = v.val := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective (weakValue D) (weakValue_injective D)).apply_symm_apply
      (Submodule.inclusion (weakZeroFieldDomain_le D) v))

/-- 将图空间弱 Green 接到现有实际 L² 的受限定义域；
两个分量是 weakZeroSpatialDomain 的真实弱偏导，通量使用 weakDivergence。 -/
theorem weak_green_domain (D : Rect) (v : weakZeroFieldDomain D)
    (L : weakFluxDomain D) :
    ⟪v.val, weakDivergence D L⟫_ℝ =
      -⟪(weakZeroSpatialDomain D).componentX v, L.val.1⟫_ℝ -
      ⟪(weakZeroSpatialDomain D).componentY v, L.val.2⟫_ℝ := by
  let F : weakHDivGraph D :=
    ⟨![L.val.1, L.val.2, weakDivergence D L], weakDivergence_spec D L⟩
  have hgreen := weak_green D (weakZeroLift D v) F
  have hvalue := weakZeroLift_value D v
  change ⟪(weakZeroSpatialDomain D).componentX v, L.val.1⟫_ℝ +
    ⟪(weakZeroSpatialDomain D).componentY v, L.val.2⟫_ℝ =
    -⟪(weakZeroLift D v).val.val 0, weakDivergence D L⟫_ℝ at hgreen
  rw [hvalue] at hgreen
  linarith

/-- 已证明的弱零迹 Green 接口。标量定义域已经限制为 H₀¹，
故边界数据取零线性映射；这是零迹域上的受限接口，不冒称一般弱迹理论。
通量域为全部已定义 H(div)，没有增加 Λ·n=0。green 字段由上一条定理填入。 -/
def weakGreenDomain (D : Rect) : LeanPML.PML.ConditionalGreenDomain D.measure ℝ where
  spatial := weakZeroSpatialDomain D
  fluxDomain := weakFluxDomain D
  divergence := weakDivergence D
  trace := 0
  boundary := 0
  green v L := by simpa using weak_green_domain D v L

end LeanPML.Rectangle
