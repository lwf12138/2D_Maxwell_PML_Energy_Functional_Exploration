import LeanPML.Rectangle.WeakSpaces
import LeanPML.Analysis.WeightedL2Operators
import LeanPML.Examples.CompatibleData

/-!
# v1.0.1：新空间的实际调用

复用 v0.5 已证的非零物理区 bump，不重新假设光滑性、紧支或非零性。
它进入弱 H₀¹ 闭包；两个方向的真实弱导数与旧 toL2 对应。
随后在一般 SpatialAbsorption 上调用加权像刻画与有界系数乘法，
范围包含全零、单向、双向吸收，不对无界能量权重求上界。
这些是空间成员证书，不是新的弱 PDE 解或能量定理。
-/
noncomputable section
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
namespace LeanPML.Examples.WeakSpaces

/-- 旧非零二维 bump 的支撑严格落在整个计算矩形内部。 -/
def physicalTest : TestFunction unitSquare where
  field := FullDomain.physicalBump
  compact := FullDomain.physicalBump_hasCompactSupport
  support_inside := by
    intro x hx
    have hbox := FullDomain.physicalBump_tsupport_subset hx
    change (-1 < x.1 ∧ x.1 < 1) ∧ (-1 < x.2 ∧ x.2 < 1)
    rcases hbox with ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
    constructor <;> constructor <;> linarith

/-- 非零场确实属于新 H₀¹ 闭包，并在原 L² 中非零。
它检验测试空间不只是零空间；不声称本轮已证明所有光滑零迹函数的密度。 -/
theorem physicalTest_nonzero_member :
    smoothToWeakH1 unitSquare physicalTest.field ∈ zeroBoundaryGraph unitSquare ∧
    SmoothField.toL2 unitSquare physicalTest.field ≠ 0 :=
  ⟨test_mem_zeroBoundaryGraph unitSquare physicalTest,
    LeanPML.Examples.CompatibleData.physicalBump_L2_ne_zero⟩

/-- 在同一实际矩形上，新梯度与旧 bump 的两条真实偏导相同。 -/
theorem physicalTest_gradient_bridge :
    HasWeakPartial unitSquare 0 (SmoothField.toL2 unitSquare physicalTest.field)
      (SmoothField.toL2 unitSquare physicalTest.field.derivativeX) ∧
    HasWeakPartial unitSquare 1 (SmoothField.toL2 unitSquare physicalTest.field)
      (SmoothField.toL2 unitSquare physicalTest.field.derivativeY) :=
  ⟨hasWeakPartial_smooth unitSquare 0 physicalTest.field,
    hasWeakPartial_smooth unitSquare 1 physicalTest.field⟩

/-- 由 V7 (5.5)–(5.6) 的原吸收条件得到加权像的准确刻画。
不额外要求吸收正下界；wx=0 的区域仍显式要求物理场为零。 -/
theorem absorption_weighted_range {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (C : LeanPML.PML.SpatialAbsorption α) (f : ScalarL2 ν) :
    (∃ X : WeightedL2 ν C.wx,
      physicalL2 ν C.wx C.wx_measurable C.wx_gap X = f) ↔
    MemLp (fun x => Real.sqrt (C.wx x) * f x) 2 ν ∧
    (∀ᵐ x ∂ν, C.a x = 0 → f x = 0) := by
  rw [physicalL2_range_iff]
  simp only [C.wx_eq_zero_iff]

/-- 有界吸收 p 在加权空间中的实际作用与普通物理乘法相容。
界取 C.S（已由原假设构造 pCoeff），不是能量权重的上界。 -/
theorem absorption_weighted_multiplication {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (C : LeanPML.PML.SpatialAbsorption α) (X : WeightedL2 ν C.wx) :
    physicalL2 ν C.wx C.wx_measurable C.wx_gap
      (weightedMul ν C.wx C.pCoeff.value C.pCoeff.measurable
        C.pCoeff.bound C.pCoeff.abs_le X) =
      C.pCoeff.operator ν (physicalL2 ν C.wx C.wx_measurable C.wx_gap X) :=
  physicalL2_weightedMul ν C.wx C.pCoeff.value C.wx_measurable C.wx_gap
    C.pCoeff.measurable C.pCoeff.bound C.pCoeff.abs_le X

end LeanPML.Examples.WeakSpaces
