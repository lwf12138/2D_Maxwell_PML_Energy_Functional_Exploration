import LeanPML.PML.SpatialCoefficients
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# v0.4.1：整个非退化矩形及实际积分

对应 V7 §1、(5.1)、(7.5)。`Rect` 保存四个端点及严格边长；
`measure` 复用旧工程的整个开矩形 Lebesgue 测度。
闭矩形只用于光滑延拓和边界取值，下面证明其限制测度与开矩形一致。
先读 `measure_eq_closed`、`integral_fubini`，再读 Fields 中的实际 L² 表示。
本文件不包含 PDE、弱迹或能量结论。
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LeanPML.Rectangle

/-- V7 §1 的实际非退化矩形。严格端点条件保证两条边长为正。 -/
structure Rect where
  xlo : ℝ
  xhi : ℝ
  ylo : ℝ
  yhi : ℝ
  x_lt : xlo < xhi
  y_lt : ylo < yhi

namespace Rect
/-- 整个开计算域，不缩小为零吸收物理区。 -/
def openSet (D : Rect) : Set (ℝ × ℝ) :=
  LeanPML.PML.rectangleDomain D.xlo D.xhi D.ylo D.yhi
/-- 光滑代表的闭矩形取值域，包括四条外边。 -/
def closedSet (D : Rect) : Set (ℝ × ℝ) := Icc D.xlo D.xhi ×ˢ Icc D.ylo D.yhi
/-- 复用原有二维 Lebesgue 限制测度；与材料常数 μ 区分。 -/
def measure (D : Rect) : Measure (ℝ × ℝ) :=
  LeanPML.PML.rectangleMeasure D.xlo D.xhi D.ylo D.yhi
/-- x 方向边长。 -/
def Lx (D : Rect) : ℝ := D.xhi - D.xlo
/-- y 方向边长。 -/
def Ly (D : Rect) : ℝ := D.yhi - D.ylo

theorem Lx_pos (D : Rect) : 0 < D.Lx := sub_pos.mpr D.x_lt
theorem Ly_pos (D : Rect) : 0 < D.Ly := sub_pos.mpr D.y_lt
theorem openSet_open (D : Rect) : IsOpen D.openSet := isOpen_Ioo.prod isOpen_Ioo
theorem closedSet_compact (D : Rect) : IsCompact D.closedSet := isCompact_Icc.prod isCompact_Icc

theorem closedSet_eq_Icc (D : Rect) :
    D.closedSet = Icc (D.xlo, D.ylo) (D.xhi, D.yhi) := by
  simp only [closedSet, Icc_prod_eq]

theorem closure_openSet (D : Rect) : closure D.openSet = D.closedSet := by
  simp only [openSet, LeanPML.PML.rectangleDomain, closure_prod_eq,
    closure_Ioo D.x_lt.ne, closure_Ioo D.y_lt.ne, closedSet]

/-- 由矩形几何推出，原文未单列：四边为零测集，所以开/闭矩形限制测度相同。
后面的 Green 使用闭矩形光滑代表，但积分仍是原来的整个 Ω 积分。 -/
theorem measure_eq_closed (D : Rect) : D.measure = volume.restrict D.closedSet := by
  change volume.restrict (Ioo D.xlo D.xhi ×ˢ Ioo D.ylo D.yhi) = _
  rw [Measure.volume_eq_prod]
  exact Measure.restrict_congr_set
    (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

/-- 二维测度确为两条开区间限制测度的乘积，供 Fubini 使用。 -/
theorem measure_eq_prod (D : Rect) : D.measure =
    (volume.restrict (Ioo D.xlo D.xhi)).prod (volume.restrict (Ioo D.ylo D.yhi)) := by
  change volume.restrict (Ioo D.xlo D.xhi ×ˢ Ioo D.ylo D.yhi) = _
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

instance (D : Rect) : IsFiniteMeasure D.measure := by
  rw [D.measure_eq_closed]
  exact ⟨by simpa using D.closedSet_compact.measure_lt_top⟩

/-- 真实 Fubini 对应：先明确可积，再把二维空间积分写为两次一维积分。
不是把迭代积分另定义为原体积分。 -/
theorem integral_fubini (D : Rect) (f : ℝ × ℝ → ℝ) (hf : Integrable f D.measure) :
    (∫ z, f z ∂D.measure) =
      ∫ x in Ioo D.xlo D.xhi, ∫ y in Ioo D.ylo D.yhi, f (x,y) := by
  rw [D.measure_eq_prod] at hf ⊢
  exact integral_prod f hf

/-- 由紧致闭矩形及连续性推出 Lᵖ 成员；用于实际场及所有光滑导数。
上界仅用于证明积分有限，不是吸收系数的正下界。 -/
theorem memLp_of_continuous (D : Rect) {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p D.measure := by
  obtain ⟨B, hB⟩ := (D.closedSet_compact.image hf).isBounded.exists_norm_le
  apply MemLp.of_bound hf.aestronglyMeasurable B
  rw [D.measure_eq_closed]
  filter_upwards [ae_restrict_mem D.closedSet_compact.measurableSet] with z hz
  exact hB (f z) (mem_image_of_mem f hz)

/-- 连续密度在矩形可积。后续 Green 的乘积/导数密度均由此核验。 -/
theorem integrable_of_continuous (D : Rect) {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) : Integrable f D.measure :=
  memLp_one_iff_integrable.mp (D.memLp_of_continuous hf 1)

end Rect
end LeanPML.Rectangle
