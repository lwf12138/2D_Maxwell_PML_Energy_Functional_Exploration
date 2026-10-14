import LeanPML.Rectangle.Fields
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# v0.5.2：供具体数据使用的光滑紧支函数

由 V7 §5.2 的光滑紧支初值要求引入，原文未单列此构造。
`basicBump center radius x = expNegInvGlue(radius²-(x-center)²)`：
括号非正时为零，正时严格为正。mathlib 已证明 glue 是 C∞，
所以两端拼接光滑；不能把分段多项式默认当作 C∞。
本文件给一维支撑与真实求导，二维初值在 FullDomainProfile 中组装。
-/
noncomputable section
open Set Function
open scoped ContDiff
namespace LeanPML.Examples.SmoothBump

/-- 实際一维 bump。center/radius 是几何参数，不是吸收系数；
支撑和非零性定理明确要求 radius>0。 -/
def basicBump (center radius x : ℝ) : ℝ :=
  expNegInvGlue (radius^2-(x-center)^2)

/-- C∞ 来自 mathlib 的 expNegInvGlue.contDiff 与多项式复合。 -/
theorem basicBump_contDiff (center radius : ℝ) : ContDiff ℝ ∞ (basicBump center radius) := by
  exact expNegInvGlue.contDiff.comp
    (contDiff_const.sub ((contDiff_id.sub contDiff_const).pow 2))

/-- bump 处处非负，不需要正半径假设。 -/
theorem basicBump_nonneg (center radius x : ℝ) : 0≤basicBump center radius x :=
  expNegInvGlue.nonneg _

/-- 半径为正时，bump 恰在开区间 (center-radius,center+radius) 严格为正。
平方比较与线性端点比较在这里接通，供后续支撑定位使用。 -/
theorem basicBump_pos_iff (center radius x : ℝ) (hradius : 0<radius) :
    0<basicBump center radius x ↔ x∈Ioo (center-radius) (center+radius) := by
  have hinner : 0<radius^2-(x-center)^2 ↔ x∈Ioo (center-radius) (center+radius) := by
    constructor
    · intro hpos
      have hsquare : (x-center)^2 < radius^2 := by linarith
      have habs : |x-center|<radius := (sq_lt_sq₀ (abs_nonneg _) hradius.le).mp
        (by simpa only [sq_abs] using hsquare)
      have hboth := abs_lt.mp habs
      constructor <;> linarith
    · intro hx
      have hleft : 0<radius-(x-center) := by linarith [hx.2]
      have hright : 0<radius+(x-center) := by linarith [hx.1]
      nlinarith only [mul_pos hleft hright]
  constructor
  · intro hpos
    apply hinner.mp
    by_contra hnot
    have hzero : basicBump center radius x=0 :=
      expNegInvGlue.zero_of_nonpos (le_of_not_gt hnot)
    exact (ne_of_gt hpos) hzero
  · intro hx
    exact expNegInvGlue.pos_of_pos (hinner.mpr hx)

/-- 中心非零，避免仅构造零函数满足支撑条件。 -/
theorem basicBump_center_pos (center radius : ℝ) (hradius : 0<radius) :
    0<basicBump center radius center :=
  (basicBump_pos_iff center radius center hradius).mpr ⟨by linarith,by linarith⟩

/-- 普通支撑是开区间；拓扑支撑随后取其闭包。 -/
theorem basicBump_support (center radius : ℝ) (hradius : 0<radius) :
    support (basicBump center radius)=Ioo (center-radius) (center+radius) := by
  ext x
  change basicBump center radius x≠0 ↔ _
  rw [← basicBump_pos_iff center radius x hradius]
  exact ⟨fun hne => lt_of_le_of_ne (basicBump_nonneg center radius x) (Ne.symm hne),
    ne_of_gt⟩

/-- 实际拓扑支撑等于闭区间；后续导数支撑也受同一闭区间控制。 -/
theorem basicBump_tsupport (center radius : ℝ) (hradius : 0<radius) :
    tsupport (basicBump center radius)=Icc (center-radius) (center+radius) := by
  rw [tsupport,basicBump_support center radius hradius]
  exact closure_Ioo (by linarith)

/-- 一维 bump 真正具有紧支撑，不是把任意函数称作紧支。 -/
theorem basicBump_hasCompactSupport (center radius : ℝ) (hradius : 0<radius) :
    HasCompactSupport (basicBump center radius) := by
  change IsCompact (tsupport (basicBump center radius))
  rw [basicBump_tsupport center radius hradius]
  exact isCompact_Icc

/-- 一维实际求导。导数值由 glue 的 mathlib 导数与内层多项式链式法则组成；
也覆盖支撑端点，那里 glue=0，使导数同样为零。 -/
theorem basicBump_hasDerivAt (center radius x : ℝ) :
    HasDerivAt (basicBump center radius)
      (((radius^2-(x-center)^2)⁻¹)^2 * basicBump center radius x * (-2*(x-center))) x := by
  have hglue : HasDerivAt expNegInvGlue
      (((radius^2-(x-center)^2)⁻¹)^2 * expNegInvGlue (radius^2-(x-center)^2))
      (radius^2-(x-center)^2) := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ)
      (radius^2-(x-center)^2)
  have hinner : HasDerivAt (fun y : ℝ => radius^2-(y-center)^2) (-2*(x-center)) x := by
    exact ((hasDerivAt_const x (radius^2)).sub
      (((hasDerivAt_id x).sub_const center).pow 2)).congr_deriv (by simp only [id_eq]; ring)
  exact hglue.comp x hinner

/-- 导数也不越出原闭支撑。这是 mathlib 的一般导数支撑事实的具体调用。 -/
theorem basicBump_deriv_tsupport_subset (center radius : ℝ) (hradius : 0<radius) :
    tsupport (deriv (basicBump center radius)) ⊆ Icc (center-radius) (center+radius) := by
  rw [← basicBump_tsupport center radius hradius]
  exact tsupport_deriv_subset

end LeanPML.Examples.SmoothBump
