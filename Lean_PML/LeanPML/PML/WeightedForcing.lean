import LeanPML.Analysis.WeightedL2Operators
import LeanPML.PML.SpatialCoefficients
import LeanPML.Rectangle.WeakPaths
import LeanPML.PML.Coercivity
import LeanPML.PML.BalanceBlocks
import Mathlib.Tactic.Positivity

/-!
# (5.8) 所需的真实加权强迫算子

V7 §5.2：(5.7) 的强迫是 (σⱼ−σᵢ)∂ᵢu；(5.8) 后的未编号式
估计 φᵢ,t=σⱼ∂ᵢu−σᵢΛᵢ。本文件先证明系数平方界，再把普通 L²
输入送入实际 WeightedL2，最后证明加权范数估计及物理恢复。
这里没有假设输入梯度本来属于加权空间，也没有把无界 w 当作有界乘子。

这补的是传播证明的空间部分。尚不能仅由此声称时间卷积公式已经在加权
空间中建立，或 φ 的 C¹/C² 加权正则性自动传播。
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace LeanPML.Analysis
variable {α : Type*} [MeasurableSpace α]

/-- 由 V7 (5.8) 前后的系数界推出，原文未单列。
若 w m²≤B，则 √w m 是有界乘子；不要求 w 本身有界。
平方根消去只使用 w、B 非负，供 weightedForcing 构造使用。 -/
theorem sqrt_weight_mul_abs_le (w m B : ℝ) (hw_nonneg : 0 ≤ w)
    (hB_nonneg : 0 ≤ B) (hbound : w * m ^ 2 ≤ B) :
    |Real.sqrt w * m| ≤ Real.sqrt B := by
  have hsqrt_w : (Real.sqrt w) ^ 2 = w := Real.sq_sqrt hw_nonneg
  have hsqrt_B : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB_nonneg
  have hproduct : (Real.sqrt w * m) ^ 2 ≤ B := by nlinarith
  have habs_sq : |Real.sqrt w * m| ^ 2 = (Real.sqrt w * m) ^ 2 := sq_abs _
  nlinarith [Real.sqrt_nonneg B, abs_nonneg (Real.sqrt w * m)]

/-- 由 (5.8) 所需的乘法估计构造真实空间映射 g↦m g。
输出保存平方根坐标 √w m g；在 w=0 区坐标自动为零。
输入 B 是已证系数界，不是加权成员资格；后面由原吸收条件给出 B。 -/
def weightedForcing (ν : Measure α) (w m : α → ℝ)
    (hw : Measurable w) (hm : Measurable m)
    (hw_nonneg : ∀ x, 0 ≤ w x) (B : ℝ) (hB_nonneg : 0 ≤ B)
    (hbound : ∀ x, w x * m x ^ 2 ≤ B) :
    ScalarL2 ν →L[ℝ] WeightedL2 ν w :=
  (boundedMul ν (fun x => Real.sqrt (w x) * m x) (hw.sqrt.mul hm)
    (Real.sqrt B) (fun x => sqrt_weight_mul_abs_le _ _ _ (hw_nonneg x)
      hB_nonneg (hbound x))).codRestrict (weightedSubspace ν w) (by
        intro g
        filter_upwards [coeFn_boundedMul ν (fun x => Real.sqrt (w x) * m x)
          (hw.sqrt.mul hm) (Real.sqrt B)
          (fun x => sqrt_weight_mul_abs_le _ _ _ (hw_nonneg x) hB_nonneg (hbound x)) g]
          with x hvalue
        intro hzero
        simp only [hvalue, hzero, Real.sqrt_zero, zero_mul])

/-- 上述输出的加权范数平方≤B‖g‖²。这是实际商空间的范数结论。 -/
theorem weightedForcing_norm_sq_le (ν : Measure α) (w m : α → ℝ)
    (hw : Measurable w) (hm : Measurable m)
    (hw_nonneg : ∀ x, 0 ≤ w x) (B : ℝ) (hB_nonneg : 0 ≤ B)
    (hbound : ∀ x, w x * m x ^ 2 ≤ B) (g : ScalarL2 ν) :
    ‖weightedForcing ν w m hw hm hw_nonneg B hB_nonneg hbound g‖ ^ 2 ≤
      B * ‖g‖ ^ 2 := by
  have hnorm : ‖weightedForcing ν w m hw hm hw_nonneg B hB_nonneg hbound g‖ ≤
      Real.sqrt B * ‖g‖ :=
    norm_boundedMul_le ν _ (hw.sqrt.mul hm) _
      (fun x => sqrt_weight_mul_abs_le _ _ _ (hw_nonneg x) hB_nonneg (hbound x)) g
  have hsquare := mul_self_le_mul_self (norm_nonneg _) hnorm
  nlinarith [Real.sq_sqrt hB_nonneg]

/-- 物理恢复确实得到 m g；零区必须有 m=0，不能只凭权重为零遗漏原场。
正区以 √w≠0 约分；零区独立改写。 -/
theorem physicalL2_weightedForcing (ν : Measure α) (w m : α → ℝ)
    (hw : Measurable w) (hm : Measurable m)
    (hgap : ∀ x, w x = 0 ∨ 1 ≤ w x)
    (hw_nonneg : ∀ x, 0 ≤ w x) (B : ℝ) (hB_nonneg : 0 ≤ B)
    (hbound : ∀ x, w x * m x ^ 2 ≤ B)
    (hzero : ∀ x, w x = 0 → m x = 0)
    (C : ℝ) (hm_bound : ∀ x, |m x| ≤ C) (g : ScalarL2 ν) :
    physicalL2 ν w hw hgap
      (weightedForcing ν w m hw hm hw_nonneg B hB_nonneg hbound g) =
      boundedMul ν m hm C hm_bound g := by
  apply Lp.ext
  filter_upwards [physicalL2_coe ν w hw hgap
      (weightedForcing ν w m hw hm hw_nonneg B hB_nonneg hbound g),
    coeFn_boundedMul ν (fun x => Real.sqrt (w x) * m x) (hw.sqrt.mul hm)
      (Real.sqrt B) (fun x => sqrt_weight_mul_abs_le _ _ _ (hw_nonneg x)
        hB_nonneg (hbound x)) g,
    coeFn_boundedMul ν m hm C hm_bound g] with x hphysical hcoord hordinary
  rw [hphysical, hordinary]
  change (Real.sqrt (w x))⁻¹ *
    (boundedMul ν (fun x => Real.sqrt (w x) * m x) _ _ _ g) x = _
  rw [hcoord]
  rcases hgap x with hw_zero | hw_lower
  · simp [hw_zero, hzero x hw_zero]
  · have hsqrt_ne : Real.sqrt (w x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
    field_simp

end LeanPML.Analysis

namespace LeanPML.PML

/-- V7 (5.8) 后未编号式的系数依据：wᵢ σᵢ²、wᵢ σⱼ²≤cS。
只用非负及幅度限制；a=0 独立分支，不除以吸收系数。 -/
theorem weight_absorption_squares (c p r S : ℝ)
    (hc_pos : 0 < c) (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (hp_le : p ≤ S) (hr_le : r ≤ S) (hS_le : S ≤ c / 4) :
    energyWeightX c p r * p ^ 2 ≤ c * S ∧
    energyWeightX c p r * r ^ 2 ≤ c * S := by
  have hS_nonneg : 0 ≤ S := hp_nonneg.trans hp_le
  by_cases ha_pos : 0 < absorptionSum p r
  · have hcr_nonneg : 0 ≤ c - r := by linarith
    have hp_square : p ^ 2 ≤ S * (p + r) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp_le) hp_nonneg, mul_nonneg hS_nonneg hr_nonneg]
    have hr_square : r ^ 2 ≤ S * (p + r) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr_le) hr_nonneg, mul_nonneg hS_nonneg hp_nonneg]
    rw [energyWeightX, if_pos ha_pos]
    constructor
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ ha_pos).2
      dsimp [absorptionSum]
      have hscale := mul_le_mul_of_nonneg_left hp_square hc_pos.le
      nlinarith [mul_nonneg hr_nonneg (sq_nonneg p)]
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ ha_pos).2
      dsimp [absorptionSum]
      have hscale := mul_le_mul_of_nonneg_left hr_square hc_pos.le
      nlinarith [mul_nonneg hr_nonneg (sq_nonneg r)]
  · simp only [energyWeightX, if_neg ha_pos, zero_mul]
    exact ⟨mul_nonneg hc_pos.le hS_nonneg, mul_nonneg hc_pos.le hS_nonneg⟩

/-- V7 (5.8) 前的关键界 wᵢ(σⱼ−σᵢ)²≤2cS。
先用非负吸收得到 (r−p)²≤p²+r²，再调用上一条，未放宽论文常数。 -/
theorem weight_difference_square (c p r S : ℝ)
    (hc_pos : 0 < c) (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (hp_le : p ≤ S) (hr_le : r ≤ S) (hS_le : S ≤ c / 4) :
    energyWeightX c p r * (r - p) ^ 2 ≤ 2 * c * S := by
  have hw_nonneg : 0 ≤ energyWeightX c p r := by
    by_cases ha_pos : 0 < absorptionSum p r
    · rw [energyWeightX, if_pos ha_pos]
      exact div_nonneg (by linarith) ha_pos.le
    · simp [energyWeightX, ha_pos]
  have hsplit : (r - p) ^ 2 ≤ p ^ 2 + r ^ 2 := by
    nlinarith [mul_nonneg hp_nonneg hr_nonneg]
  have hweighted := mul_le_mul_of_nonneg_left hsplit hw_nonneg
  have hbounds := weight_absorption_squares c p r S hc_pos hp_nonneg hr_nonneg
    hp_le hr_le hS_le
  nlinarith

namespace SpatialAbsorption
open LeanPML.Analysis
variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/-- 幅度非负由任一点的 0≤p≤S 得到；矩形非空，不额外加强物理条件。 -/
theorem forcing_S_nonneg (C : SpatialAbsorption α) : 0 ≤ C.S :=
  (C.p_nonneg (Classical.arbitrary α)).trans (C.p_le_S _)

omit [Nonempty α] in
/-- 能量权重非负，包括独立的零区分支。 -/
theorem forcing_wx_nonneg (C : SpatialAbsorption α) (x : α) : 0 ≤ C.wx x := by
  rcases C.wx_gap x with hzero | hlower
  · rw [hzero]
  · exact zero_le_one.trans hlower

omit [Nonempty α] in
private theorem x_lift_bound (C : SpatialAbsorption α) (other : Bool) (x : α) :
    C.wx x * (if other then C.r x else C.p x) ^ 2 ≤ C.c * C.S := by
  have hbounds := weight_absorption_squares C.c (C.p x) (C.r x) C.S
    C.c_pos (C.p_nonneg x) (C.r_nonneg x) (C.p_le_S x) (C.r_le_S x) C.S_le_quarter
  cases other
  · exact hbounds.1
  · exact hbounds.2

/-- (5.8) 后的乘子：other=false 表示 σᵢ=p，true 表示 σⱼ=r。
输入仅普通 L²；输出实际 wₓ 加权空间，成员资格已由系数界证明。
y 方向用 C.swap 调用，不能仍用 x 方向的系数次序。 -/
def xAbsorptionLift (ν : Measure α) (C : SpatialAbsorption α) (other : Bool) :
    ScalarL2 ν →L[ℝ] WeightedL2 ν C.wx :=
  weightedForcing ν C.wx (fun x => if other then C.r x else C.p x)
    C.wx_measurable (by
      cases other
      · exact C.p_measurable
      · exact C.r_measurable)
    C.forcing_wx_nonneg (C.c * C.S) (mul_nonneg C.c_pos.le C.forcing_S_nonneg)
    (C.x_lift_bound other)

/-- 实际加权强迫的平方范数界，供 φ_t 的双项估计调用。 -/
theorem xAbsorptionLift_norm_sq (ν : Measure α) (C : SpatialAbsorption α)
    (other : Bool) (g : ScalarL2 ν) :
    ‖C.xAbsorptionLift ν other g‖ ^ 2 ≤ C.c * C.S * ‖g‖ ^ 2 :=
  weightedForcing_norm_sq_le ν C.wx _ C.wx_measurable _
    C.forcing_wx_nonneg (C.c * C.S) _ (C.x_lift_bound other) g

omit [Nonempty α] in
private theorem absorption_zero_of_wx_zero (C : SpatialAbsorption α) (x : α)
    (hw_zero : C.wx x = 0) : C.p x = 0 ∧ C.r x = 0 := by
  have ha_zero : C.a x = 0 := (C.wx_eq_zero_iff x).mp hw_zero
  change C.p x + C.r x = 0 at ha_zero
  constructor <;> linarith [C.p_nonneg x, C.r_nonneg x]

/-- 恢复后与普通 L² 系数乘法相同；零区中 p=r=0 来自非负及 a=0。 -/
theorem physical_xAbsorptionLift (ν : Measure α) (C : SpatialAbsorption α)
    (other : Bool) (g : ScalarL2 ν) :
    physicalL2 ν C.wx C.wx_measurable C.wx_gap (C.xAbsorptionLift ν other g) =
      (if other then C.rCoeff else C.pCoeff).operator ν g := by
  cases other
  · exact physicalL2_weightedForcing ν C.wx C.p C.wx_measurable C.p_measurable
      C.wx_gap C.forcing_wx_nonneg (C.c * C.S) _ (C.x_lift_bound false)
      (fun x hx => (C.absorption_zero_of_wx_zero x hx).1) |C.S| C.pCoeff.abs_le g
  · exact physicalL2_weightedForcing ν C.wx C.r C.wx_measurable C.r_measurable
      C.wx_gap C.forcing_wx_nonneg (C.c * C.S) _ (C.x_lift_bound true)
      (fun x hx => (C.absorption_zero_of_wx_zero x hx).2) |C.S| C.rCoeff.abs_le g

/-- (5.7) 的真实强迫映射：g↦(r−p)g，输入普通 L²，输出 wₓ 空间。
平方根坐标系数由 weight_difference_square 控制，不要求 wₓ 有上界。 -/
def differenceLift (ν : Measure α) (C : SpatialAbsorption α) :
    ScalarL2 ν →L[ℝ] WeightedL2 ν C.wx :=
  weightedForcing ν C.wx (fun x => C.r x - C.p x)
    C.wx_measurable (C.r_measurable.sub C.p_measurable) C.forcing_wx_nonneg
    (2 * C.c * C.S) (mul_nonneg (mul_nonneg (by norm_num) C.c_pos.le) C.forcing_S_nonneg)
    (fun x => weight_difference_square C.c (C.p x) (C.r x) C.S C.c_pos
      (C.p_nonneg x) (C.r_nonneg x) (C.p_le_S x) (C.r_le_S x) C.S_le_quarter)

/-- (5.8) 所需的实际强迫平方界：‖(r−p)g‖w²≤2cS‖g‖²。
这里已经是空间范数，不再只是点态系数代数；时间卷积估计另需证明。 -/
theorem differenceLift_norm_sq (ν : Measure α) (C : SpatialAbsorption α)
    (g : ScalarL2 ν) : ‖C.differenceLift ν g‖ ^ 2 ≤ 2 * C.c * C.S * ‖g‖ ^ 2 := by
  unfold differenceLift
  exact weightedForcing_norm_sq_le ν _ _ _ _ _ _ _ _ g

/-- 记忆强迫的加权构造与普通 L² 右端一致；零区由 p=r=0 处理。 -/
theorem physical_differenceLift (ν : Measure α) (C : SpatialAbsorption α)
    (g : ScalarL2 ν) :
    physicalL2 ν C.wx C.wx_measurable C.wx_gap (C.differenceLift ν g) =
      C.rCoeff.operator ν g - C.pCoeff.operator ν g := by
  have hphysical := physicalL2_weightedForcing ν C.wx (fun x => C.r x - C.p x)
    C.wx_measurable (C.r_measurable.sub C.p_measurable) C.wx_gap C.forcing_wx_nonneg
    (2 * C.c * C.S) (mul_nonneg (mul_nonneg (by norm_num) C.c_pos.le) C.forcing_S_nonneg)
    (fun x => weight_difference_square C.c (C.p x) (C.r x) C.S C.c_pos
      (C.p_nonneg x) (C.r_nonneg x) (C.p_le_S x) (C.r_le_S x) C.S_le_quarter)
    (fun x hx => by rcases C.absorption_zero_of_wx_zero x hx with ⟨hp, hr⟩; simp [hp, hr])
    (C.rCoeff.sub C.pCoeff).bound (C.rCoeff.sub C.pCoeff).abs_le g
  exact hphysical.trans ((C.rCoeff.operator_sub C.pCoeff ν g))

/-- V7 (5.8) 后未编号估计的实际加权导数值：r h−p l。
h 可取真实弱梯度，l 可取 H(div) 通量分量；这不是任意命名的标量代数。 -/
def auxiliaryRateX (ν : Measure α) (C : SpatialAbsorption α)
    (h l : ScalarL2 ν) : WeightedL2 ν C.wx :=
  C.xAbsorptionLift ν true h - C.xAbsorptionLift ν false l

/-- 已构造的加权坐标恢复成原辅助演化右端；等式在 L² 商类中成立。 -/
theorem physical_auxiliaryRateX (ν : Measure α) (C : SpatialAbsorption α)
    (h l : ScalarL2 ν) :
    physicalL2 ν C.wx C.wx_measurable C.wx_gap (C.auxiliaryRateX ν h l) =
      C.rCoeff.operator ν h - C.pCoeff.operator ν l := by
  rw [auxiliaryRateX, map_sub, C.physical_xAbsorptionLift, C.physical_xAbsorptionLift]
  rfl

/-- V7 (5.8) 后未编号式的单方向实际范数估计。
先用旧工程的差平方界，再分别用 cS 系数界；保留精确因子 2。 -/
theorem auxiliaryRateX_norm_sq (ν : Measure α) (C : SpatialAbsorption α)
    (h l : ScalarL2 ν) :
    ‖C.auxiliaryRateX ν h l‖ ^ 2 ≤ 2 * C.c * C.S * (‖h‖ ^ 2 + ‖l‖ ^ 2) := by
  have hsplit := norm_sub_sq_le_twice (C.xAbsorptionLift ν true h)
    (C.xAbsorptionLift ν false l)
  have hgradient := C.xAbsorptionLift_norm_sq ν true h
  have hflux := C.xAbsorptionLift_norm_sq ν false l
  change ‖C.xAbsorptionLift ν true h - C.xAbsorptionLift ν false l‖ ^ 2 ≤ _
  linarith

omit [Nonempty α] in
/-- 方向交换后的权重确为 w_y；分母 r+p=p+r，并非把两个方向默认为相同。 -/
theorem swap_wx_eq_wy (C : SpatialAbsorption α) : C.swap.wx = C.wy := by
  funext x
  simp only [wx, wy, swap, energyWeightX, energyWeightY, absorptionSum, add_comm]

/-- V7 (5.8) 后的二维估计，接到真实弱梯度与 H(div) 分量。
右侧为两个分量的平方和；不把普通乘积类型的 max 范数误当欧氏范数。
y 输出属于 C.swap.wx（上一条证明等于 C.wy），输入次序为 p h_y−r l_y。 -/
theorem auxiliaryRate_weak_norm_sq (D : LeanPML.Rectangle.Rect)
    (C : SpatialAbsorption (ℝ × ℝ))
    (u : LeanPML.Rectangle.weakH1Graph D) (L : LeanPML.Rectangle.weakHDivGraph D) :
    ‖C.auxiliaryRateX D.measure (u.val 1) (L.val 0)‖ ^ 2 +
      ‖C.swap.auxiliaryRateX D.measure (u.val 2) (L.val 1)‖ ^ 2 ≤
      2 * C.c * C.S *
        (‖u.val 1‖ ^ 2 + ‖u.val 2‖ ^ 2 + ‖L.val 0‖ ^ 2 + ‖L.val 1‖ ^ 2) := by
  have hx := C.auxiliaryRateX_norm_sq D.measure (u.val 1) (L.val 0)
  have hy := C.swap.auxiliaryRateX_norm_sq D.measure (u.val 2) (L.val 1)
  change _ ≤ 2 * C.c * C.S * _ at hy
  linarith

/-- 原普通 L² 路径的真实导数确有加权代表，并满足论文估计。
hpath 是 HasDerivAt 证据，hODE 是辅助演化；没有假设全时段加权成员。
这仅证明该时刻导数值的加权成员，不能由此宣称路径在加权范数中可导。 -/
theorem auxiliary_derivative_weighted_representative
    (ν : Measure α) (C : SpatialAbsorption α) (φ : ℝ → ScalarL2 ν)
    (h l dφ : ScalarL2 ν) (t : ℝ)
    (hpath : HasDerivAt φ dφ t)
    (hODE : dφ = C.rCoeff.operator ν h - C.pCoeff.operator ν l) :
    ∃ W : WeightedL2 ν C.wx,
      HasDerivAt φ (physicalL2 ν C.wx C.wx_measurable C.wx_gap W) t ∧
      ‖W‖ ^ 2 ≤ 2 * C.c * C.S * (‖h‖ ^ 2 + ‖l‖ ^ 2) := by
  refine ⟨C.auxiliaryRateX ν h l, ?_, C.auxiliaryRateX_norm_sq ν h l⟩
  rw [C.physical_auxiliaryRateX, ← hODE]
  exact hpath

/-- (5.7) 的阻尼形式在实际加权空间成立。
兼容关系 l=h+φ 只识别空间坐标；通过物理恢复的单射性证明等式，
没有对无界权重求导。后续可在此基础上证明加权空间中的变常数公式。 -/
theorem auxiliaryRateX_eq_damped (ν : Measure α) (C : SpatialAbsorption α)
    (W : WeightedL2 ν C.wx) (h l : ScalarL2 ν)
    (hspace : l = h + physicalL2 ν C.wx C.wx_measurable C.wx_gap W) :
    C.auxiliaryRateX ν h l =
      -(weightedMul ν C.wx C.pCoeff.value C.pCoeff.measurable
        C.pCoeff.bound C.pCoeff.abs_le W) + C.differenceLift ν h := by
  apply physicalL2_injective ν C.wx C.wx_measurable C.wx_gap
  rw [C.physical_auxiliaryRateX, map_add, map_neg,
    physicalL2_weightedMul, C.physical_differenceLift, hspace, map_add]
  abel

omit [Nonempty α] in
/-- 非负吸收产生实际加权 Hilbert 空间中的非负阻尼算子。
内积还原为 ∫p X²（X=√w φ），可积性由有界 p 与 X∈L² 保证。
这是时间记忆估计所需的已证耗散性，不作为原系数结构字段输入。 -/
theorem weighted_absorption_inner_nonneg (ν : Measure α) (C : SpatialAbsorption α)
    (X : WeightedL2 ν C.wx) :
    0 ≤ inner ℝ X (weightedMul ν C.wx C.pCoeff.value C.pCoeff.measurable
      C.pCoeff.bound C.pCoeff.abs_le X) := by
  rw [real_inner_comm]
  change 0 ≤ inner ℝ (boundedMul ν C.pCoeff.value C.pCoeff.measurable
    C.pCoeff.bound C.pCoeff.abs_le X.val) X.val
  rw [inner_boundedMul_eq_integral]
  apply integral_nonneg
  intro x
  change 0 ≤ C.p x * X.val x * X.val x
  nlinarith [mul_nonneg (C.p_nonneg x) (sq_nonneg (X.val x))]

end SpatialAbsorption
end LeanPML.PML
