import LeanPML.Examples.SmoothBump
import LeanPML.Rectangle.RegionalCoefficients
import LeanPML.Rectangle.ParameterCertificate

/-!
# v0.5.2：含物理区、四边层和四角层的实际光滑剖面

V7 §10 的 (10.2) 使用正部幂剖面，通常只有有限阶光滑。
这里为已选 C∞ 解类使用光滑替代 S·smoothTransition(4x²-1)：
物理区 [-1/2,1/2] 为零，外侧严格为正，|x|≥3/4 时等于 S。
它保持原文的分区结构，但不声称逐字验证 (10.2) 的幂函数。

参数复用实际矩形 C_P=4 的证书：c=1/16384，S=1/65536，K=384；
不用原精确 π 常数下的旧数值。下方还提供非零物理区紧支函数和
正吸收平台内的单向 bump，供兼容初值及静态例调用，不宣称解存在。
-/
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff
open LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
open LeanPML.Examples.SmoothBump
namespace LeanPML.Examples.FullDomain

/-- 分离剖面的一维实际函数；x/y 两向分别读取各自坐标。
来源 V7 (10.2) 的 C∞ 替代版本，幅度与阈值使用本工程保守常数。 -/
def profile (x : ℝ) : ℝ := amplitudeS * Real.smoothTransition (4*x^2-1)

/-- 多项式与 mathlib 光滑过渡函数复合，保证内界面也 C∞。 -/
theorem profile_contDiff : ContDiff ℝ ∞ profile := by
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const))

/-- 剖面满足 0≤profile≤S；本具体选择甚至全轴有界，
但 RegionalAbsorption 只使用计算域闭区间上的界。 -/
theorem profile_bounds (x : ℝ) : 0≤profile x ∧ profile x≤amplitudeS := by
  constructor
  · exact mul_nonneg amplitudeS_pos.le (Real.smoothTransition.nonneg _)
  · exact mul_le_of_le_one_right amplitudeS_pos.le (Real.smoothTransition.le_one _)

/-- 零剖面恰对应 |x|≤1/2，包含内界面；保留真正的零吸收物理区。 -/
theorem profile_zero_iff (x : ℝ) : profile x=0 ↔ |x|≤(1:ℝ)/2 := by
  rw [profile,mul_eq_zero,or_iff_right amplitudeS_pos.ne',Real.smoothTransition.zero_iff_nonpos]
  have hsquare : |x|≤(1:ℝ)/2 ↔ x^2≤(1:ℝ)/4 := by
    rw [← sq_le_sq₀ (abs_nonneg x) (by norm_num : (0:ℝ)≤1/2)]
    norm_num [sq_abs]
  rw [hsquare]
  constructor <;> intro hbound <;> linarith

/-- 物理坐标闭区间上剖面为零；用于物理区紧支数据。 -/
theorem profile_zero_of_mem_physical {x : ℝ} (hx : x∈Icc (-(1:ℝ)/2) (1/2)) :
    profile x=0 :=
  (profile_zero_iff x).mpr (abs_le.mpr (by constructor <;> linarith [hx.1,hx.2]))

/-- 内界面外严格吸收。只要求某点在外侧，不引入统一正下界。 -/
theorem profile_pos_iff (x : ℝ) : 0<profile x ↔ (1:ℝ)/2< |x| := by
  constructor
  · intro hpositive
    by_contra hnot
    have hzero : profile x=0 := (profile_zero_iff x).mpr (le_of_not_gt hnot)
    exact hpositive.ne' hzero
  · intro houtside
    apply lt_of_le_of_ne (profile_bounds x).1
    intro hzero
    have hinside : |x|≤(1:ℝ)/2 := (profile_zero_iff x).mp hzero.symm
    exact not_le_of_gt houtside hinside

/-- |x|≥3/4 的外层是正平台 profile=S。
这是本构造的额外便利性质，供静态 bump 支撑上的有界权重计算使用。 -/
theorem profile_eq_amplitude_of_plateau {x : ℝ} (hx : (3:ℝ)/4≤|x|) :
    profile x=amplitudeS := by
  have hsquare : ((3:ℝ)/4)^2≤x^2 := by
    have hpow := (sq_le_sq₀ (by norm_num : (0:ℝ)≤3/4) (abs_nonneg x)).mpr hx
    simpa only [sq_abs] using hpow
  have hargument : 1≤4*x^2-1 := by nlinarith only [hsquare]
  rw [profile,Real.smoothTransition.one_of_one_le hargument,mul_one]

/-- 实际区域系数结构，p(x)=profile x、r(y)=profile y。
所有字段都是已证明的光滑性、原幅度和正性；不输入权重界或能量结论。 -/
def regional : RegionalAbsorption unitSquare where
  c := smallC
  S := amplitudeS
  c_pos := smallC_pos
  p := profile
  r := profile
  p_smooth := profile_contDiff
  r_smooth := profile_contDiff
  p_bounds := fun x _ => profile_bounds x
  r_bounds := fun y _ => profile_bounds y
  S_le_quarter := amplitudeS_eq_quarter.le

/-- 同一具体剖面调用实际 C_P=4 下的阈值证书，未沿用旧 c=1/128。 -/
theorem regional_threshold :
    regional.c ≤ LeanPML.PML.threshold 1 1 1 1 (poincareConstant unitSquare) :=
  unitSquare_le_threshold

/-- 物理区内两个吸收系数均为零。 -/
theorem physical_region (x y : ℝ)
    (hx : x∈Icc (-(1:ℝ)/2) (1/2)) (hy : y∈Icc (-(1:ℝ)/2) (1/2)) :
    profile x=0 ∧ profile y=0 :=
  ⟨profile_zero_of_mem_physical hx,profile_zero_of_mem_physical hy⟩

/-- 左/右边层：x 外侧正吸收，y 仍在物理坐标区间。
用 |x| 统一两边，但不把两个方向交换。 -/
theorem vertical_side (x y : ℝ) (hx : (1:ℝ)/2< |x|)
    (hy : y∈Icc (-(1:ℝ)/2) (1/2)) : 0<profile x ∧ profile y=0 :=
  ⟨(profile_pos_iff x).mpr hx,profile_zero_of_mem_physical hy⟩

/-- 下/上边层：p=0、r>0，与上一条的系数方向相反。 -/
theorem horizontal_side (x y : ℝ) (hx : x∈Icc (-(1:ℝ)/2) (1/2))
    (hy : (1:ℝ)/2< |y|) : profile x=0 ∧ 0<profile y :=
  ⟨profile_zero_of_mem_physical hx,(profile_pos_iff y).mpr hy⟩

/-- 四个角层两个吸收系数都严格为正，不能只以单边层代替二维角层。 -/
theorem corner_region (x y : ℝ) (hx : (1:ℝ)/2< |x|) (hy : (1:ℝ)/2< |y|) :
    0<profile x ∧ 0<profile y :=
  ⟨(profile_pos_iff x).mpr hx,(profile_pos_iff y).mpr hy⟩

/-- 四个边层各有整个矩形内部的具体点；不是只检验对称角点。 -/
theorem four_sides_nonempty :
    ((3/4:ℝ),0)∈unitSquare.openSet ∧ ((-3/4:ℝ),0)∈unitSquare.openSet ∧
    ((0:ℝ),3/4)∈unitSquare.openSet ∧ ((0:ℝ),-3/4)∈unitSquare.openSet ∧
    (0<profile (3/4) ∧ profile 0=0) ∧ (0<profile (-3/4) ∧ profile 0=0) ∧
    (profile 0=0 ∧ 0<profile (3/4)) ∧ (profile 0=0 ∧ 0<profile (-3/4)) := by
  have hzero : profile 0=0 := (profile_zero_iff 0).mpr (by norm_num)
  have hplus : 0<profile (3/4) := (profile_pos_iff _).mpr (by norm_num)
  have hminus : 0<profile (-3/4) := (profile_pos_iff _).mpr (by norm_num)
  refine ⟨?_,?_,?_,?_,⟨hplus,hzero⟩,⟨hminus,hzero⟩,⟨hzero,hplus⟩,⟨hzero,hminus⟩⟩ <;>
    norm_num [Rect.openSet,LeanPML.PML.rectangleDomain,unitSquare]

/-- 四个角层各有实际域内点，同时核验 p>0、r>0。 -/
theorem four_corners_nonempty :
    ∀ x∈({(3/4:ℝ),-3/4} : Set ℝ), ∀ y∈({(3/4:ℝ),-3/4} : Set ℝ),
      (x,y)∈unitSquare.openSet ∧ 0<profile x ∧ 0<profile y := by
  intro x hx y hy
  simp only [mem_insert_iff,mem_singleton_iff] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;>
    constructor
  all_goals first
  | exact corner_region _ _ (by norm_num) (by norm_num)
  | norm_num [Rect.openSet,LeanPML.PML.rectangleDomain,unitSquare]

/-- 非零二维物理区 bump，两个方向都真依赖空间坐标。
拓扑支撑在 [-1/4,1/4]²，严格置于物理区内部。 -/
def physicalBump : SmoothField :=
  ⟨fun X : ℝ×ℝ => basicBump 0 (1/4) X.1 * basicBump 0 (1/4) X.2,
    ((basicBump_contDiff 0 (1/4)).comp contDiff_fst).mul
      ((basicBump_contDiff 0 (1/4)).comp contDiff_snd)⟩

/-- 中心严格为正，保证实际二维函数非零。 -/
theorem physicalBump_center_pos : 0<physicalBump (0,0) :=
  mul_pos (basicBump_center_pos 0 (1/4) (by norm_num))
    (basicBump_center_pos 0 (1/4) (by norm_num))

/-- 二维拓扑支撑位于物理区内的紧矩形；使用闭包最小性处理端点。 -/
theorem physicalBump_tsupport_subset :
    tsupport (⇑physicalBump) ⊆ Icc (-(1:ℝ)/4) (1/4) ×ˢ Icc (-(1:ℝ)/4) (1/4) := by
  apply closure_minimal ?_ (isClosed_Icc.prod isClosed_Icc)
  intro X hX
  have hprod : basicBump 0 (1/4) X.1 * basicBump 0 (1/4) X.2≠0 := hX
  have hx : X.1∈Ioo (0-(1:ℝ)/4) (0+1/4) :=
    (basicBump_pos_iff 0 (1/4) X.1 (by norm_num)).mp
      (lt_of_le_of_ne (basicBump_nonneg _ _ _) (Ne.symm (mul_ne_zero_iff.mp hprod).1))
  have hy : X.2∈Ioo (0-(1:ℝ)/4) (0+1/4) :=
    (basicBump_pos_iff 0 (1/4) X.2 (by norm_num)).mp
      (lt_of_le_of_ne (basicBump_nonneg _ _ _) (Ne.symm (mul_ne_zero_iff.mp hprod).2))
  constructor <;> constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

/-- 二维函数的实际紧支撑，不是仅有点态零值的命名。 -/
theorem physicalBump_hasCompactSupport : HasCompactSupport (⇑physicalBump) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport _)
    physicalBump_tsupport_subset

/-- 支撑上的两个吸收系数为零，供兼容数据和增长族消去 p/r 项。 -/
theorem physicalBump_support_zero {X : ℝ×ℝ} (hX : X∈tsupport (⇑physicalBump)) :
    profile X.1=0 ∧ profile X.2=0 := by
  have hbox := physicalBump_tsupport_subset hX
  apply physical_region <;> constructor <;> linarith [hbox.1.1,hbox.1.2,hbox.2.1,hbox.2.2]

/-- 真正坐标导数的支撑仍在同一物理紧矩形，由一般 Fréchet 导数支撑定理推出。 -/
theorem physicalBump_gradient_tsupport_subset :
    tsupport (Rectangle.dx physicalBump) ⊆ tsupport (⇑physicalBump) ∧
    tsupport (Rectangle.dy physicalBump) ⊆ tsupport (⇑physicalBump) :=
  ⟨tsupport_fderiv_apply_subset ℝ (1,0),tsupport_fderiv_apply_subset ℝ (0,1)⟩

/-- x=-1/8,y=0 处真实 x 导数严格为正；用于证明梯度的实际 L² 类非零。
先调用一维真实求导，再由同一切片导数的唯一性识别 Rectangle.dx。 -/
theorem physicalBump_dx_pos : 0<Rectangle.dx physicalBump (-(1:ℝ)/8,0) := by
  have hslice := (basicBump_hasDerivAt 0 (1/4) (-(1:ℝ)/8)).mul_const (basicBump 0 (1/4) 0)
  have hidentify := (physicalBump.hasDerivAt_sliceX (-(1:ℝ)/8,0)).unique hslice
  rw [hidentify]
  have hleft : 0<basicBump 0 (1/4) (-(1:ℝ)/8) :=
    (basicBump_pos_iff 0 (1/4) _ (by norm_num)).mpr (by norm_num)
  have hright : 0<basicBump 0 (1/4) 0 := basicBump_center_pos _ _ (by norm_num)
  norm_num at hleft ⊢
  exact mul_pos (mul_pos (mul_pos (by norm_num) hleft) (by norm_num)) hright

/-- 正吸收平台内的一维紧支函数，用于单向吸收 r=0 的静态回归。
支撑 [13/16,15/16] 既远离物理区，也远离外边界。 -/
def sideBump1D : ℝ→ℝ := basicBump (7/8) (1/16)

/-- 单向 bump 的全轴 C∞ 性质。 -/
theorem sideBump1D_contDiff : ContDiff ℝ ∞ sideBump1D := basicBump_contDiff _ _

/-- 单向 bump 的中心非零。 -/
theorem sideBump1D_center_pos : 0<sideBump1D (7/8) :=
  basicBump_center_pos _ _ (by norm_num)

/-- 单向 bump 的精确闭支撑，供静态例读取平台权重。 -/
theorem sideBump1D_tsupport : tsupport sideBump1D=Icc (13/16:ℝ) (15/16) := by
  rw [sideBump1D,basicBump_tsupport _ _ (by norm_num : (0:ℝ)<1/16)]
  norm_num

/-- 单向 bump 的紧支撑，供实际 L² 成员资格和可积性使用。 -/
theorem sideBump1D_hasCompactSupport : HasCompactSupport sideBump1D :=
  basicBump_hasCompactSupport _ _ (by norm_num)

/-- 支撑上 p=S>0；无须假设整个域的吸收有正下界。 -/
theorem sideBump1D_support_plateau {x : ℝ} (hx : x∈tsupport sideBump1D) :
    profile x=amplitudeS := by
  rw [sideBump1D_tsupport] at hx
  apply profile_eq_amplitude_of_plateau
  rw [abs_of_nonneg (by linarith [hx.1])]
  linarith [hx.1]

end LeanPML.Examples.FullDomain
