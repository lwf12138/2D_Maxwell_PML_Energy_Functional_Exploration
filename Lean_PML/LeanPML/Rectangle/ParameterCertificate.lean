import LeanPML.Rectangle.Poincare

/-!
# v0.4 对齐：保守 Poincaré 常数下的精确参数证书

在整个矩形 Ω=(-1,1)×(-1,1) 上，已证明的常数是 C_P=2Lx=4。
本文件据此重新计算 V7 (5.2) 的 A、K、c_*，核验材料参数全部为 1、
c=1/16384、S=1/65536 满足 (5.3)。所有计算均为 Lean 中的精确实数等式。

建议先读 `unitSquare_explicit_smallness`、`unitSquare_le_threshold`，
再读 `oldC_not_le_threshold`：旧 c=1/128 在这个 C_P 下会使第二条小量条件失效。
本文件只核验参数，不构造二维吸收剖面、初值证书或非零 PDE 解，也不证明原文
(5.1) 的最优 π 常数；最终主定理合成仍属于后续阶段。
-/

noncomputable section
open LeanPML.PML
namespace LeanPML.Rectangle.ParameterCertificate

/-- 实际矩形 (-1,1)²；严格端点证明保证其非退化。
来源 V7 §1 的矩形几何，本数值选择为本轮证书，原文未单列。 -/
def unitSquare : Rect where
  xlo := -1
  xhi := 1
  ylo := -1
  yhi := 1
  x_lt := by norm_num
  y_lt := by norm_num

/-- 本轮新的移位常数 c；对应 (5.3)，其合法性在下方由显式条件证明。 -/
def smallC : ℝ := 1 / 16384

/-- 本轮吸收幅度上界 S=c/4；这里只给上界，不额外选取吸收场。 -/
def amplitudeS : ℝ := 1 / 65536

/-- 用于对照的旧 c 值。定义不代表它满足本轮保守常数的参数条件。 -/
def oldC : ℝ := 1 / 128

/-- 从实际矩形端点得到两条边长均为 2，供几何常数核对。 -/
theorem unitSquare_sideLengths : unitSquare.Lx = 2 ∧ unitSquare.Ly = 2 := by
  norm_num [unitSquare, Rect.Lx, Rect.Ly]

/-- 实际已证常数是 C_P=2Lx=4，不能替换成原文 (5.1) 的精确 π 常数。
后面的 K 和阈值均使用这个 `poincareConstant unitSquare`。 -/
theorem poincareConstant_unitSquare : poincareConstant unitSquare = 4 := by
  unfold poincareConstant
  rw [unitSquare_sideLengths.1]
  norm_num

/-- (5.2) 的 A=ε+2κ；本轮 ε=κ=1，因此 A=3。 -/
theorem materialA_unit : materialA 1 1 = 3 := by
  norm_num [materialA]

/-- (5.2) 的 K=8μAC_P²，在 μ=1、A=3、C_P=4 时精确为 384。
调用同一个 `scaleK` 定义，不另设与工程脱节的数值 K。 -/
theorem scaleK_unitSquare : scaleK 1 1 1 (poincareConstant unitSquare) = 384 := by
  rw [poincareConstant_unitSquare]
  norm_num [scaleK, materialA]

/-- 新 c 严格为正，供阈值双向等价中的平方根与消分母步骤使用。 -/
theorem smallC_pos : 0 < smallC := by norm_num [smallC]

/-- S 严格为正，特别满足幅度参数的非负要求。 -/
theorem amplitudeS_pos : 0 < amplitudeS := by norm_num [amplitudeS]

/-- 本轮幅度恰好取 S=c/4，因此满足 (5.3) 所需的非严格幅度上界。 -/
theorem amplitudeS_eq_quarter : amplitudeS = smallC / 4 := by
  norm_num [amplitudeS, smallC]

/-- (5.3) 的三条显式小量条件，使用矩形实际常数 C_P=4。
计算得到 c²K=3/2097152、8cAK=9/16、8cAτ=3/2048，均不超过 1。
`norm_num` 只核算有理数；这个结论随后实际传入阈值等价定理。 -/
theorem unitSquare_explicit_smallness :
    smallC ^ 2 * scaleK 1 1 1 (poincareConstant unitSquare) ≤ 1 ∧
    8 * smallC * materialA 1 1 * scaleK 1 1 1 (poincareConstant unitSquare) ≤ 1 ∧
    8 * smallC * materialA 1 1 * (1 : ℝ) ≤ 1 := by
  have hsquare_value : smallC ^ 2 * scaleK 1 1 1 (poincareConstant unitSquare) =
      (3 : ℝ) / 2097152 := by
    rw [scaleK_unitSquare]
    norm_num [smallC]
  have hmaterial_value : 8 * smallC * materialA 1 1 *
      scaleK 1 1 1 (poincareConstant unitSquare) = (9 : ℝ) / 16 := by
    rw [materialA_unit, scaleK_unitSquare]
    norm_num [smallC]
  have hrelaxation_value : 8 * smallC * materialA 1 1 * (1 : ℝ) =
      (3 : ℝ) / 2048 := by
    rw [materialA_unit]
    norm_num [smallC]
  -- 三个右端都是正有理数；此时不需要估计 sqrt K。
  constructor
  · rw [hsquare_value]
    norm_num
  · constructor
    · rw [hmaterial_value]
      norm_num
    · rw [hrelaxation_value]
      norm_num

/-- 将上一数值证书接回论文 min 定义的 c_*，不是只核验其中一条条件。
四个材料参数均为 1；C_P 正性调用真实非退化矩形引理。
使用旧工程 `le_threshold_iff_explicit` 的反向，即“三条显式条件 ⇒ c≤c_*”。 -/
theorem unitSquare_le_threshold :
    smallC ≤ threshold 1 1 1 1 (poincareConstant unitSquare) := by
  have hunit_pos : (0 : ℝ) < 1 := by norm_num
  have hCP_pos : 0 < poincareConstant unitSquare := poincareConstant_pos unitSquare
  have hiff := le_threshold_iff_explicit 1 1 1 1 (poincareConstant unitSquare) smallC
    hunit_pos hunit_pos hunit_pos hunit_pos hCP_pos smallC_pos
  apply hiff.mpr
  simpa only [one_mul] using unitSquare_explicit_smallness

/-- 本轮完整参数证书：材料正性、真实 C_P/A/K 值及正性、c/S 正性、
幅度条件和精确 min 阈值。它只证明这组数值可供后续模型使用，不给出解。 -/
theorem unitSquare_parameter_certificate :
    (0 : ℝ) < 1 ∧
    poincareConstant unitSquare = 4 ∧
    materialA 1 1 = 3 ∧
    scaleK 1 1 1 (poincareConstant unitSquare) = 384 ∧
    0 < poincareConstant unitSquare ∧
    0 < materialA 1 1 ∧
    0 < scaleK 1 1 1 (poincareConstant unitSquare) ∧
    0 < smallC ∧ 0 < amplitudeS ∧ amplitudeS ≤ smallC / 4 ∧
    smallC ≤ threshold 1 1 1 1 (poincareConstant unitSquare) := by
  have hunit_pos : (0 : ℝ) < 1 := by norm_num
  have hCP_pos : 0 < poincareConstant unitSquare := poincareConstant_pos unitSquare
  have hA_pos : 0 < materialA 1 1 := materialA_pos 1 1 hunit_pos hunit_pos
  have hK_pos : 0 < scaleK 1 1 1 (poincareConstant unitSquare) :=
    scaleK_pos 1 1 1 (poincareConstant unitSquare) hunit_pos hunit_pos hunit_pos hCP_pos
  exact ⟨hunit_pos, poincareConstant_unitSquare, materialA_unit, scaleK_unitSquare,
    hCP_pos, hA_pos, hK_pos, smallC_pos, amplitudeS_pos,
    amplitudeS_eq_quarter.le, unitSquare_le_threshold⟩

/-- 旧 c=1/128 在新 C_P 下，(5.3) 第二条左边精确等于 72。
与阈值右边 κτ=1 比较前先单列等式，避免把失败原因藏在自动化中。 -/
theorem oldC_material_condition_value :
    8 * oldC * materialA 1 1 * scaleK 1 1 1 (poincareConstant unitSquare) = 72 := by
  rw [materialA_unit, scaleK_unitSquare]
  norm_num [oldC]

/-- 旧 c 的材料小量条件失效：72>κτ=1。
这不否定原文定理，只说明不能沿用其他 Poincaré 常数下的旧数值选择。 -/
theorem oldC_fails_material_condition :
    ¬ 8 * oldC * materialA 1 1 * scaleK 1 1 1 (poincareConstant unitSquare) ≤ 1 := by
  rw [oldC_material_condition_value]
  norm_num

/-- 由阈值等价的正向证明旧 c 不满足本轮 c≤c_*。
若它满足 min 阈值，第二条显式条件必须成立，与精确 72>1 矛盾。 -/
theorem oldC_not_le_threshold :
    ¬ oldC ≤ threshold 1 1 1 1 (poincareConstant unitSquare) := by
  have hunit_pos : (0 : ℝ) < 1 := by norm_num
  have hCP_pos : 0 < poincareConstant unitSquare := poincareConstant_pos unitSquare
  have hold_pos : 0 < oldC := by norm_num [oldC]
  intro hold_le_threshold
  have hexplicit := (le_threshold_iff_explicit 1 1 1 1
    (poincareConstant unitSquare) oldC hunit_pos hunit_pos hunit_pos hunit_pos
    hCP_pos hold_pos).mp hold_le_threshold
  have hold_material : 8 * oldC * materialA 1 1 *
      scaleK 1 1 1 (poincareConstant unitSquare) ≤ 1 := by
    simpa only [one_mul] using hexplicit.2.1
  exact oldC_fails_material_condition hold_material

end LeanPML.Rectangle.ParameterCertificate
