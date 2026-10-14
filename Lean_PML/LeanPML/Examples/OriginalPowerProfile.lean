import LeanPML.PML.LipschitzCoefficients
import LeanPML.Rectangle.OriginalParameterThreshold

/-!
# V7 (10.2) 的原分段幂次剖面

本文件验证原式 η[2(|x|−1/2)₊]^m，m≥2，而非 C∞ 替代。
在计算区间外截断到平台仅用于获得方便的 Lipschitz 延拓；域内与原式严格相同。
Lipschitz → 绝对连续积分分部 → 二维弱导数是实际证明链，不把分段函数冒称 C∞。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate LeanPML.PML
namespace LeanPML.Examples.OriginalPower

/-- (10.2) 的正部基底，之后证明与论文写法严格相等。 -/
def base (x : ℝ) : ℝ := max 0 (2*|x|-1)
/-- 仅用于技术延拓的截断；|x|≤1 时不会触发上截断。 -/
def clippedBase (x : ℝ) : ℝ := min 1 (base x)
/-- 原文函数，域外值不作物理幅度要求。 -/
def profile (η : ℝ) (m : ℕ) (x : ℝ) : ℝ := η*(base x)^m
/-- 与原剖面在实际计算区间相同的全轴 Lipschitz 延拓。 -/
def extension (η : ℝ) (m : ℕ) (x : ℝ) : ℝ := η*(clippedBase x)^m

/-- 定义与论文 (10.2) 完全一致；正部取 max 0。 -/
theorem profile_eq_paper (η : ℝ) (m : ℕ) (x : ℝ) :
    profile η m x = η*(2*max 0 (|x|-(1:ℝ)/2))^m := by
  have heq : base x = 2*max 0 (|x|-(1:ℝ)/2) := by
    by_cases hx : |x| ≤ (1:ℝ)/2
    · rw [base,max_eq_left (by linarith),max_eq_left (by linarith)];ring
    · rw [base,max_eq_right (by linarith),max_eq_right (by linarith)];ring
  rw [profile,heq]

/-- base 的 Lipschitz 常数 2 来自绝对值的 1-Lipschitz 性及正部截断。 -/
theorem base_lipschitz : LipschitzWith 2 base := by
  have hlinear : LipschitzWith 2 (fun x : ℝ => 2*|x|-1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have habs := abs_abs_sub_abs_le_abs_sub x y
    rw [Real.dist_eq,Real.dist_eq]
    have heq : (2*|x|-1)-(2*|y|-1) = 2*(|x|-|y|) := by ring
    rw [heq,abs_mul]
    norm_num
    linarith
  exact hlinear.const_max 0

theorem clippedBase_lipschitz : LipschitzWith 2 clippedBase := base_lipschitz.const_min 1

theorem clippedBase_bounds (x : ℝ) : 0 ≤ clippedBase x ∧ clippedBase x ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

/-- 幂在 [0,1] 上的严格 Lipschitz 估计；m 任意，未用数值采样。 -/
theorem extension_lipschitz (η : ℝ) (m : ℕ) :
    LipschitzWith ⟨|η| *2*m,by positivity⟩ (extension η m) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hpow := abs_pow_sub_pow_le (clippedBase x) (clippedBase y) m
  have hmax : 0 ≤ max |clippedBase x| |clippedBase y| ∧
      max |clippedBase x| |clippedBase y| ≤ 1 := by
    rw [abs_of_nonneg (clippedBase_bounds x).1,abs_of_nonneg (clippedBase_bounds y).1]
    exact ⟨le_trans (clippedBase_bounds x).1 (le_max_left _ _),max_le (clippedBase_bounds x).2 (clippedBase_bounds y).2⟩
  have hpowbound := pow_le_one₀ hmax.1 hmax.2 (n := m-1)
  have hbase := clippedBase_lipschitz.dist_le_mul x y
  rw [Real.dist_eq,Real.dist_eq] at hbase
  norm_num at hbase
  have hdiff : |clippedBase x^m-clippedBase y^m| ≤ 2*m*|x-y| := by
    calc
      _ ≤ |clippedBase x-clippedBase y| *m*max |clippedBase x| |clippedBase y|^(m-1) := hpow
      _ ≤ |clippedBase x-clippedBase y| *m := mul_le_of_le_one_right (by positivity) hpowbound
      _ ≤ 2*m*|x-y| := by exact (mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg m)).trans_eq (by ring)
  simp only [Real.dist_eq,extension,← mul_sub,abs_mul]
  change |η| * |clippedBase x^m-clippedBase y^m| ≤ (|η| * 2*(m:ℝ))*|x-y|
  calc
    _ ≤ |η| *(2*m*|x-y|) := mul_le_mul_of_nonneg_left hdiff (abs_nonneg η)
    _ = _ := by ring

/-- 技术延拓在闭计算区间与原式相同，端点也不改变。 -/
theorem extension_eq_profile (η : ℝ) (m : ℕ) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    extension η m x = profile η m x := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hb : base x ≤ 1 := max_le (by norm_num) (by linarith)
  simp only [extension,clippedBase,min_eq_right hb,profile]

/-- 原文区域幅度：0≤p≤η≤1/512；不限制域外原剖面的增长。 -/
theorem profile_bounds (η : ℝ) (m : ℕ) (hη : 0 ≤ η) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    0 ≤ profile η m x ∧ profile η m x ≤ η := by
  rw [← extension_eq_profile η m hx]
  exact ⟨mul_nonneg hη (pow_nonneg (clippedBase_bounds x).1 _),
    mul_le_of_le_one_right hη (pow_le_one₀ (clippedBase_bounds x).1 (clippedBase_bounds x).2)⟩

/-- 物理区内吸收为零，包括内界面；m≥2 保证 m≠0。 -/
theorem profile_zero (η : ℝ) {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : |x| ≤ (1:ℝ)/2) :
    profile η m x = 0 := by
  simp [profile,base,max_eq_left (by linarith : 2*|x|-1 ≤ 0),show m ≠ 0 by omega]

/-- 外侧吸收区严格为正，但不提供全域统一正下界。 -/
theorem profile_pos (η : ℝ) (m : ℕ) (hη : 0 < η) {x : ℝ} (hx : (1:ℝ)/2 < |x|) :
    0 < profile η m x := by
  apply mul_pos hη
  apply pow_pos
  exact lt_of_lt_of_le (by linarith : 0 < 2*|x|-1) (le_max_right _ _)

/-- 技术延拓在全轴的幅度界来自截断；不改变原剖面的区域条件。 -/
theorem extension_bounds (η : ℝ) (m : ℕ) (hη : 0 ≤ η) (x : ℝ) :
    0 ≤ extension η m x ∧ extension η m x ≤ η :=
  ⟨mul_nonneg hη (pow_nonneg (clippedBase_bounds x).1 _),
    mul_le_of_le_one_right hη (pow_le_one₀ (clippedBase_bounds x).1 (clippedBase_bounds x).2)⟩

/-- 实际 x 系数及真实弱导数，不假设分段剖面 C∞。 -/
def coefficientX (η : ℝ) (m : ℕ) (hη : 0 ≤ η) : RegionalWeakCoefficient unitSquare :=
  weakCoefficientOfLipschitzX unitSquare (extension η m) (extension_lipschitz η m) η hη
    (fun x _ => by rw [abs_of_nonneg (extension_bounds η m hη x).1]; exact (extension_bounds η m hη x).2)

/-- 实际 y 系数，横向弱偏导由二维 Fubini 自动证明为零。 -/
def coefficientY (η : ℝ) (m : ℕ) (hη : 0 ≤ η) : RegionalWeakCoefficient unitSquare :=
  weakCoefficientOfLipschitzY unitSquare (extension η m) (extension_lipschitz η m) η hη
    (fun x _ => by rw [abs_of_nonneg (extension_bounds η m hη x).1]; exact (extension_bounds η m hη x).2)

/-- 原文 (10.2) 整族：整数 m≥2、0<ηx,ηy≤1/512。
物理域两剖面都零，边层只有一向正，角层两向正；允许 ηx≠ηy。
成员和幅度由构造证明，不重新作为 example 的假设。 -/
def absorption (m : ℕ) (ηx ηy : ℝ) (hηx : 0 < ηx) (hηy : 0 < ηy)
    (hxS : ηx ≤ (1:ℝ)/512) (hyS : ηy ≤ (1:ℝ)/512) : RawWeakRegionalAbsorption unitSquare where
  coefficients :=
    { p := coefficientX ηx m hηx.le
      r := coefficientY ηy m hηy.le
      profileX := profile ηx m
      profileY := profile ηy m
      p_separated := by
        intro z hz
        apply extension_eq_profile
        exact ⟨hz.1.1.le,hz.1.2.le⟩
      r_separated := by
        intro z hz
        apply extension_eq_profile
        exact ⟨hz.2.1.le,hz.2.2.le⟩ }
  c := oldC
  S := 1/512
  c_pos := by norm_num [oldC]
  S_nonneg := by norm_num
  S_le_quarter := by norm_num [oldC]
  profileX_bounds x hx := ⟨(profile_bounds ηx m hηx.le hx).1,(profile_bounds ηx m hηx.le hx).2.trans hxS⟩
  profileY_bounds y hy := ⟨(profile_bounds ηy m hηy.le hy).1,(profile_bounds ηy m hηy.le hy).2.trans hyS⟩

/-- 剖面构造实际调用原文精确常数阈值证书，而非独立填入自由 CP。 -/
theorem absorption_threshold (m : ℕ) (ηx ηy : ℝ) (hηx : 0 < ηx) (hηy : 0 < ηy)
    (hxS : ηx ≤ (1:ℝ)/512) (hyS : ηy ≤ (1:ℝ)/512) :
    (absorption m ηx ηy hηx hηy hxS hyS).c ≤ threshold 1 1 1 1 (sharpPoincareConstant unitSquare) :=
  original_parameters_threshold

/-- 由分布构造选出的代表与原文连续剖面在整个开坐标区间逐点相同。
先有 a.e. 识别，再由两者连续性提升；不是读取 L² 商类在指定点的值。 -/
theorem represented_profiles (m : ℕ) (ηx ηy : ℝ) (hηx : 0 < ηx) (hηy : 0 < ηy)
    (hxS : ηx ≤ (1:ℝ)/512) (hyS : ηy ≤ (1:ℝ)/512) :
    EqOn (profile ηx m) (absorption m ηx ηy hηx hηy hxS hyS).profileX (Ioo (-1) 1) ∧
    EqOn (profile ηy m) (absorption m ηx ηy hηx hηy hxS hyS).profileY (Ioo (-1) 1) := by
  let A := absorption m ηx ηy hηx hηy hxS hyS
  have hcx : Continuous (profile ηx m) := continuous_const.mul (base_lipschitz.continuous.pow m)
  have hcy : Continuous (profile ηy m) := continuous_const.mul (base_lipschitz.continuous.pow m)
  exact ⟨MeasureTheory.Measure.eqOn_open_of_ae_eq A.representative_spec.2.2.1 isOpen_Ioo
      hcx.continuousOn A.representative_spec.1.continuousOn,
    MeasureTheory.Measure.eqOn_open_of_ae_eq A.representative_spec.2.2.2.1 isOpen_Ioo
      hcy.continuousOn A.representative_spec.2.1.continuousOn⟩

/-- 四种空间分支的正式证书，顺序体现 x/y 方向而非只测试对称系数。
通过 represented_profiles 调用一般弱代表构造，再证明每个区域的吸收符号。 -/
theorem absorption_branches {m : ℕ} (hm : 2 ≤ m) (ηx ηy : ℝ) (hηx : 0 < ηx) (hηy : 0 < ηy)
    (hxS : ηx ≤ (1:ℝ)/512) (hyS : ηy ≤ (1:ℝ)/512)
    (z : ℝ × ℝ) (hz : z ∈ unitSquare.openSet) :
    let C := (absorption m ηx ηy hηx hηy hxS hyS).represented.spatial
    (|z.1| ≤ (1:ℝ)/2 → C.p z = 0) ∧
    (|z.2| ≤ (1:ℝ)/2 → C.r z = 0) ∧
    ((1:ℝ)/2 < |z.1| → 0 < C.p z) ∧
    ((1:ℝ)/2 < |z.2| → 0 < C.r z) := by
  let A := absorption m ηx ηy hηx hηy hxS hyS
  have hmatch := A.represented.profile_match z hz
  have hrep := represented_profiles m ηx ηy hηx hηy hxS hyS
  have hp : A.represented.spatial.p z = profile ηx m z.1 := hmatch.1.trans (hrep.1 hz.1).symm
  have hr : A.represented.spatial.r z = profile ηy m z.2 := hmatch.2.trans (hrep.2 hz.2).symm
  dsimp only
  change (_ → A.represented.spatial.p z = 0) ∧ (_ → A.represented.spatial.r z = 0) ∧
    (_ → 0 < A.represented.spatial.p z) ∧ (_ → 0 < A.represented.spatial.r z)
  rw [hp,hr]
  exact ⟨profile_zero ηx hm,profile_zero ηy hm,profile_pos ηx m hηx,profile_pos ηy m hηy⟩

/-- 真正非恒定的代表调用：中心为零，外侧点为正。
该结论验证一般代表构造的实际使用，不是只用常数系数检查类型。 -/
theorem representative_nonconstant {m : ℕ} (hm : 2 ≤ m) (ηx ηy : ℝ) (hηx : 0 < ηx) (hηy : 0 < ηy)
    (hxS : ηx ≤ (1:ℝ)/512) (hyS : ηy ≤ (1:ℝ)/512) :
    (absorption m ηx ηy hηx hηy hxS hyS).profileX 0 = 0 ∧
      0 < (absorption m ηx ηy hηx hηy hxS hyS).profileX ((3:ℝ)/4) := by
  have hrep := (represented_profiles m ηx ηy hηx hηy hxS hyS).1
  rw [← hrep (by norm_num : (0:ℝ) ∈ Ioo (-1) 1),
    ← hrep (by norm_num : (3:ℝ)/4 ∈ Ioo (-1) 1)]
  exact ⟨profile_zero ηx hm (by norm_num),profile_pos ηx m hηx (by norm_num)⟩

end LeanPML.Examples.OriginalPower
