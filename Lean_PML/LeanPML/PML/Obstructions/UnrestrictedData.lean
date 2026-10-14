import LeanPML.PML.ClassicalSystem
import LeanPML.PML.Obstructions.SingleLayer
import LeanPML.Examples.FullDomainProfile

/-!
# 任意八变量初值不能直接套用兼容类单调能量定理

来源：路线图 v0.5.3 的范围回归；V7 (2.1)、(2.4) 的实际原场计算。
取物理区内 C∞ 紧支函数 ψ，令 H=t∇ψ、Q=μ∇ψ，E=P=Z₁=Z₂=0。
本文件核验完整八条 PDE 与 PEC，而不是只验证某个局部 ODE。

磁场的真实 L² 平方随 t² 增长；初始磁辅助不变量非零，因此这族不属于
五不变量为零的兼容解类。结论只否定“对这整个增长族、以固定正数控制磁场
L²、有限初能量且全未来单调不增”的能量，不否定任意形式的能量泛函。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open LeanPML.Rectangle LeanPML.Analysis LeanPML.PML.Concrete
namespace LeanPML.PML.Obstructions

/-- 实际八变量增长路径。H 与 Q 的 x/y 次序对应原 (2.1)，
λ=(μH_y,−μH_x) 的旋转约定仍由既有 lift 使用。 -/
def unrestrictedFields (ψ : SmoothField) (μ : ℝ) : OriginalFields where
  E := fun _ _ => 0
  Hx := fun t X => t*dx ψ X
  Hy := fun t X => t*dy ψ X
  P := fun _ _ => 0
  Z1 := fun _ _ => 0
  Z2 := fun _ _ => 0
  Qx := fun _ X => μ*dx ψ X
  Qy := fun _ X => μ*dy ψ X

/-- 真正的二阶混合偏导抵消：∂x∂yψ=∂y∂xψ。
来自 mathlib 的 C² 对称性，不把 curl∇ψ=0 设成模型输入。 -/
theorem smooth_mixed_partials (ψ : SmoothField) (X : Point) :
    dx ψ.derivativeY X = dy ψ.derivativeX X := by
  have hsecond : Differentiable ℝ (fderiv ℝ (ψ : Point → ℝ)) :=
    ((contDiff_infty_iff_fderiv.mp ψ.contDiff).2).differentiable (by simp)
  have hcomponent (v : Point) :
      HasFDerivAt (fun Y => fderiv ℝ (ψ : Point → ℝ) Y v)
        ((fderiv ℝ (fderiv ℝ (ψ : Point → ℝ)) X).flip v) X := by
    simpa using (hsecond X).hasFDerivAt.clm_apply (hasFDerivAt_const v X)
  have hx := congrArg (fun L : Point →L[ℝ] ℝ => L (1,0)) (hcomponent (0,1)).fderiv
  have hy := congrArg (fun L : Point →L[ℝ] ℝ => L (0,1)) (hcomponent (1,0)).fderiv
  have hsymm := (ψ.contDiff.contDiffAt (x := X)).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
    (1,0) (0,1)
  change dx ψ.derivativeY X = _ at hx
  change dy ψ.derivativeX X = _ at hy
  exact hx.trans (hsymm.trans hy.symm)

/-- 光滑梯度在 ψ 的闭支撑外确实为零。
后续仅在支撑内使用 p=r=0；其他地方允许完整边层/角层的非零吸收。 -/
theorem gradient_zero_outside_tsupport (ψ : SmoothField) (X : Point)
    (hX : X ∉ tsupport (ψ : Point → ℝ)) : dx ψ X=0 ∧ dy ψ X=0 := by
  have hderiv : fderiv ℝ (ψ : Point → ℝ) X=0 := fderiv_of_notMem_tsupport ℝ hX
  simp only [dx,dy,hderiv,zero_apply,and_self]

/-- H_x、H_y 的真实时间导数；Q 等其余坐标为常值。
HasDerivAt 明确把导数值 ∂xψ、∂yψ 绑定到 t↦H(t,X)。 -/
theorem unrestricted_time_derivatives (ψ : SmoothField) (μ t : ℝ) (X : Point) :
    HasDerivAt (fun s => (unrestrictedFields ψ μ).Hx s X) (dx ψ X) t ∧
    HasDerivAt (fun s => (unrestrictedFields ψ μ).Hy s X) (dy ψ X) t := by
  constructor
  · simpa only [unrestrictedFields,one_mul,id_eq] using (hasDerivAt_id t).mul_const (dx ψ X)
  · simpa only [unrestrictedFields,one_mul,id_eq] using (hasDerivAt_id t).mul_const (dy ψ X)

/-- 电方程中的 curl H 为零，使用真实二阶空间求导，而不是普通代数槽抵消。 -/
theorem unrestricted_curl_zero (ψ : SmoothField) (μ t : ℝ) (X : Point) :
    spaceDx (unrestrictedFields ψ μ).Hy t X-spaceDy (unrestrictedFields ψ μ).Hx t X=0 := by
  have hx : spaceDx (unrestrictedFields ψ μ).Hy t X = t*dx ψ.derivativeY X := by
    exact spaceDx_const_mul (fun _ Y => dy ψ Y) t t X
  have hy : spaceDy (unrestrictedFields ψ μ).Hx t X = t*dy ψ.derivativeX X := by
    exact spaceDy_const_mul (fun _ Y => dx ψ Y) t t X
  rw [hx,hy,smooth_mixed_partials ψ X]
  ring

/-- 完整原八方程在任意时空点成立，前提只是 ψ 支撑在零吸收物理区。
在支撑外梯度为零；支撑内 p=r=0。真实时间导数与空间 curl 抵消先分别证明。
材料无需符号假设即可核验恒等式；物理实例会取正材料参数。 -/
theorem unrestricted_originalAt (ψ : SmoothField) (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (hsupport : ∀ X∈tsupport (ψ : Point → ℝ), p X.1=0 ∧ r X.2=0)
    (t : ℝ) (X : Point) : OriginalAt ε κ τ μ p r (unrestrictedFields ψ μ) t X := by
  have hHx := (unrestricted_time_derivatives ψ μ t X).1
  have hHy := (unrestricted_time_derivatives ψ μ t X).2
  have hHx_value : dt (unrestrictedFields ψ μ).Hx t X=dx ψ X := hHx.deriv
  have hHy_value : dt (unrestrictedFields ψ μ).Hy t X=dy ψ X := hHy.deriv
  have hconstant (a : ℝ) : HasDerivAt (fun _ : ℝ => a) (deriv (fun _ : ℝ => a) t) t :=
    (hasDerivAt_const t a).differentiableAt.hasDerivAt
  have hcurl := unrestricted_curl_zero ψ μ t X
  have hregions : (p X.1=0 ∧ r X.2=0) ∨ (dx ψ X=0 ∧ dy ψ X=0) := by
    by_cases hX : X∈tsupport (ψ : Point → ℝ)
    · exact Or.inl (hsupport X hX)
    · exact Or.inr (gradient_zero_outside_tsupport ψ X hX)
  refine {
    dE := hconstant 0, dHx := hHx.congr_deriv hHx_value.symm,
    dHy := hHy.congr_deriv hHy_value.symm, dP := hconstant 0,
    dZ1 := hconstant 0, dZ2 := hconstant 0,
    dQx := hconstant (μ*dx ψ X), dQy := hconstant (μ*dy ψ X)
    electric := ?_, magneticX := ?_, magneticY := ?_, debye := ?_,
    memory1 := ?_, memory2 := ?_, auxiliaryX := ?_, auxiliaryY := ?_ }
  · simpa only [unrestrictedFields,dt,deriv_const,mul_zero,zero_sub,sub_zero,zero_add,add_zero]
      using hcurl.symm
  · rw [hHx_value]
    rcases hregions with ⟨hp,hr⟩ | ⟨hdx,hdy⟩
    · simp [unrestrictedFields,spaceDy,hp,hr]
    · simp [unrestrictedFields,spaceDy,hdx]
  · rw [hHy_value]
    rcases hregions with ⟨hp,hr⟩ | ⟨hdx,hdy⟩
    · simp [unrestrictedFields,spaceDx,hp,hr]
    · simp [unrestrictedFields,spaceDx,hdy]
  · simp [unrestrictedFields,dt]
  · simp [unrestrictedFields,dt]
  · simp [unrestrictedFields,dt]
  · rcases hregions with ⟨hp,hr⟩ | ⟨hdx,hdy⟩
    · simp [unrestrictedFields,dt,hp,hr]
    · simp [unrestrictedFields,dt,hdx]
  · rcases hregions with ⟨hp,hr⟩ | ⟨hdx,hdy⟩
    · simp [unrestrictedFields,dt,hp,hr]
    · simp [unrestrictedFields,dt,hdy]

/-- 该族的原系统空间导数有实际证据：光滑 ψ 的梯度仍光滑，时间只作常数缩放。 -/
theorem unrestricted_spatialAt (ψ : SmoothField) (μ t : ℝ) (X : Point) :
    OriginalSpatialAt (unrestrictedFields ψ μ) t X := by
  exact ⟨differentiableAt_const 0,
    (ψ.derivativeX.differentiable X).const_mul t,
    (ψ.derivativeY.differentiable X).const_mul t⟩

/-- 全矩形、任意有限时段的完整古典解。此族故意不满足磁辅助初始兼容，
因此不能传给要求五个初始不变量为零的能量主定理。 -/
theorem unrestricted_originalClassicalOn (D : Rect) (ψ : SmoothField)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (hsupport : ∀ X∈tsupport (ψ : Point → ℝ), p X.1=0 ∧ r X.2=0) :
    OriginalClassicalOn D.openSet T ε κ τ μ p r (unrestrictedFields ψ μ) := by
  exact ⟨fun t _ X _ => unrestricted_originalAt ψ ε κ τ μ p r hsupport t X,
    fun t _ X _ => unrestricted_spatialAt ψ μ t X⟩

/-- E 恒为零，所以四条完整外边界均满足 PEC，包括时间端点。 -/
theorem unrestricted_PEC (D : Rect) (ψ : SmoothField) (μ T : ℝ) :
    OriginalRectPEC D T (unrestrictedFields ψ μ) := by
  intro t _
  exact ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

/-- 实际梯度 L² 平方；两个标量分量相加，不把普通乘积范数误当欧氏范数。 -/
def unrestrictedGradientSquare (D : Rect) (ψ : SmoothField) : ℝ :=
  ‖SmoothField.toL2 D ψ.derivativeX‖^2+‖SmoothField.toL2 D ψ.derivativeY‖^2

/-- 整个矩形上的真实磁场 L² 平方：与 unrestrictedFields 的 H=t∇ψ 是同一函数。
光滑代表已保证成员资格；不是任意命名为 normSq 的实数。 -/
def unrestrictedMagneticSquare (D : Rect) (ψ : SmoothField) (t : ℝ) : ℝ :=
  ‖SmoothField.toL2 D (t • ψ.derivativeX)‖^2+‖SmoothField.toL2 D (t • ψ.derivativeY)‖^2

/-- 真正的空间范数计算：‖H(t)‖²=t²‖∇ψ‖²。
使用实际 toL2 线性与 norm_smul；不以点态二次式代替空间 L²。 -/
theorem unrestrictedMagneticSquare_eq (D : Rect) (ψ : SmoothField) (t : ℝ) :
    unrestrictedMagneticSquare D ψ t=t^2*unrestrictedGradientSquare D ψ := by
  simp only [unrestrictedMagneticSquare,unrestrictedGradientSquare,map_smul,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs]
  ring

/-- 实际磁场 L² 路径的时间导数，与逐点 HasDerivAt 独立核验。
连续线性 toL2 与常数向量的标量乘法给出真实 L² 可导性。 -/
theorem unrestricted_magnetic_L2_derivatives (D : Rect) (ψ : SmoothField) (t : ℝ) :
    HasDerivAt (fun s => SmoothField.toL2 D (s • ψ.derivativeX))
      (SmoothField.toL2 D ψ.derivativeX) t ∧
    HasDerivAt (fun s => SmoothField.toL2 D (s • ψ.derivativeY))
      (SmoothField.toL2 D ψ.derivativeY) t := by
  constructor
  · simpa only [map_smul,one_smul,id_eq] using (hasDerivAt_id t).smul_const (SmoothField.toL2 D ψ.derivativeX)
  · simpa only [map_smul,one_smul,id_eq] using (hasDerivAt_id t).smul_const (SmoothField.toL2 D ψ.derivativeY)



/-- 梯度在内部某点非零即给出正 L² 平方。
关键是光滑代表相同 L² 类时在开矩形逐点相等，不能用一般函数 f≠0 替代 a.e. 非零。 -/
theorem unrestrictedGradientSquare_pos_of_dx (D : Rect) (ψ : SmoothField) (X : Point)
    (hX : X∈D.openSet) (hdx : dx ψ X≠0) : 0<unrestrictedGradientSquare D ψ := by
  have hnonzero : SmoothField.toL2 D ψ.derivativeX≠0 := by
    intro hzero
    have heq : SmoothField.toL2 D ψ.derivativeX=SmoothField.toL2 D (0:SmoothField) := by
      simpa only [map_zero] using hzero
    have hpoint := SmoothField.eqOn_open_of_toL2_eq D ψ.derivativeX 0 heq hX
    exact hdx hpoint
  have hnorm : 0<‖SmoothField.toL2 D ψ.derivativeX‖ := norm_pos_iff.mpr hnonzero
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hnorm) (sq_nonneg _)

/-- 初始 H 为零但 Q 可以非零；这不是兼容类中的零解。
初值只是实际 unrestrictedFields 在 t=0 的取值。 -/
theorem unrestricted_initial_fields (ψ : SmoothField) (μ : ℝ) (X : Point) :
    (unrestrictedFields ψ μ).Hx 0 X=0 ∧ (unrestrictedFields ψ μ).Hy 0 X=0 ∧
    (unrestrictedFields ψ μ).Qx 0 X=μ*dx ψ X ∧
    (unrestrictedFields ψ μ).Qy 0 X=μ*dy ψ X := by simp [unrestrictedFields]

/-- 选择固定历史初值 u₀=q₀=0 后，初始 Cx=μ∂xψ、Cy=μ∂yψ。
来源 (2.4)；E=0 的实际历史积分为零，故此时 φ₀=0，而 Q₀ 不必为零。 -/
theorem unrestricted_initial_magnetic_invariants (ψ : SmoothField) (μ : ℝ)
    (p r : ℝ → ℝ) (X : Point) :
    invariantX (unrestrictedFields ψ μ) (lift (unrestrictedFields ψ μ) μ 0 0) p 0 X=μ*dx ψ X ∧
    invariantY (unrestrictedFields ψ μ) (lift (unrestrictedFields ψ μ) μ 0 0) r 0 X=μ*dy ψ X := by
  have hhistory : integralLift (fun _ _ => (0:ℝ)) (0:Point → ℝ) 0 = 0 := by
    funext Y
    exact integralLift_initial (fun _ _ => (0:ℝ)) 0 Y
  simp [invariantX,invariantY,lift,unrestrictedFields,spaceDx,spaceDy,hhistory]

/-- 原始磁辅助兼容在梯度非零点失败；不能把此增长族冒充本项目的兼容类解。
仅使用 μ≠0 与真实梯度值非零，不假设任何目标能量性质。 -/
theorem unrestricted_not_initialCompatible (ψ : SmoothField) (ε κ τ μ : ℝ)
    (p r : ℝ → ℝ) (X : Point) (hμ : μ≠0) (hdx : dx ψ X≠0) :
    ¬ InitialCompatible (unrestrictedFields ψ μ) (lift (unrestrictedFields ψ μ) μ 0 0)
      ε κ τ p r X := by
  intro hcompatible
  have hvalue := (unrestricted_initial_magnetic_invariants ψ μ p r X).1
  have hnonzero : μ*dx ψ X≠0 := mul_ne_zero hμ hdx
  exact hnonzero (hvalue.symm.trans hcompatible.magneticX)

/-- 正梯度 L² 平方使磁场平方在未来任意大的时刻超过任意给定实数界。
没有假设全局解存在：实际八变量公式在上方已经直接构造并核验。 -/
theorem unrestricted_magnetic_growth (D : Rect) (ψ : SmoothField)
    (hpositive : 0<unrestrictedGradientSquare D ψ) (after bound : ℝ) :
    ∃ t : ℝ, 0≤t ∧ after≤t ∧ bound<unrestrictedMagneticSquare D ψ t := by
  let t : ℝ := max (max 1 after) (bound/unrestrictedGradientSquare D ψ)+1
  have hone : 1<t := by
    have h := (le_max_left 1 after).trans (le_max_left (max 1 after) (bound/unrestrictedGradientSquare D ψ))
    dsimp [t]
    linarith
  have hafter : after≤t := by
    have h := (le_max_right 1 after).trans (le_max_left (max 1 after) (bound/unrestrictedGradientSquare D ψ))
    dsimp [t]
    linarith
  have hratio : bound/unrestrictedGradientSquare D ψ<t := by
    have h := le_max_right (max 1 after) (bound/unrestrictedGradientSquare D ψ)
    dsimp [t]
    linarith
  have hlinear : bound<t*unrestrictedGradientSquare D ψ := (div_lt_iff₀ hpositive).mp hratio
  have ht_square : t≤t^2 := by nlinarith only [hone]
  have hsquare := mul_le_mul_of_nonneg_right ht_square hpositive.le
  refine ⟨t,by linarith,hafter,?_⟩
  rw [unrestrictedMagneticSquare_eq]
  exact hlinear.trans_le hsquare

/-- 该完整未来增长族不存在同时满足如下三个条件的实值能量：
(1) 固定 m>0 控制磁 L² 平方；(2) 初能量为有限实数；(3) 在 [0,∞) 单调不增。
只否定这组明确条件，不声称所有能量形式均不存在，也不否定有限时间带增长的估计。 -/
theorem unrestricted_no_global_coercive_antitone_energy (D : Rect) (ψ : SmoothField)
    (hpositive : 0<unrestrictedGradientSquare D ψ) :
    ¬ ∃ (energy : ℝ → ℝ) (m : ℝ), 0<m ∧
      (∀ t, 0≤t → m*unrestrictedMagneticSquare D ψ t≤energy t) ∧
      AntitoneOn energy (Ici 0) := by
  rintro ⟨energy,m,hm,hcontrol,hantitone⟩
  obtain ⟨t,ht,_,hgrowth⟩ := unrestricted_magnetic_growth D ψ hpositive 0 (energy 0/m)
  have hlarge : energy 0<m*unrestrictedMagneticSquare D ψ t := by
    have h := (div_lt_iff₀ hm).mp hgrowth
    simpa only [mul_comm] using h
  have hbound : energy t≤energy 0 := hantitone (by simp) ht ht
  exact (not_lt_of_ge ((hcontrol t ht).trans hbound)) hlarge

/-- 单层失败的独立回归：只调用旧 §11.1 候选的负耗散结论。
采用已经核验阈值的 smallC=1/16384；它针对该单层候选，
与上面的任意数据增长族是两种不同的范围限制。 -/
theorem singleLayer_candidate_failure_regression :
    initialDissipation 1 1 1 1 ParameterCertificate.smallC 0 0 1<0 := by
  exact initialDissipation_neg 1 1 1 1 ParameterCertificate.smallC 0 0 1
    (by norm_num) (by norm_num) (by norm_num) ParameterCertificate.smallC_pos (by norm_num)
    (fun _ => ⟨rfl,rfl⟩)



/-- 固定时刻的四个非零场仍实际紧支，来自 ψ 的紧支与导数支撑定理。
这保留物理区、边层和角层，未把计算域截成 ψ 的支撑。 -/
theorem unrestricted_compact_support (ψ : SmoothField) (μ t : ℝ)
    (hcompact : HasCompactSupport (ψ : Point → ℝ)) :
    HasCompactSupport ((unrestrictedFields ψ μ).Hx t) ∧
    HasCompactSupport ((unrestrictedFields ψ μ).Hy t) ∧
    HasCompactSupport ((unrestrictedFields ψ μ).Qx t) ∧
    HasCompactSupport ((unrestrictedFields ψ μ).Qy t) := by
  have hx : HasCompactSupport (dx ψ) := hcompact.fderiv_apply ℝ (1,0)
  have hy : HasCompactSupport (dy ψ) := hcompact.fderiv_apply ℝ (0,1)
  exact ⟨hx.mul_left,hy.mul_left,hx.mul_left,hy.mul_left⟩

/-- 任意固定历史初值都无法修复物理区非零 Qx 的磁辅助不变量。
在 p=0 的点，Cx=Qx，与 u₀ 或 q₀ 的选择无关。 -/
theorem unrestricted_no_compatible_lift (ψ : SmoothField) (ε κ τ μ : ℝ)
    (p r : ℝ → ℝ) (u₀ q₀ : Point → ℝ) (X : Point)
    (hpzero : p X.1=0) (hμ : μ≠0) (hdx : dx ψ X≠0) :
    ¬ InitialCompatible (unrestrictedFields ψ μ) (lift (unrestrictedFields ψ μ) μ u₀ q₀)
      ε κ τ p r X := by
  intro hcompatible
  have hx : μ*dx ψ X=0 := by
    simpa only [invariantX,unrestrictedFields,hpzero,zero_mul,sub_zero] using hcompatible.magneticX
  exact mul_ne_zero hμ hdx hx

/-- 实际光滑 L² 类的平方范数等于代表函数平方的空间积分。
来自旧 EnergyCalculus.norm_sq_eq_integral 与已证 toL2 的 a.e. 代表关系。 -/
theorem smooth_L2_square_integral (D : Rect) (f : SmoothField) :
    ‖SmoothField.toL2 D f‖^2 = ∫ X, (f X)^2 ∂D.measure := by
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [SmoothField.coe_toL2 D f] with X hX
  rw [hX]

/-- 梯度平方是整个矩形上的合法实际积分；可积性由两个 L² 成员证据获得。 -/
theorem unrestrictedGradientSquare_eq_integral (D : Rect) (ψ : SmoothField) :
    Integrable (fun X => (dx ψ X)^2+(dy ψ X)^2) D.measure ∧
    unrestrictedGradientSquare D ψ = ∫ X, (dx ψ X)^2+(dy ψ X)^2 ∂D.measure := by
  have hx : Integrable (fun X => (dx ψ X)^2) D.measure := (ψ.derivativeX.memLp D).integrable_sq
  have hy : Integrable (fun X => (dy ψ X)^2) D.measure := (ψ.derivativeY.memLp D).integrable_sq
  refine ⟨hx.add hy,?_⟩
  rw [unrestrictedGradientSquare,smooth_L2_square_integral,smooth_L2_square_integral]
  exact (integral_add hx hy).symm

/-- 实际 H 的空间平方可积，并与前面的 L² 范数定义相同。
这样增长结论明确关于原八变量中的两个 H 场，不只是同名的辅助量。 -/
theorem unrestrictedMagneticSquare_eq_integral (D : Rect) (ψ : SmoothField) (μ t : ℝ) :
    Integrable (fun X => ((unrestrictedFields ψ μ).Hx t X)^2+
      ((unrestrictedFields ψ μ).Hy t X)^2) D.measure ∧
    unrestrictedMagneticSquare D ψ t = ∫ X, ((unrestrictedFields ψ μ).Hx t X)^2+
      ((unrestrictedFields ψ μ).Hy t X)^2 ∂D.measure := by
  have hx : Integrable (fun X => ((unrestrictedFields ψ μ).Hx t X)^2) D.measure :=
    ((t • ψ.derivativeX).memLp D).integrable_sq
  have hy : Integrable (fun X => ((unrestrictedFields ψ μ).Hy t X)^2) D.measure :=
    ((t • ψ.derivativeY).memLp D).integrable_sq
  refine ⟨hx.add hy,?_⟩
  rw [unrestrictedMagneticSquare,smooth_L2_square_integral,smooth_L2_square_integral]
  exact (integral_add hx hy).symm



section FullProfile
open LeanPML.Examples.FullDomain LeanPML.Rectangle.ParameterCertificate

/-- 具体增长族：材料 ε=κ=τ=μ=1，吸收为完整物理区/四边层/四角层 profile。
ψ 是已构造的物理区内 C∞ 紧支函数；没有把全域吸收换为零。 -/
def fullProfileUnrestrictedFields : OriginalFields := unrestrictedFields physicalBump 1

/-- 实际紧支证书及梯度正 L² 证书。
点 (-1/8,0) 的实际 x 导数为正，且点位于开矩形内部；连续代表唯一性给出正范数。 -/
theorem fullProfile_unrestricted_gradient_positive :
    HasCompactSupport (physicalBump : Point → ℝ) ∧
    0<unrestrictedGradientSquare unitSquare physicalBump := by
  refine ⟨physicalBump_hasCompactSupport,?_⟩
  apply unrestrictedGradientSquare_pos_of_dx unitSquare physicalBump (-(1:ℝ)/8,0)
  · norm_num [Rect.openSet,unitSquare,rectangleDomain]
  · exact physicalBump_dx_pos.ne'

/-- 梯度正性确实是整个矩形上实际平方积分为正，不只是某个命名实数为正。 -/
theorem fullProfile_unrestricted_gradient_integral_pos :
    0<∫ X, (dx physicalBump X)^2+(dy physicalBump X)^2 ∂unitSquare.measure := by
  rw [← (unrestrictedGradientSquare_eq_integral unitSquare physicalBump).2]
  exact fullProfile_unrestricted_gradient_positive.2

/-- 非零完整 PML 剖面下的实际八方程和四边 PEC。
原电式的 curl H 由真混合求导为零，四辅助式由支撑与吸收区分支核验。
对每个有限 T 使用同一条全时间真实函数，而不是为各 T 另选一个局部解。 -/
theorem fullProfile_unrestricted_classical (T : ℝ) :
    OriginalClassicalOn unitSquare.openSet T 1 1 1 1 profile profile fullProfileUnrestrictedFields ∧
    OriginalRectPEC unitSquare T fullProfileUnrestrictedFields := by
  exact ⟨unrestricted_originalClassicalOn unitSquare physicalBump 1 1 1 1 T profile profile
      (fun _ hX => physicalBump_support_zero hX),
    unrestricted_PEC unitSquare physicalBump 1 T⟩

/-- 此实际族在每个时刻的 H 和 Q 都具有物理区紧支撑；未施加额外磁边界假设。 -/
theorem fullProfile_unrestricted_compact_fields (t : ℝ) :
    HasCompactSupport (fullProfileUnrestrictedFields.Hx t) ∧
    HasCompactSupport (fullProfileUnrestrictedFields.Hy t) ∧
    HasCompactSupport (fullProfileUnrestrictedFields.Qx t) ∧
    HasCompactSupport (fullProfileUnrestrictedFields.Qy t) :=
  unrestricted_compact_support physicalBump 1 t physicalBump_hasCompactSupport

/-- 任意固定 u₀、q₀ 都不能使该族的五个初始不变量全部为零。
在物理点 (-1/8,0)，p=0、Qx=∂xψ>0，所以磁辅助兼容已经失败。
这与兼容类最终主定理并不矛盾。 -/
theorem fullProfile_unrestricted_not_compatible (u₀ q₀ : Point → ℝ) :
    ¬ ∀ X∈unitSquare.openSet, InitialCompatible fullProfileUnrestrictedFields
      (lift fullProfileUnrestrictedFields 1 u₀ q₀) 1 1 1 profile profile X := by
  intro hall
  have hpoint : (-(1:ℝ)/8,0)∈unitSquare.openSet := by norm_num [Rect.openSet,unitSquare,rectangleDomain]
  have hpzero : profile (-(1:ℝ)/8)=0 :=
    profile_zero_of_mem_physical (by norm_num)
  exact unrestricted_no_compatible_lift physicalBump 1 1 1 1 profile profile u₀ q₀
    (-(1:ℝ)/8,0) hpzero (by norm_num) physicalBump_dx_pos.ne' (hall _ hpoint)

/-- 对具体完整场，磁场实际空间平方积分等于 t² 乘正的梯度平方积分。
可积性由前面的真实 L² 成员证明，不依赖积分的不可积总定义。 -/
theorem fullProfile_unrestricted_norm_growth (t : ℝ) :
    Integrable (fun X => (fullProfileUnrestrictedFields.Hx t X)^2+
      (fullProfileUnrestrictedFields.Hy t X)^2) unitSquare.measure ∧
    (∫ X, (fullProfileUnrestrictedFields.Hx t X)^2+
      (fullProfileUnrestrictedFields.Hy t X)^2 ∂unitSquare.measure) =
      t^2*unrestrictedGradientSquare unitSquare physicalBump := by
  have hintegral := unrestrictedMagneticSquare_eq_integral unitSquare physicalBump 1 t
  exact ⟨hintegral.1,hintegral.2.symm.trans (unrestrictedMagneticSquare_eq unitSquare physicalBump t)⟩

/-- 同一完整 PDE 增长族在任意晚的时间超过任意磁 L² 平方上界。 -/
theorem fullProfile_unrestricted_unbounded (after bound : ℝ) :
    ∃ t : ℝ, 0≤t ∧ after≤t ∧ bound<unrestrictedMagneticSquare unitSquare physicalBump t :=
  unrestricted_magnetic_growth unitSquare physicalBump fullProfile_unrestricted_gradient_positive.2 after bound

/-- 正常数控制磁 L²、有限初能量且全未来单调不增三项不能同时覆盖这个族。
限定的是具体已构造的非兼容完整场，不否定兼容类的两层单调能量定理。 -/
theorem fullProfile_unrestricted_no_coercive_antitone_energy :
    ¬ ∃ (energy : ℝ → ℝ) (m : ℝ), 0<m ∧
      (∀ t, 0≤t → m*unrestrictedMagneticSquare unitSquare physicalBump t≤energy t) ∧
      AntitoneOn energy (Ici 0) :=
  unrestricted_no_global_coercive_antitone_energy unitSquare physicalBump
    fullProfile_unrestricted_gradient_positive.2

end FullProfile
end LeanPML.PML.Obstructions
