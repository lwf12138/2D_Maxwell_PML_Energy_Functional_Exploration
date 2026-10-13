import LeanPML.PML.PrimitiveSystem
import LeanPML.Rectangle.TimeSpace
import LeanPML.Rectangle.Domain
import LeanPML.Rectangle.Boundary

/-!
# V7 命题 2.1：实际八变量与 primitive 的映射

顺序：五个初始常数为零 → 全时段重构 → 原系统推出 primitive；
再从真实 primitive 方程逐条恢复电场、磁场、Debye 和四个辅助方程。
所有对象是实际时空函数，空间偏导是 fderiv 的坐标分量。
非零不变量虽沿时间保持，但不属于此处无源 primitive 主定理。
固定 u₀、q₀ 后历史恢复由真实 FTC 唯一性证明，不声称提升规范无条件唯一。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
namespace LeanPML.PML.Concrete

/-- V7 (2.5) 加极化兼容的逐点结论包，不是原系统解的输入字段。 -/
structure CompatibleAt (F : OriginalFields) (U : PrimitiveFields)
    (ε κ τ : ℝ) (p r : ℝ → ℝ) (t : ℝ) (X : Point) : Prop where
  polar : U.q t X+τ*U.P t X = κ*U.u t X
  memory1 : F.Z1 t X = -ε*(p X.1*r X.2)*U.u t X
  memory2 : F.Z2 t X = -(p X.1*r X.2)*U.q t X
  magneticX : F.Qx t X = p X.1*U.φy t X
  magneticY : F.Qy t X = -r X.2*U.φx t X

/-- (2.4)→(2.5)：只在 t=0 输入零兼容，先利用常值结论再解出原辅助变量。 -/
theorem compatibleAt_of_initial (F : OriginalFields) (U : PrimitiveFields)
    (ε κ τ : ℝ) (p r : ℝ → ℝ) (t : ℝ) (X : Point)
    (hconstant : InvariantsEqualInitial F U ε κ τ p r t X)
    (hinitial : InitialCompatible F U ε κ τ p r X) :
    CompatibleAt F U ε κ τ p r t X := by
  have hD := hconstant.debye.trans hinitial.debye
  have hZ1 := hconstant.memory1.trans hinitial.memory1
  have hZ2 := hconstant.memory2.trans hinitial.memory2
  have hX := hconstant.magneticX.trans hinitial.magneticX
  have hY := hconstant.magneticY.trans hinitial.magneticY
  dsimp [invariantD,invariantZ1,invariantZ2,invariantX,invariantY] at *
  constructor <;> linarith

/-- V7 (2.1)→(2.6) 的真实逐点推导。兼容输入由上条保持定理提供；
电场等式使用 divλ=μcurlH，两个 φ 方程使用已经核验的磁场时间导数。
无分母消元，μ 此时不要求非零。 -/
theorem primitive_lift_at (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (t : ℝ) (X : Point)
    (hE : Continuous (fun s => F.E s X)) (hP : Continuous (fun s => F.P s X))
    (hOriginal : OriginalAt ε κ τ μ p r F t X)
    (hcompatible : CompatibleAt F (lift F μ u₀ q₀) ε κ τ p r t X)
    (hgradX : HasDerivAt (fun s => spaceDx (integralLift F.E u₀) s X) (spaceDx F.E t X) t)
    (hgradY : HasDerivAt (fun s => spaceDy (integralLift F.E u₀) s X) (spaceDy F.E t X) t) :
    PrimitiveAt ε κ τ μ p r (lift F μ u₀ q₀) t X := by
  have hφ := magnetic_lift_derivatives ε κ τ μ p r F u₀ q₀ t X hOriginal hgradX hgradY
  refine ⟨hasDerivAt_integralLift F.E u₀ X hE t,
    hasDerivAt_integralLift F.P q₀ X hP t, hOriginal.dE, hOriginal.dP, ?_, ?_, ?_, ?_, ?_, hcompatible.polar⟩
  · rw [fluxDiv_lift]
    have hmain := hOriginal.electric
    rw [hcompatible.memory1,hcompatible.memory2] at hmain
    dsimp [lift] at hmain ⊢
    have hscaled := congrArg (fun z : ℝ => μ*z) hmain
    nlinarith only [hscaled]
  · apply hφ.1.congr_deriv
    rw [hcompatible.magneticY]
    dsimp [lift]
    ring
  · apply hφ.2.congr_deriv
    rw [hcompatible.magneticX]
    dsimp [lift]
    ring
  · dsimp [lift]; ring
  · dsimp [lift]; ring

/-- V7 (2.3)、(2.5) 的真实原场重构。μ≠0 在反向证明中明确使用。
每一个原辅助变量都有实际函数定义，后面逐条验证它的原方程。 -/
def reconstruct (U : PrimitiveFields) (ε μ : ℝ) (p r : ℝ → ℝ) : OriginalFields where
  E := U.E
  Hx := fun t X => (-1/μ)*U.Λy t X
  Hy := fun t X => (1/μ)*U.Λx t X
  P := U.P
  Z1 := fun t X => (-ε*(p X.1*r X.2))*U.u t X
  Z2 := fun t X => (-(p X.1*r X.2))*U.q t X
  Qx := fun t X => p X.1*U.φy t X
  Qy := fun t X => -r X.2*U.φx t X

/-- (2.6) 的极化关系在时间邻域成立，才能对其求导。
输出 τP_t+P=κE，未额外输入教学子系统的电场方程。 -/
theorem debye_of_primitive_near (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (U : PrimitiveFields) (t : ℝ) (X : Point)
    (hat : PrimitiveAt ε κ τ μ p r U t X)
    (hnear : ∀ᶠ s in 𝓝 t, U.q s X+τ*U.P s X = κ*U.u s X) :
    τ*dt U.P t X+U.P t X = κ*U.E t X := by
  have hleft := hat.dq.add (hat.dP.const_mul τ)
  have hright := hat.du.const_mul κ
  have hright' := hright.congr_of_eventuallyEq hnear
  have hequal := hleft.unique hright'
  linarith only [hequal]

/-- (2.6) 的空间兼容对时间求导，得到真实通量导数。
低层输入实际混合导数，邻域空间兼容用于导数唯一性；没有从单点关系求导。 -/
theorem primitive_flux_derivatives (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (U : PrimitiveFields) (t : ℝ) (X : Point)
    (hat : PrimitiveAt ε κ τ μ p r U t X)
    (hnearX : ∀ᶠ s in 𝓝 t, U.Λx s X = spaceDx U.u s X+U.φx s X)
    (hnearY : ∀ᶠ s in 𝓝 t, U.Λy s X = spaceDy U.u s X+U.φy s X)
    (hgradX : HasDerivAt (fun s => spaceDx U.u s X) (spaceDx U.E t X) t)
    (hgradY : HasDerivAt (fun s => spaceDy U.u s X) (spaceDy U.E t X) t) :
    HasDerivAt (fun s => U.Λx s X)
      (spaceDx U.E t X+(r X.2-p X.1)*spaceDx U.u t X-p X.1*U.φx t X) t ∧
    HasDerivAt (fun s => U.Λy s X)
      (spaceDy U.E t X+(p X.1-r X.2)*spaceDy U.u t X-r X.2*U.φy t X) t := by
  constructor
  · exact ((hgradX.add hat.dφx).congr_of_eventuallyEq hnearX).congr_deriv (by ring)
  · exact ((hgradY.add hat.dφy).congr_of_eventuallyEq hnearY).congr_deriv (by ring)

/-- (2.6)→(2.1)：逐条恢复全部八个原方程，含四个辅助变量。
μ≠0 仅用于磁场缩放；κ、p、r 均未被除。所有导数先由真实 HasDerivAt 构造。
空间及极化兼容必须在邻域成立，正是 open-time primitive 解所提供的条件。 -/
theorem original_reconstruct_at (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (U : PrimitiveFields) (t : ℝ) (X : Point) (hμ : μ ≠ 0)
    (hat : PrimitiveAt ε κ τ μ p r U t X)
    (hnear : ∀ᶠ s in 𝓝 t, PrimitiveAt ε κ τ μ p r U s X)
    (hgradX : HasDerivAt (fun s => spaceDx U.u s X) (spaceDx U.E t X) t)
    (hgradY : HasDerivAt (fun s => spaceDy U.u s X) (spaceDy U.E t X) t) :
    OriginalAt ε κ τ μ p r (reconstruct U ε μ p r) t X := by
  have hΛ := primitive_flux_derivatives ε κ τ μ p r U t X hat
    (hnear.mono (fun _ hs => hs.fluxX)) (hnear.mono (fun _ hs => hs.fluxY)) hgradX hgradY
  have hHx := hΛ.2.const_mul (-1/μ)
  have hHy := hΛ.1.const_mul (1/μ)
  have hZ1 := hat.du.const_mul (-ε*(p X.1*r X.2))
  have hZ2 := hat.dq.const_mul (-(p X.1*r X.2))
  have hQx := hat.dφy.const_mul (p X.1)
  have hQy := hat.dφx.const_mul (-r X.2)
  have hderivatives : OriginalHasDerivAt (reconstruct U ε μ p r) t X := by
    exact ⟨hat.dE, hHx.congr_deriv hHx.deriv.symm, hHy.congr_deriv hHy.deriv.symm,
      hat.dP, hZ1.congr_deriv hZ1.deriv.symm, hZ2.congr_deriv hZ2.deriv.symm,
      hQx.congr_deriv hQx.deriv.symm, hQy.congr_deriv hQy.deriv.symm⟩
  refine ⟨hderivatives, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [reconstruct]
    rw [spaceDx_const_mul,spaceDy_const_mul]
    have hmain := hat.main
    dsimp [fluxDiv] at hmain
    apply (mul_left_cancel₀ hμ)
    field_simp
    nlinarith only [hmain]
  · change μ*deriv (fun s => (-1/μ)*U.Λy s X) t = _
    rw [hHx.deriv]
    dsimp [reconstruct]
    rw [hat.fluxY]
    field_simp
    ring
  · change μ*deriv (fun s => (1/μ)*U.Λx s X) t = _
    rw [hHy.deriv]
    dsimp [reconstruct]
    rw [hat.fluxX]
    field_simp
    ring
  · exact debye_of_primitive_near ε κ τ μ p r U t X hat (hnear.mono (fun _ hs => hs.polar))
  · exact hZ1.deriv
  · exact hZ2.deriv
  · change deriv (fun s => p X.1*U.φy s X) t = _
    rw [hQx.deriv]
    dsimp [reconstruct]
    rw [hat.fluxY]
    field_simp
    ring
  · change deriv (fun s => -r X.2*U.φx s X) t = _
    rw [hQy.deriv]
    dsimp [reconstruct]
    rw [hat.fluxX]
    field_simp
    ring

/-- 本轮光滑兼容解类的正则性：原场沿时间连续，实际历史 u 联合 C∞。
全时间连续/光滑延拓只用于正则性，PDE 仍仅要求内部成立。
没有 Green、混合求导、兼容保持或等价结论字段；混合求导从 C∞ 定理取得。 -/
structure OriginalLiftRegular (F : OriginalFields) (u₀ : Point → ℝ) : Prop where
  E_cont : ∀ X, Continuous (fun t => F.E t X)
  P_cont : ∀ X, Continuous (fun t => F.P t X)
  Hx_cont : ∀ X, Continuous (fun t => F.Hx t X)
  Hy_cont : ∀ X, Continuous (fun t => F.Hy t X)
  Z1_cont : ∀ X, Continuous (fun t => F.Z1 t X)
  Z2_cont : ∀ X, Continuous (fun t => F.Z2 t X)
  Qx_cont : ∀ X, Continuous (fun t => F.Qx t X)
  Qy_cont : ∀ X, Continuous (fun t => F.Qy t X)
  history_smooth : ContDiff ℝ ∞ (Function.uncurry (integralLift F.E u₀))

/-- 实际空间偏导的时间连续性，由已经证明的混合求导定理给出。
这是 (6.6) 的光滑解类性质，原文未单列；不是人为加入的交换条件。 -/
theorem continuous_space_partial {F : Field}
    (hsmooth : ContDiff ℝ ∞ (Function.uncurry F)) (X v : Point) :
    Continuous (fun t => fderiv ℝ (F t) X v) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (LeanPML.Rectangle.hasDerivAt_spaceFDeriv hsmooth t X v).continuousAt)

/-- (2.3) 实际积分提升满足真实混合导数。FTC 提供 u_t=E，
再由 v0.4.3 已证二阶导数对称性给出 ∂t∂iu=∂iE；不留交换假设。 -/
theorem lift_mixed_derivatives (F : OriginalFields) (u₀ : Point → ℝ)
    (hregular : OriginalLiftRegular F u₀) (t : ℝ) (X : Point) :
    HasDerivAt (fun s => spaceDx (integralLift F.E u₀) s X) (spaceDx F.E t X) t ∧
    HasDerivAt (fun s => spaceDy (integralLift F.E u₀) s X) (spaceDy F.E t X) t := by
  have hnear : ∀ᶠ Y in 𝓝 X, HasDerivAt (fun s => integralLift F.E u₀ s Y) (F.E t Y) t :=
    Filter.Eventually.of_forall (fun Y => hasDerivAt_integralLift F.E u₀ Y (hregular.E_cont Y) t)
  exact ⟨LeanPML.Rectangle.hasDerivAt_spaceFDeriv_of_timeDeriv hregular.history_smooth t X (1,0) hnear,
    LeanPML.Rectangle.hasDerivAt_spaceFDeriv_of_timeDeriv hregular.history_smooth t X (0,1) hnear⟩

/-- V7 (2.4) 的实际场版本：整个 Ω 上，每个内部/端点时刻的五个场均保持初值。
这里 Ω 可直接取 Rect.openSet；不是只在预先选定的数值空间点验证。
混合求导由实际历史的光滑性证明，未作为本定理的输入条件。 -/
theorem five_invariants_on_Icc (Ω : Set Point) (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn Ω T ε κ τ μ p r F) :
    ∀ t ∈ Icc 0 T, ∀ X ∈ Ω, InvariantsEqualInitial F (lift F μ u₀ q₀) ε κ τ p r t X := by
  intro t ht X hX
  have hφx : Continuous (fun s => (lift F μ u₀ q₀).φx s X) :=
    ((hregular.Hy_cont X).const_mul μ).sub
      (continuous_space_partial hregular.history_smooth X (1,0))
  have hφy : Continuous (fun s => (lift F μ u₀ q₀).φy s X) :=
    ((hregular.Hx_cont X).const_mul (-μ)).sub
      (continuous_space_partial hregular.history_smooth X (0,1))
  exact five_invariants_eq_initial ε κ τ μ T p r F u₀ q₀ X hT
    (hregular.E_cont X) (hregular.P_cont X) (hregular.Z1_cont X).continuousOn
    (hregular.Z2_cont X).continuousOn (hregular.Qx_cont X).continuousOn
    (hregular.Qy_cont X).continuousOn hφx.continuousOn hφy.continuousOn
    (fun s hs => hOriginal s hs X hX)
    (fun s _ => (lift_mixed_derivatives F u₀ hregular s X).1)
    (fun s _ => (lift_mixed_derivatives F u₀ hregular s X).2) ht

/-- V7 (2.5) 的全时段场兼容。只输入每个空间点的初始零不变量，
其余结论来自真实时间保持；允许 T=0，此时不使用内部方程。 -/
theorem compatible_lift_on_Icc (Ω : Set Point) (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn Ω T ε κ τ μ p r F)
    (hinitial : ∀ X ∈ Ω, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X) :
    ∀ t ∈ Icc 0 T, ∀ X ∈ Ω, CompatibleAt F (lift F μ u₀ q₀) ε κ τ p r t X := by
  intro t ht X hX
  exact compatibleAt_of_initial F _ ε κ τ p r t X
    (five_invariants_on_Icc Ω ε κ τ μ T p r F u₀ q₀ hT hregular hOriginal t ht X hX)
    (hinitial X hX)

/-- V7 命题 2.1 的原→primitive 完整场入口。
从原八方程、实际历史与初始兼容推出整个内部时空域的 (2.6)。
α=1 的 P 始终保留；没有要求 E、H 满足域外方程。 -/
theorem original_to_primitive (Ω : Set Point) (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn Ω T ε κ τ μ p r F)
    (hinitial : ∀ X ∈ Ω, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X) :
    PrimitiveOn Ω T ε κ τ μ p r (lift F μ u₀ q₀) := by
  intro t ht X hX
  have hcompatible := compatible_lift_on_Icc Ω ε κ τ μ T p r F u₀ q₀ hT hregular
    hOriginal hinitial t ⟨ht.1.le,ht.2.le⟩ X hX
  exact primitive_lift_at ε κ τ μ p r F u₀ q₀ t X
    (hregular.E_cont X) (hregular.P_cont X) (hOriginal t ht X hX) hcompatible
    (lift_mixed_derivatives F u₀ hregular t X).1 (lift_mixed_derivatives F u₀ hregular t X).2

/-- V7 命题 2.1 的 primitive→原八变量入口。
时间邻域兼容从开区间 PDE 获得；空间邻域 u_t=E 从 Ω 的开放性获得。
实际混合求导由 C∞ 定理证明，然后调用全部八方程的逐条恢复，不留下交换字段。 -/
theorem primitive_to_original (Ω : Set Point) (hΩ : IsOpen Ω)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (U : PrimitiveFields) (hμ : μ ≠ 0)
    (hsmooth : ContDiff ℝ ∞ (Function.uncurry U.u))
    (hPrimitive : PrimitiveOn Ω T ε κ τ μ p r U) :
    OriginalOn Ω T ε κ τ μ p r (reconstruct U ε μ p r) := by
  intro t ht X hX
  have htime : ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 T := isOpen_Ioo.mem_nhds ht
  have hnear : ∀ᶠ s in 𝓝 t, PrimitiveAt ε κ τ μ p r U s X :=
    htime.mono (fun s hs => hPrimitive s hs X hX)
  have hspace : ∀ᶠ Y in 𝓝 X, Y ∈ Ω := hΩ.mem_nhds hX
  have hnear_derivative : ∀ᶠ Y in 𝓝 X, HasDerivAt (fun s => U.u s Y) (U.E t Y) t :=
    hspace.mono (fun Y hY => (hPrimitive t ht Y hY).du)
  exact original_reconstruct_at ε κ τ μ p r U t X hμ (hPrimitive t ht X hX) hnear
    (LeanPML.Rectangle.hasDerivAt_spaceFDeriv_of_timeDeriv hsmooth t X (1,0) hnear_derivative)
    (LeanPML.Rectangle.hasDerivAt_spaceFDeriv_of_timeDeriv hsmooth t X (0,1) hnear_derivative)

/-- V7 (2.3) 初始 Debye 兼容的具体形式，允许非零 u₀、q₀。
与 InitialCompatible.debye 一致，绝不是默认两个历史初值为零。 -/
theorem initial_debye_lift (F : OriginalFields) (μ κ τ : ℝ) (u₀ q₀ : Point → ℝ) (X : Point) :
    invariantD (lift F μ u₀ q₀) κ τ 0 X = q₀ X+τ*F.P 0 X-κ*u₀ X := by
  simp [invariantD,lift,integralLift_initial]

/-- (2.3) 与 PEC：u₀ 在边界为零且 E 具有 PEC，则实际历史 u 也在边界为零。
积分只用 [0,t]⊆[0,T] 上的 E 值，没有扩大方程或边界的时间范围。 -/
theorem integralLift_zero_boundary (boundary : Set Point) (F : OriginalFields)
    (u₀ : Point → ℝ) (T : ℝ) (hPEC : OriginalPEC boundary T F)
    (hu₀ : ∀ X ∈ boundary, u₀ X = 0) :
    ∀ t ∈ Icc 0 T, ∀ X ∈ boundary, integralLift F.E u₀ t X = 0 := by
  intro t ht X hX
  have hintegral : (∫ s in (0 : ℝ)..t, F.E s X) = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hPEC s ⟨hs.1,hs.2.trans ht.2⟩ X hX
  simp only [integralLift,hu₀ X hX,hintegral,intervalIntegral.integral_zero,add_zero]

/-- 原 E 在重构中完全不变，因此 PEC 在反向映射中精确保留。 -/
theorem reconstruct_PEC (boundary : Set Point) (T ε μ : ℝ) (p r : ℝ → ℝ)
    (U : PrimitiveFields) (hPEC : ∀ t ∈ Icc 0 T, ∀ X ∈ boundary, U.E t X = 0) :
    OriginalPEC boundary T (reconstruct U ε μ p r) := hPEC

/-- V7 §5 的零区保持：p=r=0 时，primitive 辅助演化给出 φ_t=0。
还必须输入 φ(0)=0；仅有 p=r=0 本身不推出 φ=0。 -/
theorem primitive_zero_absorption_preserved (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (U : PrimitiveFields) (X : Point) (hT : 0 ≤ T) (hp : p X.1 = 0) (hr : r X.2 = 0)
    (hφx : ContinuousOn (fun t => U.φx t X) (Icc 0 T))
    (hφy : ContinuousOn (fun t => U.φy t X) (Icc 0 T))
    (hPrimitive : ∀ t ∈ Ioo 0 T, PrimitiveAt ε κ τ μ p r U t X)
    (hinitX : U.φx 0 X = 0) (hinitY : U.φy 0 X = 0) :
    ∀ t ∈ Icc 0 T, U.φx t X = 0 ∧ U.φy t X = 0 := by
  intro t ht
  constructor
  · have hconstant := LeanPML.Time.eq_initial_of_hasDerivAt_zero _ T hT hφx
      (fun s hs => (hPrimitive s hs).dφx.congr_deriv (by simp [hp,hr])) ht
    exact hconstant.trans hinitX
  · have hconstant := LeanPML.Time.eq_initial_of_hasDerivAt_zero _ T hT hφy
      (fun s hs => (hPrimitive s hs).dφy.congr_deriv (by simp [hp,hr])) ht
    exact hconstant.trans hinitY

/-- 五个实际不变量场的统一索引，0–4 依次为 D、Z1、Z2、X、Y。
仅用于将保持定理接入真实空间 L²；不是五个独立普通实数。 -/
def invariantField (F : OriginalFields) (U : PrimitiveFields) (ε κ τ : ℝ)
    (p r : ℝ → ℝ) : Fin 5 → Field
  | 0 => invariantD U κ τ
  | 1 => invariantZ1 F U ε p r
  | 2 => invariantZ2 F U p r
  | 3 => invariantX F U p
  | 4 => invariantY F U r

/-- (2.4) 的实际函数等式版本：每个不变量在整个 Ω 上等于初始函数。
“保持常数”指时间方向；该初始函数可以随空间位置改变。 -/
theorem invariant_fields_eqOn_initial (Ω : Set Point) (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn Ω T ε κ τ μ p r F)
    (i : Fin 5) {t : ℝ} (ht : t ∈ Icc 0 T) :
    EqOn (invariantField F (lift F μ u₀ q₀) ε κ τ p r i t)
      (invariantField F (lift F μ u₀ q₀) ε κ τ p r i 0) Ω := by
  intro X hX
  have hconstant := five_invariants_on_Icc Ω ε κ τ μ T p r F u₀ q₀ hT hregular hOriginal t ht X hX
  fin_cases i
  · exact hconstant.debye
  · exact hconstant.memory1
  · exact hconstant.memory2
  · exact hconstant.magneticX
  · exact hconstant.magneticY

/-- (2.4) 的实际矩形 L² 商类保持：先有整个矩形内部的函数等式，再有 a.e. 等式，
最后由 mathlib 的 MemLp.toLp_congr 得到代表元无关的 L² 等式。
hmemt/hmem0 是原实际函数的空间成员资格，不是保持结论；下条可由连续性构造它们。 -/
theorem five_invariants_toLp_eq_initial (D : LeanPML.Rectangle.Rect)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (i : Fin 5) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hmemt : MemLp (invariantField F (lift F μ u₀ q₀) ε κ τ p r i t) 2 D.measure)
    (hmem0 : MemLp (invariantField F (lift F μ u₀ q₀) ε κ τ p r i 0) 2 D.measure) :
    hmemt.toLp (invariantField F (lift F μ u₀ q₀) ε κ τ p r i t) =
      hmem0.toLp (invariantField F (lift F μ u₀ q₀) ε κ τ p r i 0) := by
  apply MemLp.toLp_congr
  change ∀ᵐ X ∂(volume.restrict D.openSet),
    invariantField F (lift F μ u₀ q₀) ε κ τ p r i t X =
      invariantField F (lift F μ u₀ q₀) ε κ τ p r i 0 X
  exact ae_restrict_of_forall_mem D.openSet_open.measurableSet
    (invariant_fields_eqOn_initial D.openSet ε κ τ μ T p r F u₀ q₀ hT hregular hOriginal i ht)

/-- 连续空间代表的实际 L² 版本：成员资格由整个紧致闭矩形上的连续性证明。
不要求不变量为零；本条包含五个方向，全部使用相同二维 Lebesgue 限制测度。 -/
theorem five_invariants_toLp_eq_of_continuous (D : LeanPML.Rectangle.Rect)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (i : Fin 5) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hcont_t : Continuous (invariantField F (lift F μ u₀ q₀) ε κ τ p r i t))
    (hcont_0 : Continuous (invariantField F (lift F μ u₀ q₀) ε κ τ p r i 0)) :
    (D.memLp_of_continuous hcont_t 2).toLp (invariantField F (lift F μ u₀ q₀) ε κ τ p r i t) =
      (D.memLp_of_continuous hcont_0 2).toLp (invariantField F (lift F μ u₀ q₀) ε κ τ p r i 0) :=
  five_invariants_toLp_eq_initial D ε κ τ μ T p r F u₀ q₀ hT hregular hOriginal i ht _ _

/-- 两组原场在给定时刻、整个空间域上的八分量相等。
此结论比单独核对某个数值点更强；供重构恢复和 L² a.e. 恢复使用。 -/
def OriginalFieldsEqOn (Ω : Set Point) (F G : OriginalFields) (t : ℝ) : Prop :=
  EqOn (F.E t) (G.E t) Ω ∧ EqOn (F.Hx t) (G.Hx t) Ω ∧
  EqOn (F.Hy t) (G.Hy t) Ω ∧ EqOn (F.P t) (G.P t) Ω ∧
  EqOn (F.Z1 t) (G.Z1 t) Ω ∧ EqOn (F.Z2 t) (G.Z2 t) Ω ∧
  EqOn (F.Qx t) (G.Qx t) Ω ∧ EqOn (F.Qy t) (G.Qy t) Ω

/-- 原→固定历史提升→重构，恢复全部八个实际场（含两个磁辅助场）。
μ≠0 仅用于恢复 H；全时段兼容由初始五个零值和已经证明的保持取得。 -/
theorem reconstruct_lift_eqOn (Ω : Set Point) (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T) (hμ : μ ≠ 0)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn Ω T ε κ τ μ p r F)
    (hinitial : ∀ X ∈ Ω, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    OriginalFieldsEqOn Ω (reconstruct (lift F μ u₀ q₀) ε μ p r) F t := by
  have hcompatible := compatible_lift_on_Icc Ω ε κ τ μ T p r F u₀ q₀ hT hregular hOriginal hinitial t ht
  refine ⟨fun _ _ => rfl, ?_, ?_, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro X _; dsimp [reconstruct,lift]; field_simp
  · intro X _; dsimp [reconstruct,lift]; field_simp
  · intro X hX; exact (hcompatible X hX).memory1.symm
  · intro X hX; exact (hcompatible X hX).memory2.symm
  · intro X hX; exact (hcompatible X hX).magneticX.symm
  · intro X hX; exact (hcompatible X hX).magneticY.symm

/-- 固定 u₀、q₀ 的反向历史恢复：实际 primitive 的 u、q 等于重构原场的积分提升。
闭区间连续+内部真实导数足够，T=0 同样适用；没有默认 u₀=q₀=0。 -/
theorem lift_reconstruct_histories (Ω : Set Point) (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (U : PrimitiveFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T)
    (hPrimitive : PrimitiveOn Ω T ε κ τ μ p r U)
    (hE : ∀ X ∈ Ω, Continuous (fun t => U.E t X))
    (hP : ∀ X ∈ Ω, Continuous (fun t => U.P t X))
    (hu : ∀ X ∈ Ω, ContinuousOn (fun t => U.u t X) (Icc 0 T))
    (hq : ∀ X ∈ Ω, ContinuousOn (fun t => U.q t X) (Icc 0 T))
    (hinitU : ∀ X ∈ Ω, U.u 0 X = u₀ X) (hinitQ : ∀ X ∈ Ω, U.q 0 X = q₀ X) :
    ∀ t ∈ Icc 0 T,
      EqOn ((lift (reconstruct U ε μ p r) μ u₀ q₀).u t) (U.u t) Ω ∧
      EqOn ((lift (reconstruct U ε μ p r) μ u₀ q₀).q t) (U.q t) Ω := by
  intro t ht
  constructor
  · intro X hX
    exact integralLift_eq_of_initial_derivative U.E U.u u₀ T X hT (hE X hX) (hu X hX)
      (fun s hs => (hPrimitive s hs X hX).du) (hinitU X hX) ht
  · intro X hX
    exact integralLift_eq_of_initial_derivative U.P U.q q₀ T X hT (hP X hX) (hq X hX)
      (fun s hs => (hPrimitive s hs X hX).dq) (hinitQ X hX) ht

/-- 两组实际 primitive 场在 Ω 上的八槽相等，供固定初值映射恢复使用。 -/
def PrimitiveFieldsEqOn (Ω : Set Point) (U V : PrimitiveFields) (t : ℝ) : Prop :=
  EqOn (U.u t) (V.u t) Ω ∧ EqOn (U.E t) (V.E t) Ω ∧ EqOn (U.P t) (V.P t) Ω ∧
  EqOn (U.q t) (V.q t) Ω ∧ EqOn (U.Λx t) (V.Λx t) Ω ∧ EqOn (U.Λy t) (V.Λy t) Ω ∧
  EqOn (U.φx t) (V.φx t) Ω ∧ EqOn (U.φy t) (V.φy t) Ω

/-- 固定 u₀、q₀ 后，primitive→原变量→积分提升恢复全部 primitive 场。
历史在闭区间恢复；φ 的恢复在方程域 (0,T) 使用空间兼容。
实际历史函数先在 Ω 上相等，开放性再保证它们的真实空间偏导相等。 -/
theorem lift_reconstruct_eqOn (Ω : Set Point) (hΩ : IsOpen Ω)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (U : PrimitiveFields) (u₀ q₀ : Point → ℝ)
    (hT : 0 ≤ T) (hμ : μ ≠ 0) (hPrimitive : PrimitiveOn Ω T ε κ τ μ p r U)
    (hE : ∀ X ∈ Ω, Continuous (fun t => U.E t X))
    (hP : ∀ X ∈ Ω, Continuous (fun t => U.P t X))
    (hu : ∀ X ∈ Ω, ContinuousOn (fun t => U.u t X) (Icc 0 T))
    (hq : ∀ X ∈ Ω, ContinuousOn (fun t => U.q t X) (Icc 0 T))
    (hinitU : ∀ X ∈ Ω, U.u 0 X = u₀ X) (hinitQ : ∀ X ∈ Ω, U.q 0 X = q₀ X)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    PrimitiveFieldsEqOn Ω (lift (reconstruct U ε μ p r) μ u₀ q₀) U t := by
  have hhistory := lift_reconstruct_histories Ω ε κ τ μ T p r U u₀ q₀ hT
    hPrimitive hE hP hu hq hinitU hinitQ t ⟨ht.1.le,ht.2.le⟩
  have hgradient (X : Point) (hX : X ∈ Ω) :
      fderiv ℝ ((lift (reconstruct U ε μ p r) μ u₀ q₀).u t) X = fderiv ℝ (U.u t) X := by
    have hspace : ∀ᶠ Y in 𝓝 X, Y ∈ Ω := hΩ.mem_nhds hX
    have hnear : ((lift (reconstruct U ε μ p r) μ u₀ q₀).u t) =ᶠ[𝓝 X] U.u t :=
      hspace.mono (fun Y hY => hhistory.1 hY)
    exact hnear.fderiv_eq
  refine ⟨hhistory.1,fun _ _ => rfl,fun _ _ => rfl,hhistory.2,?_,?_,?_,?_⟩
  · intro X _; dsimp [lift,reconstruct]; field_simp
  · intro X _; dsimp [lift,reconstruct]; field_simp
  · intro X hX
    have hdx := congrArg (fun A : Point →L[ℝ] ℝ => A (1,0)) (hgradient X hX)
    change spaceDx (integralLift U.E u₀) t X = spaceDx U.u t X at hdx
    dsimp only [lift,reconstruct]
    rw [hdx]
    have hflux := (hPrimitive t ht X hX).fluxX
    field_simp
    nlinarith only [hflux]
  · intro X hX
    have hdy := congrArg (fun A : Point →L[ℝ] ℝ => A (0,1)) (hgradient X hX)
    change spaceDy (integralLift U.E u₀) t X = spaceDy U.u t X at hdy
    dsimp only [lift,reconstruct]
    rw [hdy]
    have hflux := (hPrimitive t ht X hX).fluxY
    field_simp
    nlinarith only [hflux]

/-- (2.2) 的具体矩形 PEC：四条外边全部为零，包含时间端点。 -/
def OriginalRectPEC (D : LeanPML.Rectangle.Rect) (T : ℝ) (F : OriginalFields) : Prop :=
  ∀ t ∈ Icc 0 T, LeanPML.Rectangle.ZeroBoundary D (F.E t)

/-- 实际历史积分保留矩形的全部四边零迹；u₀ 的零边界不可省略。
这条是具体边界取值证明，未将目标边界保持作为正则性字段。 -/
theorem integralLift_rect_zeroBoundary (D : LeanPML.Rectangle.Rect) (T : ℝ)
    (F : OriginalFields) (u₀ : Point → ℝ)
    (hPEC : OriginalRectPEC D T F) (hu₀ : LeanPML.Rectangle.ZeroBoundary D u₀) :
    ∀ t ∈ Icc 0 T, LeanPML.Rectangle.ZeroBoundary D (integralLift F.E u₀ t) := by
  have hat (X : Point) (hinit : u₀ X = 0) (hzero : ∀ s ∈ Icc 0 T, F.E s X = 0)
      (t : ℝ) (ht : t ∈ Icc 0 T) : integralLift F.E u₀ t X = 0 := by
    apply integralLift_zero_boundary {X} F u₀ T ?_ ?_ t ht X (by simp)
    · intro s hs Y hY
      have hYX : Y = X := Set.mem_singleton_iff.mp hY
      simpa only [hYX] using hzero s hs
    · intro Y hY
      have hYX : Y = X := Set.mem_singleton_iff.mp hY
      simpa only [hYX] using hinit
  intro t ht
  exact ⟨fun y hy => hat _ (hu₀.1 y hy) (fun s hs => (hPEC s hs).1 y hy) t ht,
    fun y hy => hat _ (hu₀.2.1 y hy) (fun s hs => (hPEC s hs).2.1 y hy) t ht,
    fun x hx => hat _ (hu₀.2.2.1 x hx) (fun s hs => (hPEC s hs).2.2.1 x hx) t ht,
    fun x hx => hat _ (hu₀.2.2.2 x hx) (fun s hs => (hPEC s hs).2.2.2 x hx) t ht⟩

/-- 原→primitive 的具体矩形入口：方程在整个开矩形内部，PEC 在全部四条外边。
u₀ 可以非零，只要求其四边零值；q₀ 仍由初始 Debye 兼容限制，不默认等于零。 -/
theorem original_to_primitive_rectangle (D : LeanPML.Rectangle.Rect)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X ∈ D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hPEC : OriginalRectPEC D T F) (hu₀ : LeanPML.Rectangle.ZeroBoundary D u₀) :
    PrimitiveOn D.openSet T ε κ τ μ p r (lift F μ u₀ q₀) ∧
    (∀ t ∈ Icc 0 T, LeanPML.Rectangle.ZeroBoundary D ((lift F μ u₀ q₀).u t)) ∧
    (∀ t ∈ Icc 0 T, LeanPML.Rectangle.ZeroBoundary D ((lift F μ u₀ q₀).E t)) :=
  ⟨original_to_primitive D.openSet ε κ τ μ T p r F u₀ q₀ hT hregular hOriginal hinitial,
    integralLift_rect_zeroBoundary D T F u₀ hPEC hu₀,hPEC⟩

/-- primitive→原系统的具体矩形入口，恢复全部八方程且完整保留 PEC。 -/
theorem primitive_to_original_rectangle (D : LeanPML.Rectangle.Rect)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (U : PrimitiveFields) (hμ : μ ≠ 0)
    (hsmooth : ContDiff ℝ ∞ (Function.uncurry U.u))
    (hPrimitive : PrimitiveOn D.openSet T ε κ τ μ p r U)
    (hPEC : ∀ t ∈ Icc 0 T, LeanPML.Rectangle.ZeroBoundary D (U.E t)) :
    OriginalOn D.openSet T ε κ τ μ p r (reconstruct U ε μ p r) ∧
      OriginalRectPEC D T (reconstruct U ε μ p r) :=
  ⟨primitive_to_original D.openSet D.openSet_open ε κ τ μ T p r U hμ hsmooth hPrimitive,hPEC⟩

/-- V7 §5 的零区结论在原变量路径上的入口。
非负 p,r 与 a=0 推出 p=r=0；初始 φ=0 再经真实零导数保持到整个闭区间。
原层五个兼容常数来自初值，不能把 a=0 单独解释为辅助场自动为零。 -/
theorem original_zero_region_preserved (Ω : Set Point) (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (hT : 0 ≤ T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn Ω T ε κ τ μ p r F)
    (hinitial : ∀ X ∈ Ω, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (X : Point) (hX : X ∈ Ω) (hp : 0 ≤ p X.1) (hr : 0 ≤ r X.2)
    (ha : p X.1+r X.2 = 0)
    (hinitX : (lift F μ u₀ q₀).φx 0 X = 0) (hinitY : (lift F μ u₀ q₀).φy 0 X = 0) :
    ∀ t ∈ Icc 0 T, (lift F μ u₀ q₀).φx t X = 0 ∧ (lift F μ u₀ q₀).φy t X = 0 := by
  have hp_zero : p X.1 = 0 := by linarith
  have hr_zero : r X.2 = 0 := by linarith
  have hPrimitive := original_to_primitive Ω ε κ τ μ T p r F u₀ q₀ hT hregular hOriginal hinitial
  have hφx : Continuous (fun s => (lift F μ u₀ q₀).φx s X) :=
    ((hregular.Hy_cont X).const_mul μ).sub (continuous_space_partial hregular.history_smooth X (1,0))
  have hφy : Continuous (fun s => (lift F μ u₀ q₀).φy s X) :=
    ((hregular.Hx_cont X).const_mul (-μ)).sub (continuous_space_partial hregular.history_smooth X (0,1))
  exact primitive_zero_absorption_preserved ε κ τ μ T p r _ X hT hp_zero hr_zero
    hφx.continuousOn hφy.continuousOn (fun t ht => hPrimitive t ht X hX) hinitX hinitY

end LeanPML.PML.Concrete
