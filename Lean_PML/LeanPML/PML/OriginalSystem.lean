import LeanPML.PML.TimeInvariants
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# V7 (2.1)–(2.3)：真实八变量与因果历史

场是实际函数 `ℝ → (ℝ × ℝ) → ℝ`，第一自变量为时间。
空间导数用 mathlib 的 `fderiv` 在坐标方向上取值；时间导数用 `deriv`，
每条原方程另有 `HasDerivAt` 证据，避免把总定义的 `deriv` 当作可导性。
本文件是底层方程表达式：`OriginalAt/On` 本身不保证空间可导；
正式古典 PDE 解释须经 `ClassicalSystem` 的空间可导包装。
`p(x), r(y)` 显式分离且不依赖时间。材料采用 α=1 的 Debye 模型，P 保留。
归一化与原材料一致：ε=ε₀ε∞、κ=ε₀(εₛ−ε∞)、μ=μ₀μᵣ，
p=σₓ/ε₀、r=σᵧ/ε₀；Z₁、Z₂ 就是原 Pz₁、Pz₂，未再缩放。
PDE 仅要求于 `(0,T) × Ω`；Ω 在最终矩形入口取整个开计算域。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace LeanPML.PML.Concrete

/-- V7 §1 的二维空间点；矩形边界与积分使用相同载体。 -/
abbrev Point := ℝ × ℝ
/-- 实际时空标量场。 -/
abbrev Field := ℝ → Point → ℝ
/-- 实际时间导数值；使用时必须另外提供可导证据。 -/
def dt (F : Field) (t : ℝ) (X : Point) : ℝ := deriv (fun s => F s X) t
/-- 实际 x 偏导：空间 Fréchet 导数作用于 (1,0)。 -/
def spaceDx (F : Field) (t : ℝ) (X : Point) : ℝ := fderiv ℝ (F t) X (1,0)
/-- 实际 y 偏导：空间 Fréchet 导数作用于 (0,1)。 -/
def spaceDy (F : Field) (t : ℝ) (X : Point) : ℝ := fderiv ℝ (F t) X (0,1)

/-- V7 (2.1) 的八个实际场；没有能量、不变量保持或等价结论字段。 -/
structure OriginalFields where
  E : Field
  Hx : Field
  Hy : Field
  P : Field
  Z1 : Field
  Z2 : Field
  Qx : Field
  Qy : Field

/-- (2.1) 一个时空点处的真实时间可导证据。dt 的三个槽是函数、点、时间；
这些证据把八个普通实数导数值与各自的真实函数绑定。 -/
structure OriginalHasDerivAt (F : OriginalFields) (t : ℝ) (X : Point) : Prop where
  dE : HasDerivAt (fun s => F.E s X) (dt F.E t X) t
  dHx : HasDerivAt (fun s => F.Hx s X) (dt F.Hx t X) t
  dHy : HasDerivAt (fun s => F.Hy s X) (dt F.Hy t X) t
  dP : HasDerivAt (fun s => F.P s X) (dt F.P t X) t
  dZ1 : HasDerivAt (fun s => F.Z1 s X) (dt F.Z1 t X) t
  dZ2 : HasDerivAt (fun s => F.Z2 s X) (dt F.Z2 t X) t
  dQx : HasDerivAt (fun s => F.Qx s X) (dt F.Qx t X) t
  dQy : HasDerivAt (fun s => F.Qy s X) (dt F.Qy t X) t

/-- V7 (2.1)，α=1 的完整八变量方程。p 仅读 x 坐标、r 仅读 y 坐标。
这里恒等式不额外要求材料正性；恢复 H 时才需要 μ≠0。
空间 fderiv 仍为总定义；相关 E/H 空间可导性由 ClassicalSystem 另行提供。
没有加入教学子系统 εE'=-P'，也没有在输入中要求全时段兼容。 -/
structure OriginalAt (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (t : ℝ) (X : Point) : Prop extends OriginalHasDerivAt F t X where
  electric : ε * dt F.E t X = spaceDx F.Hy t X - spaceDy F.Hx t X -
    ε * (p X.1+r X.2)*F.E t X - dt F.P t X - (p X.1+r X.2)*F.P t X + F.Z1 t X + F.Z2 t X
  magneticX : μ * dt F.Hx t X = -spaceDy F.E t X - μ*(r X.2-p X.1)*F.Hx t X + F.Qx t X
  magneticY : μ * dt F.Hy t X = spaceDx F.E t X - μ*(p X.1-r X.2)*F.Hy t X + F.Qy t X
  debye : τ * dt F.P t X + F.P t X = κ * F.E t X
  memory1 : dt F.Z1 t X = -ε*(p X.1*r X.2)*F.E t X
  memory2 : dt F.Z2 t X = -(p X.1*r X.2)*F.P t X
  auxiliaryX : dt F.Qx t X = -p X.1*F.Qx t X + μ*p X.1*(r X.2-p X.1)*F.Hx t X
  auxiliaryY : dt F.Qy t X = -r X.2*F.Qy t X + μ*r X.2*(p X.1-r X.2)*F.Hy t X

/-- 原方程仅要求在开时间区间及实际空间域 Ω 内成立。矩形主入口传整个 Ω。 -/
def OriginalOn (Ω : Set Point) (T ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) : Prop :=
  ∀ t ∈ Ioo 0 T, ∀ X ∈ Ω, OriginalAt ε κ τ μ p r F t X

/-- (2.2) 的实际边界取值条件。边界集合在矩形入口由四边给出，端点也保留。 -/
def OriginalPEC (boundary : Set Point) (T : ℝ) (F : OriginalFields) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ X ∈ boundary, F.E t X = 0

/-- (2.3) 的因果历史，f₀ 是任意固定初始原函数；未默认其为零。
空间点固定后做真实时间 intervalIntegral，不引入任意历史坐标。 -/
def integralLift (F : Field) (f₀ : Point → ℝ) : Field :=
  fun t X => f₀ X + ∫ s in (0 : ℝ)..t, F s X

/-- (2.3) 的初值：实际零长度区间积分为零。 -/
theorem integralLift_initial (F : Field) (f₀ : Point → ℝ) (X : Point) :
    integralLift F f₀ 0 X = f₀ X := by simp [integralLift]

/-- 由 (2.3) 推出，原文未单列：时间连续给历史的真实导数。
连续性仅是正则性输入；这个结论是 FTC，不是把 u_t=E 重新定义为假设。
连续函数的实际积分有限由 mathlib 同时提供。 -/
theorem hasDerivAt_integralLift (F : Field) (f₀ : Point → ℝ) (X : Point)
    (hcontinuous : Continuous (fun t => F t X)) (t : ℝ) :
    HasDerivAt (fun s => integralLift F f₀ s X) (F t X) t := by
  have hintegral := intervalIntegral.integral_hasDerivAt_right
    (hcontinuous.intervalIntegrable 0 t)
    hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter hcontinuous.continuousAt
  exact (hasDerivAt_const t (f₀ X)).add hintegral |>.congr_deriv (zero_add _)

/-- 历史的真实连续性来自上一导数定理，不假设能量或兼容保持。 -/
theorem continuous_integralLift (F : Field) (f₀ : Point → ℝ) (X : Point)
    (hcontinuous : Continuous (fun t => F t X)) :
    Continuous (fun t => integralLift F f₀ t X) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_integralLift F f₀ X hcontinuous t).continuousAt)

/-- 固定初始原函数的历史唯一性。闭区间连续、内部 u_t=E 已足够，
无需端点普通双侧导数；本条用于反向重构后的提升恢复。 -/
theorem integralLift_eq_of_initial_derivative (F u : Field) (f₀ : Point → ℝ)
    (T : ℝ) (X : Point) (hT : 0 ≤ T)
    (hF : Continuous (fun t => F t X))
    (hu : ContinuousOn (fun t => u t X) (Icc 0 T))
    (hdu : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => u s X) (F t X) t)
    (hinit : u 0 X = f₀ X) {t : ℝ} (ht : t ∈ Icc 0 T) :
    integralLift F f₀ t X = u t X := by
  have hconstant := LeanPML.Time.eq_initial_of_hasDerivAt_zero
    (fun s => integralLift F f₀ s X - u s X) T hT
    ((continuous_integralLift F f₀ X hF).continuousOn.sub hu)
    (fun s hs => ((hasDerivAt_integralLift F f₀ X hF s).sub (hdu s hs)).congr_deriv (sub_self _)) ht
  simpa only [integralLift_initial, hinit, sub_self, sub_eq_zero] using hconstant

end LeanPML.PML.Concrete
