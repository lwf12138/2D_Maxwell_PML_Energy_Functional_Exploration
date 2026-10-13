import LeanPML.PML.OriginalSystem

/-!
# V7 (2.3)–(2.6)：真实 primitive 场与五个时间不变量

u、q 由实际历史积分定义；λ 从磁场缩放，φ=λ−实际空间导数。
先保留任意初始不变量，再以初始零值推出重构关系。
两个磁辅助不变量使用原磁场方程和真实混合导数，不由符号命名推断。
下面低层定理可输入实际混合导数证据；Equivalence 的光滑入口将调用已证交换。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace LeanPML.PML.Concrete

/-- (2.6) 的实际 primitive 场；E 是明确速度场，须以 u_t=E 证据联系。 -/
structure PrimitiveFields where
  u : Field
  E : Field
  P : Field
  q : Field
  Λx : Field
  Λy : Field
  φx : Field
  φy : Field

/-- (2.3) 的固定初始原函数提升。λ 的方向是 (μHy,−μHx)，不可交换。 -/
def lift (F : OriginalFields) (μ : ℝ) (u₀ q₀ : Point → ℝ) : PrimitiveFields where
  u := integralLift F.E u₀
  E := F.E
  P := F.P
  q := integralLift F.P q₀
  Λx := fun t X => μ*F.Hy t X
  Λy := fun t X => -μ*F.Hx t X
  φx := fun t X => μ*F.Hy t X-spaceDx (integralLift F.E u₀) t X
  φy := fun t X => -μ*F.Hx t X-spaceDy (integralLift F.E u₀) t X

/-- (2.6) 中真实空间散度，两个分量均为实际坐标导数。 -/
def fluxDiv (U : PrimitiveFields) (t : ℝ) (X : Point) : ℝ :=
  spaceDx U.Λx t X + spaceDy U.Λy t X

/-- (2.6) 的完整逐点系统。φ 方程直接用 HasDerivAt 表达，
极化与空间关系是 primitive 本身的状态约束；原→primitive 时必须证明它们。
本结构没有最终能量率、耗散符号或双向等价字段。
fderiv 的出现本身不证明空间可导，古典版本由 ClassicalSystem 显式包装。 -/
structure PrimitiveAt (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (U : PrimitiveFields) (t : ℝ) (X : Point) : Prop where
  du : HasDerivAt (fun s => U.u s X) (U.E t X) t
  dq : HasDerivAt (fun s => U.q s X) (U.P t X) t
  dE : HasDerivAt (fun s => U.E s X) (dt U.E t X) t
  dP : HasDerivAt (fun s => U.P s X) (dt U.P t X) t
  main : μ*(ε*(dt U.E t X+(p X.1+r X.2)*U.E t X+(p X.1*r X.2)*U.u t X)+
    dt U.P t X+(p X.1+r X.2)*U.P t X+(p X.1*r X.2)*U.q t X) = fluxDiv U t X
  dφx : HasDerivAt (fun s => U.φx s X)
    ((r X.2-p X.1)*spaceDx U.u t X-p X.1*U.φx t X) t
  dφy : HasDerivAt (fun s => U.φy s X)
    ((p X.1-r X.2)*spaceDy U.u t X-r X.2*U.φy t X) t
  fluxX : U.Λx t X = spaceDx U.u t X+U.φx t X
  fluxY : U.Λy t X = spaceDy U.u t X+U.φy t X
  polar : U.q t X+τ*U.P t X = κ*U.u t X

/-- primitive 方程只在开时间区间、整个空间内部成立。 -/
def PrimitiveOn (Ω : Set Point) (T ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (U : PrimitiveFields) : Prop :=
  ∀ t ∈ Ioo 0 T, ∀ X ∈ Ω, PrimitiveAt ε κ τ μ p r U t X

/-- 常数空间缩放的真实偏导规则。mathlib 对零常数也正确处理，不除吸收系数。 -/
theorem spaceDx_const_mul (F : Field) (a t : ℝ) (X : Point) :
    spaceDx (fun s Y => a*F s Y) t X = a*spaceDx F t X := by
  change fderiv ℝ (a • F t) X (1,0) = _
  rw [fderiv_const_smul_field]
  rfl

/-- y 方向同样使用真实 Fréchet 导数，不依赖普通 L² 上的虚构梯度算子。 -/
theorem spaceDy_const_mul (F : Field) (a t : ℝ) (X : Point) :
    spaceDy (fun s Y => a*F s Y) t X = a*spaceDy F t X := by
  change fderiv ℝ (a • F t) X (0,1) = _
  rw [fderiv_const_smul_field]
  rfl

/-- (2.3) 的真实散度/旋度缩放，对任意 μ（包括零）均为定义性微积分恒等式。 -/
theorem fluxDiv_lift (F : OriginalFields) (μ : ℝ) (u₀ q₀ : Point → ℝ) (t : ℝ) (X : Point) :
    fluxDiv (lift F μ u₀ q₀) t X = μ*(spaceDx F.Hy t X-spaceDy F.Hx t X) := by
  change spaceDx (fun s Y => μ*F.Hy s Y) t X +
    spaceDy (fun s Y => -μ*F.Hx s Y) t X = _
  rw [spaceDx_const_mul, spaceDy_const_mul]
  ring

/-- V7 (2.4) 的五个不变量，都是实际时间函数。Cx、Cy 各用不同方向的 φ。 -/
def invariantD (U : PrimitiveFields) (κ τ : ℝ) (t : ℝ) (X : Point) :=
  U.q t X+τ*U.P t X-κ*U.u t X
/-- 第一个电辅助不变量。 -/
def invariantZ1 (F : OriginalFields) (U : PrimitiveFields) (ε : ℝ) (p r : ℝ → ℝ) (t : ℝ) (X : Point) :=
  F.Z1 t X+ε*(p X.1*r X.2)*U.u t X
/-- 第二个电辅助不变量。 -/
def invariantZ2 (F : OriginalFields) (U : PrimitiveFields) (p r : ℝ → ℝ) (t : ℝ) (X : Point) :=
  F.Z2 t X+(p X.1*r X.2)*U.q t X
/-- 磁辅助不变量 Cx=Qx−pφy。 -/
def invariantX (F : OriginalFields) (U : PrimitiveFields) (p : ℝ → ℝ) (t : ℝ) (X : Point) :=
  F.Qx t X-p X.1*U.φy t X
/-- 磁辅助不变量 Cy=Qy+rφx。 -/
def invariantY (F : OriginalFields) (U : PrimitiveFields) (r : ℝ → ℝ) (t : ℝ) (X : Point) :=
  F.Qy t X+r X.2*U.φx t X

/-- (2.4) 后未编号的两条 φ 时间导数。原始输入是 H 的 HasDerivAt、
两条磁场方程及实际 ∂t∂iu=∂iE 证据；减法求导由 φ=λ−∇u 得到。 -/
theorem magnetic_lift_derivatives (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (t : ℝ) (X : Point)
    (hOriginal : OriginalAt ε κ τ μ p r F t X)
    (hgradX : HasDerivAt (fun s => spaceDx (integralLift F.E u₀) s X) (spaceDx F.E t X) t)
    (hgradY : HasDerivAt (fun s => spaceDy (integralLift F.E u₀) s X) (spaceDy F.E t X) t) :
    HasDerivAt (fun s => (lift F μ u₀ q₀).φx s X)
      (-(p X.1-r X.2)*(lift F μ u₀ q₀).Λx t X+F.Qy t X) t ∧
    HasDerivAt (fun s => (lift F μ u₀ q₀).φy s X)
      ((p X.1-r X.2)*(lift F μ u₀ q₀).Λy t X-F.Qx t X) t := by
  constructor
  · apply ((hOriginal.dHy.const_mul μ).sub hgradX).congr_deriv
    dsimp [lift]
    nlinarith only [hOriginal.magneticY]
  · apply ((hOriginal.dHx.const_mul (-μ)).sub hgradY).congr_deriv
    dsimp [lift]
    nlinarith only [hOriginal.magneticX]

/-- (2.4) 两个磁不变量的真实零导数。辅助原方程与上一 φ 求导式抵消。
不要求 p,r 非零；因而物理区、边层和角层使用同一证明。 -/
theorem magnetic_invariants_hasDerivAt_zero (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (t : ℝ) (X : Point)
    (hOriginal : OriginalAt ε κ τ μ p r F t X)
    (hgradX : HasDerivAt (fun s => spaceDx (integralLift F.E u₀) s X) (spaceDx F.E t X) t)
    (hgradY : HasDerivAt (fun s => spaceDy (integralLift F.E u₀) s X) (spaceDy F.E t X) t) :
    HasDerivAt (fun s => invariantX F (lift F μ u₀ q₀) p s X) 0 t ∧
    HasDerivAt (fun s => invariantY F (lift F μ u₀ q₀) r s X) 0 t := by
  have hφ := magnetic_lift_derivatives ε κ τ μ p r F u₀ q₀ t X hOriginal hgradX hgradY
  constructor
  · apply (hOriginal.dQx.sub (hφ.2.const_mul (p X.1))).congr_deriv
    dsimp [lift]
    nlinarith only [hOriginal.auxiliaryX]
  · apply (hOriginal.dQy.add (hφ.1.const_mul (r X.2))).congr_deriv
    dsimp [lift]
    nlinarith only [hOriginal.auxiliaryY]

/-- (2.4) 五个初始常数的集合；先保留任意常数，不把它们预设为零。 -/
structure InvariantsEqualInitial (F : OriginalFields) (U : PrimitiveFields)
    (ε κ τ : ℝ) (p r : ℝ → ℝ) (t : ℝ) (X : Point) : Prop where
  debye : invariantD U κ τ t X = invariantD U κ τ 0 X
  memory1 : invariantZ1 F U ε p r t X = invariantZ1 F U ε p r 0 X
  memory2 : invariantZ2 F U p r t X = invariantZ2 F U p r 0 X
  magneticX : invariantX F U p t X = invariantX F U p 0 X
  magneticY : invariantY F U r t X = invariantY F U r 0 X

/-- 五个初始不变量为零，仅是初始时刻条件；全时段兼容由保持定理推出。 -/
structure InitialCompatible (F : OriginalFields) (U : PrimitiveFields)
    (ε κ τ : ℝ) (p r : ℝ → ℝ) (X : Point) : Prop where
  debye : invariantD U κ τ 0 X = 0
  memory1 : invariantZ1 F U ε p r 0 X = 0
  memory2 : invariantZ2 F U p r 0 X = 0
  magneticX : invariantX F U p 0 X = 0
  magneticY : invariantY F U r 0 X = 0

/-- (2.4) 的闭区间时间保持。这里所有函数都是实际场在 X 的时间切片；
三个旧不变量复用 v0.1.3，两个磁不变量由新零导数和常值接口推出。
连续性是端点正则性，不包含任何全时段兼容结论。 -/
theorem five_invariants_eq_initial (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (X : Point) (hT : 0 ≤ T)
    (hE : Continuous (fun t => F.E t X)) (hP : Continuous (fun t => F.P t X))
    (hZ1 : ContinuousOn (fun t => F.Z1 t X) (Icc 0 T))
    (hZ2 : ContinuousOn (fun t => F.Z2 t X) (Icc 0 T))
    (hQx : ContinuousOn (fun t => F.Qx t X) (Icc 0 T))
    (hQy : ContinuousOn (fun t => F.Qy t X) (Icc 0 T))
    (hφx : ContinuousOn (fun t => (lift F μ u₀ q₀).φx t X) (Icc 0 T))
    (hφy : ContinuousOn (fun t => (lift F μ u₀ q₀).φy t X) (Icc 0 T))
    (hOriginal : ∀ t ∈ Ioo 0 T, OriginalAt ε κ τ μ p r F t X)
    (hgradX : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => spaceDx (integralLift F.E u₀) s X) (spaceDx F.E t X) t)
    (hgradY : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => spaceDy (integralLift F.E u₀) s X) (spaceDy F.E t X) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    InvariantsEqualInitial F (lift F μ u₀ q₀) ε κ τ p r t X := by
  have hucont : ContinuousOn (fun t => integralLift F.E u₀ t X) (Icc 0 T) :=
    (continuous_integralLift F.E u₀ X hE).continuousOn
  have hqcont : ContinuousOn (fun t => integralLift F.P q₀ t X) (Icc 0 T) :=
    (continuous_integralLift F.P q₀ X hP).continuousOn
  constructor
  · exact LeanPML.PML.CD_eq_initial κ τ T _ _ _ _ hT hucont hqcont hP.continuousOn
      (fun s _ => hasDerivAt_integralLift F.E u₀ X hE s)
      (fun s _ => hasDerivAt_integralLift F.P q₀ X hP s)
      (fun s hs => ⟨dt F.P s X, (hOriginal s hs).dP, (hOriginal s hs).debye⟩) ht
  · exact LeanPML.PML.CZ1_eq_initial ε (p X.1*r X.2) T _ _ _ hT hucont hZ1
      (fun s _ => hasDerivAt_integralLift F.E u₀ X hE s)
      (fun s hs => (hOriginal s hs).dZ1.congr_deriv (hOriginal s hs).memory1) ht
  · exact LeanPML.PML.CZ2_eq_initial (p X.1*r X.2) T _ _ _ hT hqcont hZ2
      (fun s _ => hasDerivAt_integralLift F.P q₀ X hP s)
      (fun s hs => (hOriginal s hs).dZ2.congr_deriv (hOriginal s hs).memory2) ht
  · apply LeanPML.Time.eq_initial_of_hasDerivAt_zero _ T hT
      (hQx.sub (hφy.const_mul (p X.1))) ?_ ht
    intro s hs
    exact (magnetic_invariants_hasDerivAt_zero ε κ τ μ p r F u₀ q₀ s X
      (hOriginal s hs) (hgradX s hs) (hgradY s hs)).1
  · apply LeanPML.Time.eq_initial_of_hasDerivAt_zero _ T hT
      (hQy.add (hφx.const_mul (r X.2))) ?_ ht
    intro s hs
    exact (magnetic_invariants_hasDerivAt_zero ε κ τ μ p r F u₀ q₀ s X
      (hOriginal s hs) (hgradX s hs) (hgradY s hs)).2

end LeanPML.PML.Concrete
