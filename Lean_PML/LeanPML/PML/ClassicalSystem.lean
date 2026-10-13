import LeanPML.PML.OriginalAssembly

/-!
# V7 (2.1)–(2.6)：带实际空间可导证据的古典解包装

`fderiv` 是总函数：仅写出含 `spaceDx`、`spaceDy` 的等式，并不自动证明
空间可导。旧 `OriginalOn` / `PrimitiveOn` 因而保留为低层方程谓词；本文件
另列真正的 `DifferentiableAt` 证据，再给古典解双向转换及能量路径装配。

原方程只对 E、Hx、Hy 作空间求导；primitive 侧只需 u、E、Λx、Λy。
不要求 P、Z、Q 等未被空间微分的槽全部可导。PDE 和下列空间要求均仅在
`(0,T) × Ω` 上成立；时间和加权空间的既有正则性要求仍明确列在桥接入口。
建议读 `OriginalClassicalOn` → `original_to_primitive_classical` →
`originalClassicalFiniteIntervalProblem_of_liftIdentified`。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
open LeanPML.Rectangle LeanPML.Analysis
namespace LeanPML.PML.Concrete

/-- (2.1) 实际使用的三类空间导数证据。
输入函数、时间、空间点固定；输出不是导数值名称，而是真正的空间可导性。 -/
structure OriginalSpatialAt (F : OriginalFields) (t : ℝ) (X : Point) : Prop where
  E : DifferentiableAt ℝ (F.E t) X
  Hx : DifferentiableAt ℝ (F.Hx t) X
  Hy : DifferentiableAt ℝ (F.Hy t) X

/-- 原空间正则性仅要求在实际 PDE 的开时间区间、空间内部。 -/
def OriginalSpatialOn (Ω : Set Point) (T : ℝ) (F : OriginalFields) : Prop :=
  ∀ t ∈ Ioo 0 T, ∀ X ∈ Ω, OriginalSpatialAt F t X

/-- (2.1) 的古典解谓词：八条真实时间方程，加实际空间可导证据。
只把原 PDE 与其可导性放进字段；不含兼容保持、能量律、耗散或等价结论。 -/
structure OriginalClassicalOn (Ω : Set Point) (T ε κ τ μ : ℝ)
    (p r : ℝ → ℝ) (F : OriginalFields) : Prop where
  equations : OriginalOn Ω T ε κ τ μ p r F
  spatial : OriginalSpatialOn Ω T F

/-- (2.6) 所需的空间可导性：u 提供梯度，Λ 提供散度，E 用于反向磁场方程。
没有要求普通 L² 场天然可导，也没有把梯度当作全 L² 上的有界算子。 -/
structure PrimitiveSpatialAt (U : PrimitiveFields) (t : ℝ) (X : Point) : Prop where
  u : DifferentiableAt ℝ (U.u t) X
  E : DifferentiableAt ℝ (U.E t) X
  Λx : DifferentiableAt ℝ (U.Λx t) X
  Λy : DifferentiableAt ℝ (U.Λy t) X

/-- primitive 空间正则性采用与原方程完全相同的时空域。 -/
def PrimitiveSpatialOn (Ω : Set Point) (T : ℝ) (U : PrimitiveFields) : Prop :=
  ∀ t ∈ Ioo 0 T, ∀ X ∈ Ω, PrimitiveSpatialAt U t X

/-- (2.6) 的古典解包装；空间/极化兼容仍是 primitive 方程的状态约束。
原→primitive 定理将从原初值证明这些约束，而不是把它们塞入原解定义。 -/
structure PrimitiveClassicalOn (Ω : Set Point) (T ε κ τ μ : ℝ)
    (p r : ℝ → ℝ) (U : PrimitiveFields) : Prop where
  equations : PrimitiveOn Ω T ε κ τ μ p r U
  spatial : PrimitiveSpatialOn Ω T U

/-- 从真实空间可导推出坐标切片的真实 x 导数。
由 `spaceDx` 定义推出，原文未单列；说明总定义 `fderiv` 何时确实代表偏导。 -/
theorem hasDerivAt_spaceDx_of_differentiable (F : Field) (t : ℝ) (X : Point)
    (hspace : DifferentiableAt ℝ (F t) X) :
    HasDerivAt (fun x => F t (x,X.2)) (spaceDx F t X) X.1 := by
  have hline : HasDerivAt (fun x : ℝ => (x,X.2)) (1,0) X.1 :=
    (hasDerivAt_id X.1).prodMk (hasDerivAt_const X.1 X.2)
  exact hspace.hasFDerivAt.comp_hasDerivAt X.1 hline

/-- 同一切片论证给出真实 y 偏导，不能只由 `spaceDy` 这个名字推断。 -/
theorem hasDerivAt_spaceDy_of_differentiable (F : Field) (t : ℝ) (X : Point)
    (hspace : DifferentiableAt ℝ (F t) X) :
    HasDerivAt (fun y => F t (X.1,y)) (spaceDy F t X) X.2 := by
  have hline : HasDerivAt (fun y : ℝ => (X.1,y)) (0,1) X.2 :=
    (hasDerivAt_const X.2 X.1).prodMk (hasDerivAt_id X.2)
  exact hspace.hasFDerivAt.comp_hasDerivAt X.2 hline

/-- (2.1) 的古典包装提供四个原方程实际出现的空间切片导数。
这条会在最终桥接中实例化，核查 E_x/E_y/Hx_y/Hy_x 都有真实证据。 -/
theorem OriginalClassicalOn.spatial_derivatives
    {Ω : Set Point} {T ε κ τ μ : ℝ} {p r : ℝ → ℝ} {F : OriginalFields}
    (hclassical : OriginalClassicalOn Ω T ε κ τ μ p r F)
    {t : ℝ} (ht : t∈Ioo 0 T) {X : Point} (hX : X∈Ω) :
    HasDerivAt (fun x => F.E t (x,X.2)) (spaceDx F.E t X) X.1 ∧
    HasDerivAt (fun y => F.E t (X.1,y)) (spaceDy F.E t X) X.2 ∧
    HasDerivAt (fun y => F.Hx t (X.1,y)) (spaceDy F.Hx t X) X.2 ∧
    HasDerivAt (fun x => F.Hy t (x,X.2)) (spaceDx F.Hy t X) X.1 := by
  have hspace : OriginalSpatialAt F t X := hclassical.spatial t ht X hX
  exact ⟨hasDerivAt_spaceDx_of_differentiable F.E t X hspace.E,
    hasDerivAt_spaceDy_of_differentiable F.E t X hspace.E,
    hasDerivAt_spaceDy_of_differentiable F.Hx t X hspace.Hx,
    hasDerivAt_spaceDx_of_differentiable F.Hy t X hspace.Hy⟩

/-- 固定时间切片的空间可导性由实际联合光滑性推出。
由 (6.6) 所选强正则性推出，原文未单列；下游给实际历史 u 使用。 -/
theorem differentiableAt_space_of_joint_smooth (F : Field)
    (hsmooth : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) (X : Point) :
    DifferentiableAt ℝ (F t) X := by
  have hslice : ContDiff ℝ ∞ (F t) := hsmooth.comp (contDiff_const.prodMk contDiff_id)
  exact hslice.differentiable (by simp) X

/-- (2.3) 提升的空间正则性：u 来自实际历史的联合光滑性；
E 直接继承，Λ=(μHy,-μHx) 由常数乘法保留可导性。不需要除以 μ。 -/
theorem lift_spatialOn (Ω : Set Point) (T μ : ℝ) (F : OriginalFields)
    (u₀ q₀ : Point → ℝ) (hspace : OriginalSpatialOn Ω T F)
    (hregular : OriginalLiftRegular F u₀) :
    PrimitiveSpatialOn Ω T (lift F μ u₀ q₀) := by
  intro t ht X hX
  have horiginal : OriginalSpatialAt F t X := hspace t ht X hX
  exact ⟨differentiableAt_space_of_joint_smooth (integralLift F.E u₀)
      hregular.history_smooth t X, horiginal.E,
    horiginal.Hy.const_mul μ, horiginal.Hx.const_mul (-μ)⟩

/-- V7 命题 2.1 的古典原→primitive 入口。
五不变量保持和全部 primitive 方程复用旧证明；新部分同时交付实际空间可导性。
初值兼容仅要求 t=0；PDE 与空间要求均不扩展到域外。 -/
theorem original_to_primitive_classical (Ω : Set Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (hT : 0≤T) (hregular : OriginalLiftRegular F u₀)
    (hclassical : OriginalClassicalOn Ω T ε κ τ μ p r F)
    (hinitial : ∀ X∈Ω, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X) :
    PrimitiveClassicalOn Ω T ε κ τ μ p r (lift F μ u₀ q₀) :=
  ⟨original_to_primitive Ω ε κ τ μ T p r F u₀ q₀ hT hregular hclassical.equations hinitial,
    lift_spatialOn Ω T μ F u₀ q₀ hclassical.spatial hregular⟩

/-- 重构场的空间正则性。仅 E、Hx、Hy 被原方程空间微分，
故不要求 pφ、rφ 或其他辅助槽的空间可导性；没有额外系数求导。 -/
theorem reconstruct_spatialOn (Ω : Set Point) (T ε μ : ℝ) (p r : ℝ → ℝ)
    (U : PrimitiveFields) (hspace : PrimitiveSpatialOn Ω T U) :
    OriginalSpatialOn Ω T (reconstruct U ε μ p r) := by
  intro t ht X hX
  have hprimitive : PrimitiveSpatialAt U t X := hspace t ht X hX
  exact ⟨hprimitive.E,hprimitive.Λy.const_mul (-1/μ),hprimitive.Λx.const_mul (1/μ)⟩

/-- V7 命题 2.1 的古典 primitive→原系统入口。
开放时空邻域和 u 联合光滑性负责真实混合求导；μ≠0 只在磁场重构中使用。
旧证明恢复全部八条真实时间方程，本条补上它们需要的实际空间可导性。 -/
theorem primitive_to_original_classical (Ω : Set Point) (hΩ : IsOpen Ω)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (U : PrimitiveFields) (hμ : μ≠0)
    (hsmooth : ContDiff ℝ ∞ (Function.uncurry U.u))
    (hclassical : PrimitiveClassicalOn Ω T ε κ τ μ p r U) :
    OriginalClassicalOn Ω T ε κ τ μ p r (reconstruct U ε μ p r) :=
  ⟨primitive_to_original Ω hΩ ε κ τ μ T p r U hμ hsmooth hclassical.equations,
    reconstruct_spatialOn Ω T ε μ p r U hclassical.spatial⟩

/-- 已有 SmoothStateData/LiftIdentified 实际推出原场空间可导，而不是重新假设。
E 对应光滑 V；μHy、−μHx 对应光滑 Λ。μ≠0 允许反向常数缩放。
不要求原场未被求空间导数的 P、Z、Q 一概联合光滑。 -/
theorem originalSpatialOn_of_liftIdentified (Ω : Set Point) (T : ℝ)
    (B : SmoothStateData) (F : OriginalFields) (μ : ℝ) (u₀ q₀ : Point → ℝ)
    (hid : LiftIdentified B F μ u₀ q₀) (hμ : μ≠0) :
    OriginalSpatialOn Ω T F := by
  intro t _ X _
  have hE : F.E t = (B.V.value t : Point → ℝ) := (congrFun hid.V t).symm
  have hHx : F.Hx t = (fun Y => (-1/μ)*B.Λy.value t Y) := by
    funext Y
    have hΛ := congrFun (congrFun hid.Λy t) Y
    change B.Λy.value t Y = -μ*F.Hx t Y at hΛ
    rw [hΛ]
    field_simp
  have hHy : F.Hy t = (fun Y => (1/μ)*B.Λx.value t Y) := by
    funext Y
    have hΛ := congrFun (congrFun hid.Λx t) Y
    change B.Λx.value t Y = μ*F.Hy t Y at hΛ
    rw [hΛ]
    field_simp
  constructor
  · rw [hE]; exact (B.V.value t).differentiable X
  · rw [hHx]; exact ((B.Λy.value t).differentiable X).const_mul (-1/μ)
  · rw [hHy]; exact ((B.Λx.value t).differentiable X).const_mul (1/μ)

/-- 光滑原路径的正式古典解包装：方程输入仍为原八方程；空间证据是输出。 -/
theorem originalClassicalOn_of_liftIdentified (Ω : Set Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (B : SmoothStateData) (hid : LiftIdentified B F μ u₀ q₀) (hμ : μ≠0)
    (hOriginal : OriginalOn Ω T ε κ τ μ p r F) :
    OriginalClassicalOn Ω T ε κ τ μ p r F :=
  ⟨hOriginal,originalSpatialOn_of_liftIdentified Ω T B F μ u₀ q₀ hid hμ⟩

/-- 所选光滑 primitive 场本身的空间导数均有证据，独立于其是否满足 PDE。 -/
theorem smoothPrimitiveFields_spatialOn (Ω : Set Point) (T : ℝ) (B : SmoothStateData) :
    PrimitiveSpatialOn Ω T (smoothPrimitiveFields B) := by
  intro t _ X _
  exact ⟨(B.v.value t).differentiable X,(B.V.value t).differentiable X,
    (B.Λx.value t).differentiable X,(B.Λy.value t).differentiable X⟩

/-- 具体矩形的古典原→primitive，同时保留整个外边界 PEC 和历史零迹。 -/
theorem original_to_primitive_classical_rectangle (D : Rect)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (hT : 0≤T) (hregular : OriginalLiftRegular F u₀)
    (hclassical : OriginalClassicalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀) :
    PrimitiveClassicalOn D.openSet T ε κ τ μ p r (lift F μ u₀ q₀) ∧
    (∀ t∈Icc 0 T, ZeroBoundary D ((lift F μ u₀ q₀).u t)) ∧
    (∀ t∈Icc 0 T, ZeroBoundary D ((lift F μ u₀ q₀).E t)) :=
  ⟨original_to_primitive_classical D.openSet ε κ τ μ T p r F u₀ q₀ hT hregular hclassical hinitial,
    integralLift_rect_zeroBoundary D T F u₀ hPEC hu₀,hPEC⟩

/-- 具体矩形的古典 primitive→原系统，恢复全部八方程、空间可导与四边 PEC。 -/
theorem primitive_to_original_classical_rectangle (D : Rect)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (U : PrimitiveFields) (hμ : μ≠0)
    (hsmooth : ContDiff ℝ ∞ (Function.uncurry U.u))
    (hclassical : PrimitiveClassicalOn D.openSet T ε κ τ μ p r U)
    (hPEC : ∀ t∈Icc 0 T, ZeroBoundary D (U.E t)) :
    OriginalClassicalOn D.openSet T ε κ τ μ p r (reconstruct U ε μ p r) ∧
    OriginalRectPEC D T (reconstruct U ε μ p r) :=
  ⟨primitive_to_original_classical D.openSet D.openSet_open ε κ τ μ T p r U hμ hsmooth hclassical,hPEC⟩



/-- 古典原路径进入具体矩形能量框架。
先调用古典原→primitive（含实际空间可导证据），再使用同一光滑代表转换为
实际 L² 演化；其余兼容、零区和闭区间静态结果仍从原初值与演化推出。
这不是对低层总定义 fderiv 方程的无条件 PDE 解释，也不发布最终能量主定理。 -/
def originalClassicalFiniteIntervalProblem (D : Rect) (C : SpatialAbsorption Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T)
    (hp : ∀ X, C.p X=p X.1) (hr : ∀ X, C.r X=r X.2)
    (hregular : OriginalLiftRegular F u₀)
    (hclassical : OriginalClassicalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hφzero : ∀ X∈D.openSet, C.a X=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀)
    (hdegenerate : T=0 → InitialDerivativeCompatible D C B κ τ) :
    FiniteIntervalProblemConditional (greenDomain D) C ε κ τ μ
      (poincareConstant D) T (poincare_estimate D) := by
  have hprimitiveClassical :
      PrimitiveClassicalOn D.openSet T ε κ τ μ p r (smoothPrimitiveFields B) := by
    rw [smoothPrimitiveFields_eq_lift B F μ u₀ q₀ hid]
    exact original_to_primitive_classical D.openSet ε κ τ μ T p r F u₀ q₀
      hT hregular hclassical hinitial
  have hzero : SmoothZeroOn D C B (Ioo 0 T) :=
    original_smoothZeroOn D C ε κ τ μ T p r F u₀ q₀ B hid hT hp hr hregular
      hclassical.equations hinitial hφzero
  have hstatic := original_static_closed D C ε κ τ μ T p r F u₀ q₀ B hid hT hp hr
    hregular hclassical.equations hinitial hφzero hPEC hu₀ hdegenerate
  exact finiteIntervalProblem_of_smooth D C B reg ε κ τ μ T hT p r hp hr
    hprimitiveClassical.equations hzero (fun t ht => (hstatic t ht).1)
    (fun t ht => (hstatic t ht).2)

/-- 从原八方程和已有光滑坐标识别出发的推荐古典桥接。
空间可导性不是新增未证输入：由实际 E、μHy、−μHx 的光滑代表与 μ≠0 推出，
然后调用上面的古典入口。方程仍只要求在 `(0,T)×Ω` 成立。 -/
def originalClassicalFiniteIntervalProblem_of_liftIdentified
    (D : Rect) (C : SpatialAbsorption Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T) (hμ : μ≠0)
    (hp : ∀ X, C.p X=p X.1) (hr : ∀ X, C.r X=r X.2)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hφzero : ∀ X∈D.openSet, C.a X=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀)
    (hdegenerate : T=0 → InitialDerivativeCompatible D C B κ τ) :
    FiniteIntervalProblemConditional (greenDomain D) C ε κ τ μ
      (poincareConstant D) T (poincare_estimate D) :=
  originalClassicalFiniteIntervalProblem D C ε κ τ μ T p r F u₀ q₀ B reg hid hT hp hr
    hregular (originalClassicalOn_of_liftIdentified D.openSet ε κ τ μ T p r F u₀ q₀ B hid hμ hOriginal)
    hinitial hφzero hPEC hu₀ hdegenerate

/-- 古典桥接保留积分平衡所需的实际 P_tt 的 L² 连续性。
该连续性来自所选加权/一致范数正则性，未将耗散可积或积分平衡作为输入。 -/
theorem originalClassicalFiniteIntervalProblem_second_R_continuous
    (D : Rect) (C : SpatialAbsorption Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T)
    (hp : ∀ X, C.p X=p X.1) (hr : ∀ X, C.r X=r X.2)
    (hregular : OriginalLiftRegular F u₀)
    (hclassical : OriginalClassicalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hφzero : ∀ X∈D.openSet, C.a X=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀)
    (hdegenerate : T=0 → InitialDerivativeCompatible D C B κ τ) :
    ContinuousOn (fun t => ((originalClassicalFiniteIntervalProblem D C ε κ τ μ T p r F
      u₀ q₀ B reg hid hT hp hr hregular hclassical hinitial hφzero hPEC hu₀ hdegenerate).path.second t).R)
      (Icc 0 T) :=
  (continuous_jet_L2 D B.R reg.R).2.2.continuousOn

end LeanPML.PML.Concrete
