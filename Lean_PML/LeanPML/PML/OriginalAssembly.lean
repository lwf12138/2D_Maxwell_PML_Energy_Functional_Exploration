import LeanPML.PML.Equivalence
import LeanPML.Rectangle.StatePaths
import LeanPML.Rectangle.InterfaceAssembly

/-!
# v0.4.4：原八变量、因果历史与实际能量路径的装配

建议按 `LiftIdentified` → `lift_velocity_coordinates` → `original_smoothZeroOn`
阅读。八个光滑时间槽必须逐一等于原场的真实历史提升；额外数据只规定
光滑、一致范数和加权范数正则性，不含 PDE、全时段兼容或能量结论。
本文件装配 v0.3 的输入接口，不发布 v0.5 的最终具体 PDE 主定理。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open LeanPML.Rectangle LeanPML.Analysis
namespace LeanPML.PML.Concrete

/-- V7 (2.3)/(6.3)：八个实际光滑时间槽与原场提升的定义识别。
u/q 是实际时间积分；Λ 为缩放磁场，φ 为 Λ 减实际梯度。
这些全函数相等只识别所选光滑延拓，不要求原 PDE 在域外成立。 -/
structure LiftIdentified (B : SmoothStateData) (F : OriginalFields)
    (μ : ℝ) (u₀ q₀ : Point → ℝ) : Prop where
  v : (fun t X => B.v.value t X) = (lift F μ u₀ q₀).u
  V : (fun t X => B.V.value t X) = (lift F μ u₀ q₀).E
  R : (fun t X => B.R.value t X) = (lift F μ u₀ q₀).P
  z : (fun t X => B.z.value t X) = (lift F μ u₀ q₀).q
  Λx : (fun t X => B.Λx.value t X) = (lift F μ u₀ q₀).Λx
  Λy : (fun t X => B.Λy.value t X) = (lift F μ u₀ q₀).Λy
  φx : (fun t X => B.φx.value t X) = (lift F μ u₀ q₀).φx
  φy : (fun t X => B.φy.value t X) = (lift F μ u₀ q₀).φy

/-- 八个坐标识别为同一个真实 primitive 场，没有新引入独立第二份状态。 -/
theorem smoothPrimitiveFields_eq_lift (B : SmoothStateData) (F : OriginalFields)
    (μ : ℝ) (u₀ q₀ : Point → ℝ) (hid : LiftIdentified B F μ u₀ q₀) :
    smoothPrimitiveFields B = lift F μ u₀ q₀ := by
  change PrimitiveFields.mk (fun t X => B.v.value t X) (fun t X => B.V.value t X)
    (fun t X => B.R.value t X) (fun t X => B.z.value t X)
    (fun t X => B.Λx.value t X) (fun t X => B.Λy.value t X)
    (fun t X => B.φx.value t X) (fun t X => B.φy.value t X) = _
  rw [hid.v,hid.V,hid.R,hid.z,hid.Λx,hid.Λy,hid.φx,hid.φy]


/-- 历史 FTC 与同一函数的导数唯一性给出 v.first=E、z.first=P。
不依赖 PDE，在技术延拓上成立；它将瞬时速度槽真正绑定到实际时间导数。 -/
theorem lift_velocity_coordinates (B : SmoothStateData) (F : OriginalFields)
    (μ : ℝ) (u₀ q₀ : Point → ℝ) (hid : LiftIdentified B F μ u₀ q₀)
    (hregular : OriginalLiftRegular F u₀) (t : ℝ) (X : Point) :
    B.v.first t X = B.V.value t X ∧ B.z.first t X = B.R.value t X := by
  have hv : HasDerivAt (fun s => B.v.value s X) (F.E t X) t := by
    have heq : (fun s => B.v.value s X) = (fun s => integralLift F.E u₀ s X) :=
      congrArg (fun G : Field => fun s => G s X) hid.v
    rw [heq]
    exact hasDerivAt_integralLift F.E u₀ X (hregular.E_cont X) t
  have hq : HasDerivAt (fun s => B.z.value s X) (F.P t X) t := by
    have heq : (fun s => B.z.value s X) = (fun s => integralLift F.P q₀ s X) :=
      congrArg (fun G : Field => fun s => G s X) hid.z
    rw [heq]
    exact hasDerivAt_integralLift F.P q₀ X (hregular.P_cont X) t
  have hE : B.V.value t X = F.E t X := congrFun (congrFun hid.V t) X
  have hP : B.R.value t X = F.P t X := congrFun (congrFun hid.R t) X
  exact ⟨(B.v.deriv_value t X).unique hv |>.trans hE.symm,
    (B.z.deriv_value t X).unique hq |>.trans hP.symm⟩

/-- 实际辅助函数在开时间区间恒为零，则其同源一、二阶导数也为零。
零值来自初值保持；本引理只使用真实 HasDerivAt 与邻域相等，不使用 PDE 名称。 -/
theorem jet_zero_derivatives (J : SmoothTimeJet) (T : ℝ) (X : Point)
    (hzero : ∀ s ∈ Ioo 0 T, J.value s X = 0) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    J.first t X = 0 ∧ J.second t X = 0 := by
  have hfirst (s : ℝ) (hs : s ∈ Ioo 0 T) : J.first s X = 0 := by
    have hnear : (fun r => J.value r X) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) :=
      (show ∀ᶠ r in 𝓝 s, r ∈ Ioo 0 T from isOpen_Ioo.mem_nhds hs).mono (fun r hr => hzero r hr)
    have hz : HasDerivAt (fun r => J.value r X) 0 s :=
      (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hnear
    exact (J.deriv_value s X).unique hz
  have hnear : (fun s => J.first s X) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) :=
    (show ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 T from isOpen_Ioo.mem_nhds ht).mono (fun s hs => hfirst s hs)
  have hz : HasDerivAt (fun s => J.first s X) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hnear
  exact ⟨hfirst t ht,(J.deriv_first t X).unique hz⟩

/-- 原八变量路径上的零区保持，接成三层实际加权状态需要的零值。
(5.5)/(6.3) 的零区处理：先 p=r=0、再初始 φ=0、再真实零导数保持，
最后微分得到导数两层；绝不从 a=0 单独断言辅助场为零。 -/
theorem original_smoothZeroOn (D : Rect) (C : SpatialAbsorption Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (B : SmoothStateData) (hid : LiftIdentified B F μ u₀ q₀) (hT : 0 ≤ T)
    (hp : ∀ X, C.p X=p X.1) (hr : ∀ X, C.r X=r X.2)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hφzero : ∀ X∈D.openSet, C.a X=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0) :
    SmoothZeroOn D C B (Ioo 0 T) := by
  have hvalue (X : Point) (hX : X ∈ D.openSet) (ha : C.a X=0) :
      ∀ t∈Icc 0 T, B.φx.value t X=0 ∧ B.φy.value t X=0 := by
    have hsum : p X.1+r X.2=0 := by
      simpa only [SpatialAbsorption.a,absorptionSum,hp,hr] using ha
    have hkeep := original_zero_region_preserved D.openSet ε κ τ μ T p r F u₀ q₀ hT
      hregular hOriginal hinitial X hX (hp X ▸ C.p_nonneg X) (hr X ▸ C.r_nonneg X)
      hsum (hφzero X hX ha).1 (hφzero X hX ha).2
    intro t ht
    have hx : B.φx.value t X=(lift F μ u₀ q₀).φx t X := congrFun (congrFun hid.φx t) X
    have hy : B.φy.value t X=(lift F μ u₀ q₀).φy t X := congrFun (congrFun hid.φy t) X
    exact ⟨hx.trans (hkeep t ht).1,hy.trans (hkeep t ht).2⟩
  have hxall (t : ℝ) (ht : t∈Ioo 0 T) :
      ∀ᵐ X ∂D.measure, C.wx X=0 →
        B.φx.value t X=0 ∧ B.φx.first t X=0 ∧ B.φx.second t X=0 := by
    filter_upwards [ae_restrict_mem D.openSet_open.measurableSet] with X hX
    intro hw
    have ha := (C.wx_eq_zero_iff X).mp hw
    have hv := hvalue X hX ha
    have hd := jet_zero_derivatives B.φx T X (fun s hs => (hv s ⟨hs.1.le,hs.2.le⟩).1) ht
    exact ⟨(hv t ⟨ht.1.le,ht.2.le⟩).1,hd⟩
  have hyall (t : ℝ) (ht : t∈Ioo 0 T) :
      ∀ᵐ X ∂D.measure, C.wy X=0 →
        B.φy.value t X=0 ∧ B.φy.first t X=0 ∧ B.φy.second t X=0 := by
    filter_upwards [ae_restrict_mem D.openSet_open.measurableSet] with X hX
    intro hw
    have ha := (C.wy_eq_zero_iff X).mp hw
    have hv := hvalue X hX ha
    have hd := jet_zero_derivatives B.φy T X (fun s hs => (hv s ⟨hs.1.le,hs.2.le⟩).2) ht
    exact ⟨(hv t ⟨ht.1.le,ht.2.le⟩).2,hd⟩
  exact ⟨fun t ht => (hxall t ht).mono (fun _ h hw => (h hw).1),
    fun t ht => (hxall t ht).mono (fun _ h hw => (h hw).2.1),
    fun t ht => (hxall t ht).mono (fun _ h hw => (h hw).2.2),
    fun t ht => (hyall t ht).mono (fun _ h hw => (h hw).1),
    fun t ht => (hyall t ht).mono (fun _ h hw => (h hw).2.1),
    fun t ht => (hyall t ht).mono (fun _ h hw => (h hw).2.2)⟩



/-- Λ=∇u+φ 是历史提升的实际空间定义，对整个技术延拓成立。
不是“某个名为梯度的槽”的关系，dx/dy 均为真实 fderiv 坐标分量。 -/
theorem lift_spatial_coordinates (B : SmoothStateData) (F : OriginalFields)
    (μ : ℝ) (u₀ q₀ : Point → ℝ) (hid : LiftIdentified B F μ u₀ q₀) (t : ℝ) (X : Point) :
    B.Λx.value t X=dx (B.v.value t) X+B.φx.value t X ∧
    B.Λy.value t X=dy (B.v.value t) X+B.φy.value t X := by
  have hx := congrFun (congrFun hid.Λx t) X
  have hy := congrFun (congrFun hid.Λy t) X
  have hφx := congrFun (congrFun hid.φx t) X
  have hφy := congrFun (congrFun hid.φy t) X
  have hgx := congrArg (fun U : Field => spaceDx U t X) hid.v
  have hgy := congrArg (fun U : Field => spaceDy U t X) hid.v
  change dx (B.v.value t) X=spaceDx (integralLift F.E u₀) t X at hgx
  change dy (B.v.value t) X=spaceDy (integralLift F.E u₀) t X at hgy
  dsimp only [lift] at hx hy hφx hφy
  constructor <;> linarith

/-- 对前条真实空间关系求导，得到导数层 Λ_t=∇u_t+φ_t。
联合光滑性通过 TimeSpace 已证定理兑现混合导数交换；不把交换当作结构字段。 -/
theorem lift_first_spatial_coordinates (B : SmoothStateData) (F : OriginalFields)
    (μ : ℝ) (u₀ q₀ : Point → ℝ) (hid : LiftIdentified B F μ u₀ q₀) (t : ℝ) (X : Point) :
    B.Λx.first t X=dx (B.v.first t) X+B.φx.first t X ∧
    B.Λy.first t X=dy (B.v.first t) X+B.φy.first t X := by
  have hxgrad : HasDerivAt (fun s => dx (B.v.value s) X) (dx (B.v.first t) X) t :=
    hasDerivAt_spaceFDeriv_of_timeDeriv (F := fun s Y => B.v.value s Y)
      (E := fun s Y => B.v.first s Y) B.v.joint_value t X (1,0)
      (Eventually.of_forall (fun Y => B.v.deriv_value t Y))
  have hygrad : HasDerivAt (fun s => dy (B.v.value s) X) (dy (B.v.first t) X) t :=
    hasDerivAt_spaceFDeriv_of_timeDeriv (F := fun s Y => B.v.value s Y)
      (E := fun s Y => B.v.first s Y) B.v.joint_value t X (0,1)
      (Eventually.of_forall (fun Y => B.v.deriv_value t Y))
  have hxfunction : (fun s => B.Λx.value s X) = (fun s => dx (B.v.value s) X+B.φx.value s X) :=
    funext (fun s => (lift_spatial_coordinates B F μ u₀ q₀ hid s X).1)
  have hyfunction : (fun s => B.Λy.value s X) = (fun s => dy (B.v.value s) X+B.φy.value s X) :=
    funext (fun s => (lift_spatial_coordinates B F μ u₀ q₀ hid s X).2)
  have hxderiv := (hxgrad.add (B.φx.deriv_value t X))
  have hyderiv := (hygrad.add (B.φy.deriv_value t X))
  change HasDerivAt (fun s => dx (B.v.value s) X+B.φx.value s X) _ t at hxderiv
  rw [← hxfunction] at hxderiv
  change HasDerivAt (fun s => dy (B.v.value s) X+B.φy.value s X) _ t at hyderiv
  rw [← hyfunction] at hyderiv
  exact ⟨(B.Λx.deriv_value t X).unique hxderiv,(B.Λy.deriv_value t X).unique hyderiv⟩

/-- T>0 时，闭区间连续等式由内部等式延拓到两个端点。
这里只是拓扑闭包，不要求端点满足普通双侧 PDE；T=0 留给真实初始约束。 -/
theorem eq_on_closed_of_internal {F G : ℝ → ℝ} {T : ℝ} (hT : 0<T)
    (hF : Continuous F) (hG : Continuous G) (hinterior : EqOn F G (Ioo 0 T)) :
    EqOn F G (Icc 0 T) := by
  have hclosure := hinterior.closure hF hG
  simpa only [closure_Ioo hT.ne] using hclosure

/-- 原层兼容保持经真正时间求导得到导数层极化约束，再连续延拓到端点。
T=0 的首层初始约束不能从空内部方程推出，因此只在退化情况下明确输入。 -/
theorem lift_first_polar_closed (D : Rect) (ε κ τ μ T : ℝ) (p r : ℝ → ℝ)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (B : SmoothStateData)
    (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hdegenerate : T=0 → ∀ X∈D.openSet, B.z.first 0 X+τ*B.R.first 0 X=κ*B.v.first 0 X) :
    ∀ t∈Icc 0 T, ∀ X∈D.openSet, B.z.first t X+τ*B.R.first t X=κ*B.v.first t X := by
  have hcompat := compatible_lift_on_Icc D.openSet ε κ τ μ T p r F u₀ q₀ hT
    hregular hOriginal hinitial
  have hbase (s : ℝ) (hs : s∈Icc 0 T) (X : Point) (hX : X∈D.openSet) :
      B.z.value s X+τ*B.R.value s X=κ*B.v.value s X := by
    have hz := congrFun (congrFun hid.z s) X
    have hR := congrFun (congrFun hid.R s) X
    have hv := congrFun (congrFun hid.v s) X
    rw [hz,hR,hv]
    exact (hcompat s hs X hX).polar
  intro t ht X hX
  by_cases hzero : T=0
  · have htzero : t=0 := by rw [hzero] at ht; exact le_antisymm ht.2 ht.1
    simpa only [htzero] using hdegenerate hzero X hX
  · have hpositive : 0<T := lt_of_le_of_ne hT (Ne.symm hzero)
    have hzcont : Continuous (fun s => B.z.first s X) :=
      continuous_iff_continuousAt.mpr (fun s => (B.z.deriv_first s X).continuousAt)
    have hRcont : Continuous (fun s => B.R.first s X) :=
      continuous_iff_continuousAt.mpr (fun s => (B.R.deriv_first s X).continuousAt)
    have hvcont : Continuous (fun s => B.v.first s X) :=
      continuous_iff_continuousAt.mpr (fun s => (B.v.deriv_first s X).continuousAt)
    apply eq_on_closed_of_internal hpositive (hzcont.add (hRcont.const_mul τ))
      (hvcont.const_mul κ) ?_ ht
    intro s hs
    have hleft := (B.z.deriv_value s X).add ((B.R.deriv_value s X).const_mul τ)
    have hright := (B.v.deriv_value s X).const_mul κ
    have hnear : (fun r => B.z.value r X+τ*B.R.value r X) =ᶠ[𝓝 s]
        (fun r => κ*B.v.value r X) :=
      (show ∀ᶠ r in 𝓝 s, r∈Ioo 0 T from isOpen_Ioo.mem_nhds hs).mono
        (fun r hr => hbase r ⟨hr.1.le,hr.2.le⟩ X hX)
    exact hleft.unique (hright.congr_of_eventuallyEq hnear)



/-- 只有 T=0 时额外使用的导数层初始兼容。它们约束初始场，
不是能量估计；非退化区间会从原 PDE 和连续性推出同样关系。 -/
structure InitialDerivativeCompatible (D : Rect) (C : SpatialAbsorption Point)
    (B : SmoothStateData) (κ τ : ℝ) : Prop where
  polar : ∀ X∈D.openSet, B.z.first 0 X+τ*B.R.first 0 X=κ*B.v.first 0 X
  zeroX : ∀ X∈D.openSet, C.a X=0 → B.φx.first 0 X=0
  zeroY : ∀ X∈D.openSet, C.a X=0 → B.φy.first 0 X=0

/-- 零区保持延拓到闭时间区间的原层和导数层。
原层使用初始 φ=0；首层在内部由真正零导数推出，端点只用连续性。
这专门保证普通场恢复映射在零区不丢失物理信息。 -/
theorem lift_zero_coordinates_closed (D : Rect) (C : SpatialAbsorption Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (B : SmoothStateData) (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T)
    (hp : ∀ X, C.p X=p X.1) (hr : ∀ X, C.r X=r X.2)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hφzero : ∀ X∈D.openSet, C.a X=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hdegenerate : T=0 → InitialDerivativeCompatible D C B κ τ) :
    ∀ t∈Icc 0 T, ∀ X∈D.openSet, C.a X=0 →
      (B.φx.value t X=0 ∧ B.φy.value t X=0) ∧
      (B.φx.first t X=0 ∧ B.φy.first t X=0) := by
  intro t ht X hX ha
  have hsum : p X.1+r X.2=0 := by
    simpa only [SpatialAbsorption.a,absorptionSum,hp,hr] using ha
  have hkeep := original_zero_region_preserved D.openSet ε κ τ μ T p r F u₀ q₀ hT
    hregular hOriginal hinitial X hX (hp X ▸ C.p_nonneg X) (hr X ▸ C.r_nonneg X)
    hsum (hφzero X hX ha).1 (hφzero X hX ha).2
  have hvalue (s : ℝ) (hs : s∈Icc 0 T) : B.φx.value s X=0 ∧ B.φy.value s X=0 := by
    have hx := congrFun (congrFun hid.φx s) X
    have hy := congrFun (congrFun hid.φy s) X
    exact ⟨hx.trans (hkeep s hs).1,hy.trans (hkeep s hs).2⟩
  refine ⟨hvalue t ht,?_⟩
  by_cases hzero : T=0
  · have htzero : t=0 := by rw [hzero] at ht; exact le_antisymm ht.2 ht.1
    simpa only [htzero] using
      And.intro ((hdegenerate hzero).zeroX X hX ha) ((hdegenerate hzero).zeroY X hX ha)
  · have hpositive : 0<T := lt_of_le_of_ne hT (Ne.symm hzero)
    have hXcont : Continuous (fun s => B.φx.first s X) :=
      continuous_iff_continuousAt.mpr (fun s => (B.φx.deriv_first s X).continuousAt)
    have hYcont : Continuous (fun s => B.φy.first s X) :=
      continuous_iff_continuousAt.mpr (fun s => (B.φy.deriv_first s X).continuousAt)
    constructor
    · apply eq_on_closed_of_internal hpositive hXcont continuous_const ?_ ht
      intro s hs
      exact (jet_zero_derivatives B.φx T X
        (fun r hr => (hvalue r ⟨hr.1.le,hr.2.le⟩).1) hs).1
    · apply eq_on_closed_of_internal hpositive hYcont continuous_const ?_ ht
      intro s hs
      exact (jet_zero_derivatives B.φy T X
        (fun r hr => (hvalue r ⟨hr.1.le,hr.2.le⟩).2) hs).1

/-- 原 PDE、初始兼容、PEC 与历史初值零迹，推出闭区间两层静态约束。
空间、极化、零区及边界条件逐项得到，未把它们打包成解定义的目标字段。
此结果填入具体 Green/Poincaré 装配的有限区间接口。 -/
theorem original_static_closed (D : Rect) (C : SpatialAbsorption Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (B : SmoothStateData) (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T)
    (hp : ∀ X, C.p X=p X.1) (hr : ∀ X, C.r X=r X.2)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hφzero : ∀ X∈D.openSet, C.a X=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀)
    (hdegenerate : T=0 → InitialDerivativeCompatible D C B κ τ) :
    ∀ t∈Icc 0 T,
      SmoothStaticAt D C κ τ (smoothCoordinatesBase B t) ∧
      SmoothStaticAt D C κ τ (smoothCoordinatesFirst B t) := by
  have hcompat := compatible_lift_on_Icc D.openSet ε κ τ μ T p r F u₀ q₀ hT
    hregular hOriginal hinitial
  have hfirstpolar := lift_first_polar_closed D ε κ τ μ T p r F u₀ q₀ B hid hT
    hregular hOriginal hinitial (fun hz => (hdegenerate hz).polar)
  have hzeros := lift_zero_coordinates_closed D C ε κ τ μ T p r F u₀ q₀ B hid hT
    hp hr hregular hOriginal hinitial hφzero hdegenerate
  intro t ht
  have hv : (fun X => B.v.value t X)=integralLift F.E u₀ t := congrFun hid.v t
  have hfirstv : (fun X => B.v.first t X)=F.E t := by
    funext X
    exact (lift_velocity_coordinates B F μ u₀ q₀ hid hregular t X).1.trans
      (congrFun (congrFun hid.V t) X)
  constructor
  · constructor
    · intro X hX
      change B.z.value t X+τ*B.R.value t X=κ*B.v.value t X
      rw [congrFun (congrFun hid.z t) X,congrFun (congrFun hid.R t) X,
        congrFun (congrFun hid.v t) X]
      exact (hcompat t ht X hX).polar
    · intro X _; exact (lift_spatial_coordinates B F μ u₀ q₀ hid t X).1
    · intro X _; exact (lift_spatial_coordinates B F μ u₀ q₀ hid t X).2
    · change ZeroBoundary D (fun X => B.v.value t X)
      rw [hv]
      exact integralLift_rect_zeroBoundary D T F u₀ hPEC hu₀ t ht
    · filter_upwards [ae_restrict_mem D.openSet_open.measurableSet] with X hX
      intro hw
      exact (hzeros t ht X hX ((C.wx_eq_zero_iff X).mp hw)).1.1
    · filter_upwards [ae_restrict_mem D.openSet_open.measurableSet] with X hX
      intro hw
      exact (hzeros t ht X hX ((C.wy_eq_zero_iff X).mp hw)).1.2
  · constructor
    · exact hfirstpolar t ht
    · intro X _; exact (lift_first_spatial_coordinates B F μ u₀ q₀ hid t X).1
    · intro X _; exact (lift_first_spatial_coordinates B F μ u₀ q₀ hid t X).2
    · change ZeroBoundary D (fun X => B.v.first t X)
      rw [hfirstv]
      exact hPEC t ht
    · filter_upwards [ae_restrict_mem D.openSet_open.measurableSet] with X hX
      intro hw
      exact (hzeros t ht X hX ((C.wx_eq_zero_iff X).mp hw)).2.1
    · filter_upwards [ae_restrict_mem D.openSet_open.measurableSet] with X hX
      intro hw
      exact (hzeros t ht X hX ((C.wy_eq_zero_iff X).mp hw)).2.2



/-- v0.4.4 的原系统到有限区间框架入口。
输入只有八方程、原始初始兼容、PEC、零区初始 φ、所选光滑/加权正则性及
坐标识别；实际 Green、Poincaré、混合求导、全时段兼容和两层零区均在内部得到。
此构造尚未发布最终能量主定理，留作下一阶段直接调用的具体问题对象。 -/
def originalFiniteIntervalProblem (D : Rect) (C : SpatialAbsorption Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T)
    (hp : ∀ X, C.p X=p X.1) (hr : ∀ X, C.r X=r X.2)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hφzero : ∀ X∈D.openSet, C.a X=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀)
    (hdegenerate : T=0 → InitialDerivativeCompatible D C B κ τ) :
    FiniteIntervalProblemConditional (greenDomain D) C ε κ τ μ
      (poincareConstant D) T (poincare_estimate D) := by
  have hprimitive : PrimitiveOn D.openSet T ε κ τ μ p r (smoothPrimitiveFields B) := by
    rw [smoothPrimitiveFields_eq_lift B F μ u₀ q₀ hid]
    exact original_to_primitive D.openSet ε κ τ μ T p r F u₀ q₀ hT hregular hOriginal hinitial
  have hzero : SmoothZeroOn D C B (Ioo 0 T) :=
    original_smoothZeroOn D C ε κ τ μ T p r F u₀ q₀ B hid hT hp hr hregular hOriginal hinitial hφzero
  have hstatic := original_static_closed D C ε κ τ μ T p r F u₀ q₀ B hid hT hp hr
    hregular hOriginal hinitial hφzero hPEC hu₀ hdegenerate
  exact finiteIntervalProblem_of_smooth D C B reg ε κ τ μ T hT p r hp hr hprimitive hzero
    (fun t ht => (hstatic t ht).1) (fun t ht => (hstatic t ht).2)

/-- 前条实际构造中的 P_tt 属于连续 L² 路径，供后续积分平衡调用。
这里它确实是 B.R 的第二次真实时间导数，不是另取一个普通坐标。 -/
theorem originalFiniteIntervalProblem_second_R_continuous
    (D : Rect) (C : SpatialAbsorption Point)
    (ε κ τ μ T : ℝ) (p r : ℝ → ℝ) (F : OriginalFields) (u₀ q₀ : Point → ℝ)
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T)
    (hp : ∀ X, C.p X=p X.1) (hr : ∀ X, C.r X=r X.2)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hφzero : ∀ X∈D.openSet, C.a X=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀)
    (hdegenerate : T=0 → InitialDerivativeCompatible D C B κ τ) :
    ContinuousOn (fun t => ((originalFiniteIntervalProblem D C ε κ τ μ T p r F u₀ q₀ B reg
      hid hT hp hr hregular hOriginal hinitial hφzero hPEC hu₀ hdegenerate).path.second t).R)
      (Icc 0 T) := by
  exact (continuous_jet_L2 D B.R reg.R).2.2.continuousOn

/-- 显式分离系数的模型入口：p=p(x)、r=r(y)，非负并受原幅度约束。
光滑系数正则性声明的是本阶段选择的强解类；可测性由其连续性推得。
没有正吸收下界；p=r=0、两种边层及角层全部允许。
材料参数正性供下一阶段主定理使用；本映射本身没有做除材料参数的操作。 -/
def originalFiniteIntervalProblem_separated (D : Rect)
    (ε κ τ μ T c S : ℝ) (_hε : 0<ε) (_hκ : 0<κ) (_hτ : 0<τ) (_hμ : 0<μ)
    (hc : 0<c) (p r : ℝ → ℝ) (hp_smooth : ContDiff ℝ ∞ p) (hr_smooth : ContDiff ℝ ∞ r)
    (hp_nonneg : ∀ x, 0≤p x) (hr_nonneg : ∀ y, 0≤r y)
    (hp_le : ∀ x, p x≤S) (hr_le : ∀ y, r y≤S) (hS : S≤c/4)
    (F : OriginalFields) (u₀ q₀ : Point → ℝ) (B : SmoothStateData)
    (reg : SmoothStateRegular D
      (SpatialAbsorption.separated c S hc p r hp_smooth.continuous.measurable
        hr_smooth.continuous.measurable hp_nonneg hr_nonneg hp_le hr_le hS) B)
    (hid : LiftIdentified B F μ u₀ q₀) (hT : 0≤T)
    (hregular : OriginalLiftRegular F u₀) (hOriginal : OriginalOn D.openSet T ε κ τ μ p r F)
    (hinitial : ∀ X∈D.openSet, InitialCompatible F (lift F μ u₀ q₀) ε κ τ p r X)
    (hφzero : ∀ X∈D.openSet, p X.1+r X.2=0 →
      (lift F μ u₀ q₀).φx 0 X=0 ∧ (lift F μ u₀ q₀).φy 0 X=0)
    (hPEC : OriginalRectPEC D T F) (hu₀ : ZeroBoundary D u₀)
    (hdegenerate : T=0 → InitialDerivativeCompatible D
      (SpatialAbsorption.separated c S hc p r hp_smooth.continuous.measurable
        hr_smooth.continuous.measurable hp_nonneg hr_nonneg hp_le hr_le hS) B κ τ) :
    FiniteIntervalProblemConditional (greenDomain D)
      (SpatialAbsorption.separated c S hc p r hp_smooth.continuous.measurable
        hr_smooth.continuous.measurable hp_nonneg hr_nonneg hp_le hr_le hS)
      ε κ τ μ (poincareConstant D) T (poincare_estimate D) :=
  originalFiniteIntervalProblem D _ ε κ τ μ T p r F u₀ q₀ B reg hid hT
    (fun _ => rfl) (fun _ => rfl) hregular hOriginal hinitial hφzero hPEC hu₀ hdegenerate

end LeanPML.PML.Concrete
