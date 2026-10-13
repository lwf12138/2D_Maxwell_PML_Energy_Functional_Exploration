import LeanPML.Rectangle.Poincare
import LeanPML.Rectangle.StatePaths
import LeanPML.Rectangle.BoundaryTime
import LeanPML.PML.PrimitiveSystem
import LeanPML.PML.MainAbstract
import LeanPML.PML.WeightedCalculus

/-!
# v0.4.4：真实光滑场到既有能量框架的接口桥接

本文件把原系统→primitive 已经推出的逐点方程，转为旧工程使用的实际 L² 方程。
空间算子、迹及 Poincaré 均来自 Rectangle 中已证的具体构造，不能再传入任意
Green 或 estimate。坐标本身仍不自动是时间导数；SameSourcePath 的构造另由
真实时间路径证明填入。本文件不发布 v0.5 的最终具体 PDE 能量定理。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology InnerProductSpace
open LeanPML.Analysis LeanPML.PML
namespace LeanPML.Rectangle

/-- 八个 primitive 瞬时光滑坐标，顺序与 FieldState 一致。
这里的 V 只是坐标，时间导数含义由下游实际时间路径赋予。 -/
structure SmoothStateCoordinates where
  v : SmoothField
  V : SmoothField
  R : SmoothField
  z : SmoothField
  ψx : SmoothField
  ψy : SmoothField
  Λx : SmoothField
  Λy : SmoothField

/-- 实际状态的代表识别。普通分量使用已证 toL2，辅助分量使用实际加权恢复。
此结构只记录空间表示，不输入演化、Green、兼容保持或任何能量结论。 -/
structure StateRepresented (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (U : FieldState D.measure C.wx C.wy) (s : SmoothStateCoordinates) : Prop where
  v : U.v = SmoothField.toL2 D s.v
  V : U.V = SmoothField.toL2 D s.V
  R : U.R = SmoothField.toL2 D s.R
  z : U.z = SmoothField.toL2 D s.z
  ψx : physicalX D.measure C U.ψx = SmoothField.toL2 D s.ψx
  ψy : physicalY D.measure C U.ψy = SmoothField.toL2 D s.ψy
  Λx : U.Λx = SmoothField.toL2 D s.Λx
  Λy : U.Λy = SmoothField.toL2 D s.Λy

/-- 光滑函数在整个开计算域逐点相等，则实际 L² 类相等。
这里没有将计算域缩为物理区；端点和外部代表取值不参与 L² 等价。 -/
theorem toL2_eq_of_eqOn (D : Rect) (f g : SmoothField) (heq : EqOn (⇑f) (⇑g) D.openSet) :
    SmoothField.toL2 D f = SmoothField.toL2 D g := by
  apply Lp.ext
  filter_upwards [SmoothField.coe_toL2 D f, SmoothField.coe_toL2 D g,
    ae_restrict_mem D.openSet_open.measurableSet] with z hf hg hz
  rw [hf,hg]
  exact heq hz

/-- 实际 L² 和的代表表达；用于把逐点 primitive 主方程合法传给 L² 商类。
由 mathlib 的商类加法事实及 a.e. 传递推出，原文未单列。 -/
theorem coe_add_of (D : Rect) {u v : ScalarL2 D.measure} {f g : ℝ × ℝ → ℝ}
    (hu : (⇑u) =ᵐ[D.measure] f) (hv : (⇑v) =ᵐ[D.measure] g) :
    (⇑(u+v)) =ᵐ[D.measure] (fun z => f z+g z) := by
  filter_upwards [Lp.coeFn_add u v,hu,hv] with z hsum hf hg
  simpa only [Pi.add_apply,hf,hg] using hsum

/-- 标量乘法在实际 L² 代表上的表达；μ、ε、κ 等常数从这里进入。 -/
theorem coe_smul_of (D : Rect) (r : ℝ) {u : ScalarL2 D.measure} {f : ℝ × ℝ → ℝ}
    (hu : (⇑u) =ᵐ[D.measure] f) :
    (⇑(r•u)) =ᵐ[D.measure] (fun z => r*f z) := by
  filter_upwards [Lp.coeFn_smul r u,hu] with z hsm hf
  simpa only [Pi.smul_apply,smul_eq_mul,hf] using hsm

/-- 实际有界系数乘法对应点态乘法；仅用于 p,r,a,b 等有界系数。
不对无界能量权重使用这个入口。 -/
theorem coe_operator_of (D : Rect) (m : BoundedCoefficient (ℝ × ℝ))
    {u : ScalarL2 D.measure} {f : ℝ × ℝ → ℝ} (hu : (⇑u) =ᵐ[D.measure] f) :
    (⇑(m.operator D.measure u)) =ᵐ[D.measure] (fun z => m.value z*f z) := by
  filter_upwards [m.coe_operator D.measure u,hu] with z hmul hf
  simpa only [hf] using hmul

/-- 光滑通量的散度代表是两条真实坐标偏导，不是另给一个叫 div 的函数。 -/
theorem divergence_ofSmooth_ae (D : Rect) (X Y : SmoothField) :
    (⇑(divergence D (fluxOfSmooth D X Y))) =ᵐ[D.measure]
      (fun z => dx X z+dy Y z) := by
  rw [divergence_ofSmooth]
  exact coe_add_of D (SmoothField.coe_toL2 D X.derivativeX)
    (SmoothField.coe_toL2 D Y.derivativeY)

/-- 逐点约束 z+τR=κv 给出真实 L² 极化约束。
来源 V7 (2.6)/(6.1)；输入等式由初值保持或其真实求导在上游产生。 -/
theorem polar_of_pointwise (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (κ τ : ℝ) (U : FieldState D.measure C.wx C.wy) (s : SmoothStateCoordinates)
    (hrep : StateRepresented D C U s)
    (hpolar : ∀ x∈D.openSet, s.z x+τ*s.R x=κ*s.v x) : PolarConstraint κ τ U := by
  unfold PolarConstraint
  apply Lp.ext
  have hz : (⇑U.z) =ᵐ[D.measure] (⇑s.z) := hrep.z ▸ SmoothField.coe_toL2 D s.z
  have hR : (⇑U.R) =ᵐ[D.measure] (⇑s.R) := hrep.R ▸ SmoothField.coe_toL2 D s.R
  have hv : (⇑U.v) =ᵐ[D.measure] (⇑s.v) := hrep.v ▸ SmoothField.coe_toL2 D s.v
  filter_upwards [coe_add_of D hz (coe_smul_of D τ hR), coe_smul_of D κ hv,
    ae_restrict_mem D.openSet_open.measurableSet] with x hleft hright hx
  exact hleft.trans ((hpolar x hx).trans hright.symm)

/-- 从逐点 Λ=∇v+ψ 得到具体矩形的实际空间约束。
梯度是 Fields 中真实偏导降到商类的结果；辅助量走加权物理恢复映射。 -/
theorem spatial_of_pointwise (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (U : FieldState D.measure C.wx C.wy) (s : SmoothStateCoordinates)
    (hrep : StateRepresented D C U s)
    (hX : ∀ x∈D.openSet, s.Λx x=dx s.v x+s.ψx x)
    (hY : ∀ x∈D.openSet, s.Λy x=dy s.v x+s.ψy x) :
    FieldSpatialConstraint D.measure C (spatialDomain D) U := by
  have hmem : U.v ∈ (spatialDomain D).domain := by
    rw [hrep.v]
    exact ⟨s.v,rfl⟩
  refine ⟨hmem,?_,?_⟩
  · have harg : (⟨U.v,hmem⟩ : fieldDomain D) = fieldOfSmooth D s.v :=
      Subtype.ext hrep.v
    erw [harg]
    erw [componentX_toL2]
    rw [hrep.Λx,hrep.ψx]
    apply Lp.ext
    filter_upwards [SmoothField.coe_toL2 D s.Λx,
      coe_add_of D (SmoothField.coe_toL2 D s.v.derivativeX) (SmoothField.coe_toL2 D s.ψx),
      ae_restrict_mem D.openSet_open.measurableSet] with x hflux hsum hx
    exact hflux.trans ((hX x hx).trans hsum.symm)
  · have harg : (⟨U.v,hmem⟩ : fieldDomain D) = fieldOfSmooth D s.v :=
      Subtype.ext hrep.v
    erw [harg]
    erw [componentY_toL2]
    rw [hrep.Λy,hrep.ψy]
    apply Lp.ext
    filter_upwards [SmoothField.coe_toL2 D s.Λy,
      coe_add_of D (SmoothField.coe_toL2 D s.v.derivativeY) (SmoothField.coe_toL2 D s.ψy),
      ae_restrict_mem D.openSet_open.measurableSet] with x hflux hsum hx
    exact hflux.trans ((hY x hx).trans hsum.symm)

/-- 兼容、真实空间约束和四边零值进入实际静态约束；Poincaré 已具体证明。
来源 (6.1)/(8.3)，不输入任何图范数界或能量非负结论。 -/
theorem static_of_pointwise (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (κ τ : ℝ) (U : FieldState D.measure C.wx C.wy) (s : SmoothStateCoordinates)
    (hrep : StateRepresented D C U s)
    (hpolar : ∀ x∈D.openSet, s.z x+τ*s.R x=κ*s.v x)
    (hX : ∀ x∈D.openSet, s.Λx x=dx s.v x+s.ψx x)
    (hY : ∀ x∈D.openSet, s.Λy x=dy s.v x+s.ψy x)
    (hzero : ZeroBoundary D s.v) :
    StateCoercivityConstraints D.measure C (spatialDomain D) (poincareDomain D) κ τ U := by
  have hspatial := spatial_of_pointwise D C U s hrep hX hY
  refine ⟨hspatial,?_,polar_of_pointwise D C κ τ U s hrep hpolar⟩
  change trace D ⟨U.v,hspatial.mem_domain⟩ = 0
  have harg : (⟨U.v,hspatial.mem_domain⟩ : fieldDomain D) = fieldOfSmooth D s.v :=
    Subtype.ext hrep.v
  rw [harg]
  erw [trace_toL2]
  exact (smoothTrace_eq_zero_iff D s.v).mpr hzero

/-- primitive 主方程左边在实际 L² 中的代表表达。
这里只转换已有坐标表达，不把 dU 的名字当成导数；时间层调用者另有真实证据。 -/
theorem primitiveMain_ae_of_represented (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ε μ : ℝ) (U dU : FieldState D.measure C.wx C.wy)
    (s ds : SmoothStateCoordinates) (hrep : StateRepresented D C U s)
    (hdrep : StateRepresented D C dU ds) :
    (⇑(primitiveMain D.measure C ε μ U dU)) =ᵐ[D.measure]
      (fun x => μ*(ε*(ds.V x+C.a x*s.V x+C.b x*s.v x)+
        ds.R x+C.a x*s.R x+C.b x*s.z x)) := by
  have hv : (⇑U.v) =ᵐ[D.measure] (⇑s.v) := hrep.v ▸ SmoothField.coe_toL2 D s.v
  have hV : (⇑U.V) =ᵐ[D.measure] (⇑s.V) := hrep.V ▸ SmoothField.coe_toL2 D s.V
  have hR : (⇑U.R) =ᵐ[D.measure] (⇑s.R) := hrep.R ▸ SmoothField.coe_toL2 D s.R
  have hz : (⇑U.z) =ᵐ[D.measure] (⇑s.z) := hrep.z ▸ SmoothField.coe_toL2 D s.z
  have hdV : (⇑dU.V) =ᵐ[D.measure] (⇑ds.V) := hdrep.V ▸ SmoothField.coe_toL2 D ds.V
  have hdR : (⇑dU.R) =ᵐ[D.measure] (⇑ds.R) := hdrep.R ▸ SmoothField.coe_toL2 D ds.R
  have helectric := coe_smul_of D ε (coe_add_of D
    (coe_add_of D hdV (coe_operator_of D C.aCoeff hV)) (coe_operator_of D C.bCoeff hv))
  have hmain := coe_smul_of D μ (coe_add_of D
    (coe_add_of D (coe_add_of D helectric hdR) (coe_operator_of D C.aCoeff hR))
    (coe_operator_of D C.bCoeff hz))
  simpa only [primitiveMain,SpatialAbsorption.aCoeff_value,SpatialAbsorption.bCoeff_value] using hmain

/-- (2.6) 的逐点 primitive 方程接入真实 L² PrimitiveAtConditional。
输入六条关系是上游原模型消元后的方程；本引理仅做空间表示桥接，
不自行声称 ds 是时间导数。具体路径用真实 SameSourcePath 绑定该层。
Green、Poincaré 与梯度的具体定义均固定，不能由调用者另行输入。 -/
theorem primitive_of_pointwise (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ε κ τ μ : ℝ) (U dU : FieldState D.measure C.wx C.wy)
    (s ds : SmoothStateCoordinates) (hrep : StateRepresented D C U s)
    (hdrep : StateRepresented D C dU ds)
    (hmain : ∀ x∈D.openSet,
      μ*(ε*(ds.V x+C.a x*s.V x+C.b x*s.v x)+ds.R x+C.a x*s.R x+C.b x*s.z x) =
        dx s.Λx x+dy s.Λy x)
    (hpolar : ∀ x∈D.openSet, s.z x+τ*s.R x=κ*s.v x)
    (hspX : ∀ x∈D.openSet, s.Λx x=dx s.v x+s.ψx x)
    (hspY : ∀ x∈D.openSet, s.Λy x=dy s.v x+s.ψy x)
    (hauxX : ∀ x∈D.openSet, ds.ψx x=C.r x*dx s.v x-C.p x*s.Λx x)
    (hauxY : ∀ x∈D.openSet, ds.ψy x=C.p x*dy s.v x-C.r x*s.Λy x) :
    PrimitiveAtConditional (greenDomain D) C ε κ τ μ U dU
      (fieldOfSmooth D s.v) (fluxOfSmooth D s.Λx s.Λy) := by
  refine ⟨?_,polar_of_pointwise D C κ τ U s hrep hpolar,?_,?_,?_,?_⟩
  · apply Lp.ext
    filter_upwards [primitiveMain_ae_of_represented D C ε μ U dU s ds hrep hdrep,
      divergence_ofSmooth_ae D s.Λx s.Λy,
      ae_restrict_mem D.openSet_open.measurableSet] with x hleft hright hx
    exact hleft.trans ((hmain x hx).trans hright.symm)
  · change U.Λx = (spatialDomain D).componentX (fieldOfSmooth D s.v) + physicalX D.measure C U.ψx
    erw [componentX_toL2]
    rw [hrep.Λx,hrep.ψx]
    apply Lp.ext
    filter_upwards [SmoothField.coe_toL2 D s.Λx,
      coe_add_of D (SmoothField.coe_toL2 D s.v.derivativeX) (SmoothField.coe_toL2 D s.ψx),
      ae_restrict_mem D.openSet_open.measurableSet] with x hleft hright hx
    exact hleft.trans ((hspX x hx).trans hright.symm)
  · change U.Λy = (spatialDomain D).componentY (fieldOfSmooth D s.v) + physicalY D.measure C U.ψy
    erw [componentY_toL2]
    rw [hrep.Λy,hrep.ψy]
    apply Lp.ext
    filter_upwards [SmoothField.coe_toL2 D s.Λy,
      coe_add_of D (SmoothField.coe_toL2 D s.v.derivativeY) (SmoothField.coe_toL2 D s.ψy),
      ae_restrict_mem D.openSet_open.measurableSet] with x hleft hright hx
    exact hleft.trans ((hspY x hx).trans hright.symm)
  · change physicalX D.measure C dU.ψx = C.rCoeff.operator D.measure
      ((spatialDomain D).componentX (fieldOfSmooth D s.v)) - C.pCoeff.operator D.measure U.Λx
    erw [componentX_toL2]
    rw [hdrep.ψx,hrep.Λx]
    apply Lp.ext
    filter_upwards [SmoothField.coe_toL2 D ds.ψx,
      Lp.coeFn_sub (C.rCoeff.operator D.measure (SmoothField.toL2 D s.v.derivativeX))
        (C.pCoeff.operator D.measure (SmoothField.toL2 D s.Λx)),
      coe_operator_of D C.rCoeff (SmoothField.coe_toL2 D s.v.derivativeX),
      coe_operator_of D C.pCoeff (SmoothField.coe_toL2 D s.Λx),
      ae_restrict_mem D.openSet_open.measurableSet] with x hleft hsub hr hp hx
    simp only [Pi.sub_apply,hr,hp,SpatialAbsorption.rCoeff_value,SpatialAbsorption.pCoeff_value] at hsub
    exact hleft.trans ((hauxX x hx).trans hsub.symm)
  · change physicalY D.measure C dU.ψy = C.pCoeff.operator D.measure
      ((spatialDomain D).componentY (fieldOfSmooth D s.v)) - C.rCoeff.operator D.measure U.Λy
    erw [componentY_toL2]
    rw [hdrep.ψy,hrep.Λy]
    apply Lp.ext
    filter_upwards [SmoothField.coe_toL2 D ds.ψy,
      Lp.coeFn_sub (C.pCoeff.operator D.measure (SmoothField.toL2 D s.v.derivativeY))
        (C.rCoeff.operator D.measure (SmoothField.toL2 D s.Λy)),
      coe_operator_of D C.pCoeff (SmoothField.coe_toL2 D s.v.derivativeY),
      coe_operator_of D C.rCoeff (SmoothField.coe_toL2 D s.Λy),
      ae_restrict_mem D.openSet_open.measurableSet] with x hleft hsub hp hr hx
    simp only [Pi.sub_apply,hp,hr,SpatialAbsorption.rCoeff_value,SpatialAbsorption.pCoeff_value] at hsub
    exact hleft.trans ((hauxY x hx).trans hsub.symm)


/-- 同一 SmoothStateData 的原层坐标，不另取独立状态。 -/
def smoothCoordinatesBase (B : SmoothStateData) (t : ℝ) : SmoothStateCoordinates :=
  ⟨B.v.value t,B.V.value t,B.R.value t,B.z.value t,
    B.φx.value t,B.φy.value t,B.Λx.value t,B.Λy.value t⟩
/-- 同源第一导数层的光滑坐标。 -/
def smoothCoordinatesFirst (B : SmoothStateData) (t : ℝ) : SmoothStateCoordinates :=
  ⟨B.v.first t,B.V.first t,B.R.first t,B.z.first t,
    B.φx.first t,B.φy.first t,B.Λx.first t,B.Λy.first t⟩
/-- 同源第二导数数据，只在时间正则性允许处用作导数。 -/
def smoothCoordinatesSecond (B : SmoothStateData) (t : ℝ) : SmoothStateCoordinates :=
  ⟨B.v.second t,B.V.second t,B.R.second t,B.z.second t,
    B.φx.second t,B.φy.second t,B.Λx.second t,B.Λy.second t⟩

/-- 原层物理表示。零区条件来自上游的保持定理，不由权重的名字推断。 -/
theorem represented_smoothBase (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B) (t : ℝ)
    (hx : ∀ᵐ x ∂D.measure, C.wx x=0 → B.φx.value t x=0)
    (hy : ∀ᵐ x ∂D.measure, C.wy x=0 → B.φy.value t x=0) :
    StateRepresented D C (smoothStateBase D C B reg t) (smoothCoordinatesBase B t) := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,rfl,rfl⟩
  · exact weighted_smooth_recovery D C.wx C.wx_measurable C.wx_gap
      (B.φx.value t) (reg.weightedX.mem_value t) hx
  · exact weighted_smooth_recovery D C.wy C.wy_measurable C.wy_gap
      (B.φy.value t) (reg.weightedY.mem_value t) hy

/-- 第一导数层的同一恢复，要求该层本身的实际零区证据。 -/
theorem represented_smoothFirst (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B) (t : ℝ)
    (hx : ∀ᵐ x ∂D.measure, C.wx x=0 → B.φx.first t x=0)
    (hy : ∀ᵐ x ∂D.measure, C.wy x=0 → B.φy.first t x=0) :
    StateRepresented D C (smoothStateFirst D C B reg t) (smoothCoordinatesFirst B t) := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,rfl,rfl⟩
  · exact weighted_smooth_recovery D C.wx C.wx_measurable C.wx_gap
      (B.φx.first t) (reg.weightedX.mem_first t) hx
  · exact weighted_smooth_recovery D C.wy C.wy_measurable C.wy_gap
      (B.φy.first t) (reg.weightedY.mem_first t) hy

/-- 把实际八组时间场读成 (2.6) 的 primitive 场，不包含方程断言。 -/
def smoothPrimitiveFields (B : SmoothStateData) : Concrete.PrimitiveFields where
  u := fun t x => B.v.value t x
  E := fun t x => B.V.value t x
  P := fun t x => B.R.value t x
  q := fun t x => B.z.value t x
  Λx := fun t x => B.Λx.value t x
  Λy := fun t x => B.Λy.value t x
  φx := fun t x => B.φx.value t x
  φy := fun t x => B.φy.value t x

/-- primitive 的真实 u_t=E、q_t=P 唯一性给出 L² 槽识别。
最终原系统入口中的 primitive 条件由真实历史提升和五不变量保持提供。 -/
theorem primitive_coordinates (D : Rect) (B : SmoothStateData)
    (ε κ τ μ : ℝ) (p r : ℝ → ℝ) (t : ℝ)
    (hprim : ∀ x∈D.openSet, Concrete.PrimitiveAt ε κ τ μ p r (smoothPrimitiveFields B) t x) :
    SmoothField.toL2 D (B.v.first t) = SmoothField.toL2 D (B.V.value t) ∧
    SmoothField.toL2 D (B.z.first t) = SmoothField.toL2 D (B.R.value t) := by
  constructor
  · apply toL2_eq_of_eqOn
    intro x hx
    exact (B.v.deriv_value t x).unique (hprim x hx).du
  · apply toL2_eq_of_eqOn
    intro x hx
    exact (B.z.deriv_value t x).unique (hprim x hx).dq

/-- 已证真实 primitiveAt 的空间装配。时间导数值由 SmoothTimeJet 的
HasDerivAt 与 primitive 导数证据的唯一性识别，不能凭 first 名称认定。
(2.6) 辅助演化再用 Λ=∇u+φ 改写为旧能量框架需要的形式。 -/
theorem primitiveAt_from_smooth (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (ε κ τ μ : ℝ) (p r : ℝ → ℝ)
    (hp : ∀ x, C.p x=p x.1) (hr : ∀ x, C.r x=r x.2) (t : ℝ)
    (hzeroX : ∀ᵐ x ∂D.measure, C.wx x=0 → B.φx.value t x=0)
    (hzeroY : ∀ᵐ x ∂D.measure, C.wy x=0 → B.φy.value t x=0)
    (hzeroFirstX : ∀ᵐ x ∂D.measure, C.wx x=0 → B.φx.first t x=0)
    (hzeroFirstY : ∀ᵐ x ∂D.measure, C.wy x=0 → B.φy.first t x=0)
    (hprim : ∀ x∈D.openSet, Concrete.PrimitiveAt ε κ τ μ p r (smoothPrimitiveFields B) t x) :
    PrimitiveAtConditional (greenDomain D) C ε κ τ μ
      (smoothStateBase D C B reg t) (smoothStateFirst D C B reg t)
      (fieldOfSmooth D (B.v.value t)) (fluxOfSmooth D (B.Λx.value t) (B.Λy.value t)) := by
  apply primitive_of_pointwise D C ε κ τ μ _ _
    (smoothCoordinatesBase B t) (smoothCoordinatesFirst B t)
    (represented_smoothBase D C B reg t hzeroX hzeroY)
    (represented_smoothFirst D C B reg t hzeroFirstX hzeroFirstY)
  · intro x hx
    have hE := (B.V.deriv_value t x).unique (hprim x hx).dE
    have hP := (B.R.deriv_value t x).unique (hprim x hx).dP
    have hmain := (hprim x hx).main
    change μ*(ε*(B.V.first t x+C.a x*B.V.value t x+C.b x*B.v.value t x)+
      B.R.first t x+C.a x*B.R.value t x+C.b x*B.z.value t x) = _
    rw [hE,hP]
    simpa only [SpatialAbsorption.a,SpatialAbsorption.b,absorptionSum,absorptionProduct,
      hp,hr,Concrete.fluxDiv,Concrete.spaceDx,Concrete.spaceDy,smoothPrimitiveFields,
      dx,dy,smoothCoordinatesBase] using hmain
  · intro x hx
    exact (hprim x hx).polar
  · intro x hx
    exact (hprim x hx).fluxX
  · intro x hx
    exact (hprim x hx).fluxY
  · intro x hx
    have hφ := (B.φx.deriv_value t x).unique (hprim x hx).dφx
    have hflux := (hprim x hx).fluxX
    change B.φx.first t x=C.r x*dx (B.v.value t) x-C.p x*B.Λx.value t x
    rw [hp,hr]
    change B.φx.first t x=(r x.2-p x.1)*dx (B.v.value t) x-p x.1*B.φx.value t x at hφ
    change B.Λx.value t x=dx (B.v.value t) x+B.φx.value t x at hflux
    rw [hφ,hflux]
    ring
  · intro x hx
    have hφ := (B.φy.deriv_value t x).unique (hprim x hx).dφy
    have hflux := (hprim x hx).fluxY
    change B.φy.first t x=C.p x*dy (B.v.value t) x-C.r x*B.Λy.value t x
    rw [hp,hr]
    change B.φy.first t x=(p x.1-r x.2)*dy (B.v.value t) x-r x.2*B.φy.value t x at hφ
    change B.Λy.value t x=dy (B.v.value t) x+B.φy.value t x at hflux
    rw [hφ,hflux]
    ring

/-- 闭区间静态数据的中间输出包：由原方程、初始兼容保持和两层迹产生。
它不是原系统解/正则性的定义；最高入口必须证明这些全时段关系。
T=0 时，所需初始图状态兼容仍有实质内容，不由空内部方程推出。 -/
structure SmoothStaticAt (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (κ τ : ℝ) (s : SmoothStateCoordinates) : Prop where
  polar : ∀ x∈D.openSet, s.z x+τ*s.R x=κ*s.v x
  spatialX : ∀ x∈D.openSet, s.Λx x=dx s.v x+s.ψx x
  spatialY : ∀ x∈D.openSet, s.Λy x=dy s.v x+s.ψy x
  boundary : ZeroBoundary D s.v
  zeroX : ∀ᵐ x ∂D.measure, C.wx x=0 → s.ψx x=0
  zeroY : ∀ᵐ x ∂D.measure, C.wy x=0 → s.ψy x=0



/-- 光滑代表的 L² 相同会给出闭矩形上相同的连续值，因此零迹不依赖代表。
这是实际空间分析的结果，不允许任意 L² 代表元直接读取边界。 -/
theorem zeroBoundary_of_toL2_eq (D : Rect) (f g : SmoothField)
    (heq : SmoothField.toL2 D f = SmoothField.toL2 D g)
    (hzero : ZeroBoundary D g) : ZeroBoundary D f := by
  apply (smoothTrace_eq_zero_iff D f).mp
  rw [smoothTrace_independent D f g heq]
  exact (smoothTrace_eq_zero_iff D g).mpr hzero

/-- 在开时间集合中对 PEC 求真实时间导数。零迹在邻域成立才可求导；
这条不涉及端点，也不从 T=0 的空内部条件推出端点导数。 -/
theorem zeroBoundary_first_on_open (D : Rect) (J : SmoothTimeJet)
    (I : Set ℝ) (hI : IsOpen I) (hzero : ∀ s∈I, ZeroBoundary D (J.value s))
    {t : ℝ} (ht : t∈I) : ZeroBoundary D (J.first t) := by
  apply (zeroBoundary_iff_forall_boundary D (J.first t)).mpr
  intro x hx
  have hnear : (fun s => J.value s x) =ᶠ[𝓝 t] (fun _ => (0:ℝ)) :=
    Filter.mem_of_superset (hI.mem_nhds ht) (fun s hs =>
      (zeroBoundary_iff_forall_boundary D (J.value s)).mp (hzero s hs) x hx)
  have hzero_derivative : HasDerivAt (fun s => J.value s x) 0 t :=
    (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hnear
  exact (J.deriv_value t x).unique hzero_derivative

/-- 真正兑现 v0.3 的全部空间路径字段。梯度/散度交换来自联合光滑性
和 C(K)→L² 求导；两层零迹使用 u/E 的迹与对 PEC 的真实求导。
本桥接的零区/静态关系是上游原模型保持定理的输出，不能当作原解定义。 -/
def smoothSpatialPath (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (I : Set ℝ) (hI : IsOpen I) (hzero : SmoothZeroOn D C B I)
    (hv : ∀ t∈I, SmoothField.toL2 D (B.v.first t)=SmoothField.toL2 D (B.V.value t))
    (hq : ∀ t∈I, SmoothField.toL2 D (B.z.first t)=SmoothField.toL2 D (B.R.value t))
    (hboundaryBase : ∀ t∈I, ZeroBoundary D (B.v.value t))
    (hboundaryFirst : ∀ t∈I, ZeroBoundary D (B.v.first t)) :
    ConditionalSpatialPath (greenDomain D) C
      (smoothSameSourcePath D C B reg I hI hzero hv hq) := by
  have hcomponentX (f : SmoothField) :
      (greenDomain D).spatial.componentX (fieldOfSmooth D f) =
        SmoothField.toL2 D f.derivativeX := componentX_toL2 D f
  have hcomponentY (f : SmoothField) :
      (greenDomain D).spatial.componentY (fieldOfSmooth D f) =
        SmoothField.toL2 D f.derivativeY := componentY_toL2 D f
  have hboundaryV : ∀ t∈I, ZeroBoundary D (B.V.value t) := by
    intro t ht
    exact zeroBoundary_of_toL2_eq D _ _ (hv t ht).symm (hboundaryFirst t ht)
  have htrace (f : SmoothField) (hf : ZeroBoundary D f) :
      (greenDomain D).trace (fieldOfSmooth D f)=0 := by
    change trace D (fieldOfSmooth D f)=0
    erw [trace_toL2]
    exact (smoothTrace_eq_zero_iff D f).mpr hf
  refine {
    base_v := fun t => fieldOfSmooth D (B.v.value t)
    base_V := fun t => fieldOfSmooth D (B.V.value t)
    first_v := fun t => fieldOfSmooth D (B.v.first t)
    first_V := fun t => fieldOfSmooth D (B.V.first t)
    base_flux := fun t => fluxOfSmooth D (B.Λx.value t) (B.Λy.value t)
    first_flux := fun t => fluxOfSmooth D (B.Λx.first t) (B.Λy.first t)
    base_v_eq := fun _ _ => rfl
    base_V_eq := fun _ _ => rfl
    first_v_eq := fun _ _ => rfl
    first_V_eq := fun _ _ => rfl
    base_flux_eq := fun _ _ => rfl
    first_flux_eq := fun _ _ => rfl
    grad_baseX := ?_
    grad_baseY := ?_
    grad_firstX := ?_
    grad_firstY := ?_
    div_base := ?_
    trace_base_v := fun t ht => htrace _ (hboundaryBase t ht)
    trace_base_V := fun t ht => htrace _ (hboundaryV t ht)
    trace_first_v := fun t ht => htrace _ (hboundaryFirst t ht)
    trace_first_V := fun t ht => htrace _
      (zeroBoundary_first_on_open D B.V I hI hboundaryV ht) }
  · intro t ht
    simp_rw [hcomponentX]
    exact hasDerivAt_jet_gradientX D B.v reg.v t
  · intro t ht
    simp_rw [hcomponentY]
    exact hasDerivAt_jet_gradientY D B.v reg.v t
  · intro t ht
    -- 同源路径的真实导数唯一性将 u_tt 识别为 E_t，再应用同一梯度。
    have hsecond : fieldOfSmooth D (B.v.second t)=fieldOfSmooth D (B.V.first t) :=
      Subtype.ext ((sameSource_first_coordinates_of_mem_interior
        (smoothSameSourcePath D C B reg I hI hzero hv hq) ht).1)
    rw [← hsecond]
    simp_rw [hcomponentX]
    exact hasDerivAt_jet_first_gradientX D B.v reg.v t
  · intro t ht
    have hsecond : fieldOfSmooth D (B.v.second t)=fieldOfSmooth D (B.V.first t) :=
      Subtype.ext ((sameSource_first_coordinates_of_mem_interior
        (smoothSameSourcePath D C B reg I hI hzero hv hq) ht).1)
    rw [← hsecond]
    simp_rw [hcomponentY]
    exact hasDerivAt_jet_first_gradientY D B.v reg.v t
  · intro t ht
    change HasDerivAt (fun s => divergence D (fluxOfSmooth D (B.Λx.value s) (B.Λy.value s)))
      (divergence D (fluxOfSmooth D (B.Λx.first t) (B.Λy.first t))) t
    simp_rw [divergence_ofSmooth]
    exact hasDerivAt_jet_divergence D B.Λx B.Λy reg.Λx reg.Λy t

/-- v0.4.4 的最终框架桥接，不发布 v0.5 的具体能量主定理。
输入为已由原系统推出的 primitiveOn、零区保持、闭区间静态兼容，以及明确
光滑/加权正则性。G 与 Poincaré estimate 均由具体矩形定理填入；真实
SameSourcePath、空间微分交换、连续性和四项迹也在此构造，不能另行传入。
T=0 时仍要求闭区间初始静态兼容，内部 primitive 条件允许为空。 -/
def finiteIntervalProblem_of_smooth (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (ε κ τ μ T : ℝ) (hT : 0≤T) (p r : ℝ→ℝ)
    (hp : ∀ x, C.p x=p x.1) (hr : ∀ x, C.r x=r x.2)
    (hprim : Concrete.PrimitiveOn D.openSet T ε κ τ μ p r (smoothPrimitiveFields B))
    (hzero : SmoothZeroOn D C B (Ioo 0 T))
    (hstaticBase : ∀ t∈Icc 0 T,
      SmoothStaticAt D C κ τ (smoothCoordinatesBase B t))
    (hstaticFirst : ∀ t∈Icc 0 T,
      SmoothStaticAt D C κ τ (smoothCoordinatesFirst B t)) :
    FiniteIntervalProblemConditional (greenDomain D) C ε κ τ μ
      (poincareConstant D) T (poincare_estimate D) := by
  let hv := fun t ht => (primitive_coordinates D B ε κ τ μ p r t (hprim t ht)).1
  let hq := fun t ht => (primitive_coordinates D B ε κ τ μ p r t (hprim t ht)).2
  let path := smoothSameSourcePath D C B reg (Ioo 0 T) isOpen_Ioo hzero hv hq
  let regular := smoothSpatialPath D C B reg (Ioo 0 T) isOpen_Ioo hzero hv hq
    (fun t ht => (hstaticBase t ⟨ht.1.le,ht.2.le⟩).boundary)
    (fun t ht => (hstaticFirst t ⟨ht.1.le,ht.2.le⟩).boundary)
  refine { T_nonneg := hT, path := path, regular := regular
           base_evolution := ?_, continuous_base := ?_, continuous_first := ?_
           static_base := ?_, static_first := ?_ }
  · intro t ht
    exact primitiveAt_from_smooth D C B reg ε κ τ μ p r hp hr t
      (hzero.φx_value t ht) (hzero.φy_value t ht)
      (hzero.φx_first t ht) (hzero.φy_first t ht) (hprim t ht)
  · exact continuous_smoothStateBase D C B reg (Icc 0 T)
  · exact continuous_smoothStateFirst D C B reg (Icc 0 T)
  · intro t ht
    have hs := hstaticBase t ht
    exact static_of_pointwise D C κ τ _ _
      (represented_smoothBase D C B reg t hs.zeroX hs.zeroY)
      hs.polar hs.spatialX hs.spatialY hs.boundary
  · intro t ht
    have hs := hstaticFirst t ht
    exact static_of_pointwise D C κ τ _ _
      (represented_smoothFirst D C B reg t hs.zeroX hs.zeroY)
      hs.polar hs.spatialX hs.spatialY hs.boundary

/-- 上述具体构造还给出积分平衡所需的真实 P_tt 的 L² 连续性。
这是统一时间正则性的结果；不把最终耗散可积或积分平衡当作输入。 -/
theorem finiteIntervalProblem_second_R_continuous
    (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (B : SmoothStateData) (reg : SmoothStateRegular D C B)
    (ε κ τ μ T : ℝ) (hT : 0≤T) (p r : ℝ→ℝ)
    (hp : ∀ x, C.p x=p x.1) (hr : ∀ x, C.r x=r x.2)
    (hprim : Concrete.PrimitiveOn D.openSet T ε κ τ μ p r (smoothPrimitiveFields B))
    (hzero : SmoothZeroOn D C B (Ioo 0 T))
    (hstaticBase : ∀ t∈Icc 0 T,
      SmoothStaticAt D C κ τ (smoothCoordinatesBase B t))
    (hstaticFirst : ∀ t∈Icc 0 T,
      SmoothStaticAt D C κ τ (smoothCoordinatesFirst B t)) :
    ContinuousOn (fun t => ((finiteIntervalProblem_of_smooth D C B reg ε κ τ μ T hT
      p r hp hr hprim hzero hstaticBase hstaticFirst).path.second t).R) (Icc 0 T) :=
  (continuous_jet_L2 D B.R reg.R).2.2.continuousOn

end LeanPML.Rectangle
