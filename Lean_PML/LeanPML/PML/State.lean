import LeanPML.Analysis.WeightedL2

/-!
# V7 (6.1)、(6.3) 的实际场状态与时间路径

各标量槽属于实际 L²；ψ 用 WeightedL2 的平方根坐标表示。
二维场用两个标量分量，平方长度在 Energy 中明确相加，不使用乘积类型的 max 范数。
权重是空间函数，不是时间函数；它们的物理构造见 SpatialCoefficients。

阅读顺序：FieldState → StateHasDerivAt → SameSourcePath。
这里先分开“瞬时坐标”“代数约束”“真实时间导数”。梯度与零迹仅有显式接口，
尚未构造矩形 Sobolev 实现；结构中没有能量律、正定性或单调性字段。
-/

noncomputable section
open MeasureTheory
open scoped Topology
open LeanPML.Analysis

namespace LeanPML.PML

variable {α : Type*} [MeasurableSpace α]

/-- V7 (6.1) 的瞬时状态。V 是速度槽，R 的导数尚不在该状态中。
ψx、ψy 保存 √w ψ 的实际 L² 商类；Λ 的两分量为普通 L²。
定义本身不声称 V=v_t，也不声称 Λ−ψ 是空间梯度。 -/
structure FieldState (ν : Measure α) (wx wy : α → ℝ) where
  v : ScalarL2 ν
  V : ScalarL2 ν
  R : ScalarL2 ν
  z : ScalarL2 ν
  ψx : WeightedL2 ν wx
  ψy : WeightedL2 ν wy
  Λx : ScalarL2 ν
  Λy : ScalarL2 ν

/-- V7 (6.1) 的未求导代数约束 z+τR=κv。
这是状态可选的约束，而不是能量律；使用 L² 等价类相等，即全域 a.e. 相等。 -/
def PolarConstraint {ν : Measure α} {wx wy : α → ℝ}
    (κ τ : ℝ) (U : FieldState ν wx wy) : Prop :=
  U.z + τ • U.R = κ • U.v

/-- 由 (6.6) 所需时间正则性提取的一阶接口，原文未单列。
每个导数值由 HasDerivAt 绑定到对应实际空间路径；
ψ 的导数在加权范数中成立，不能由普通 L² 或逐点可导自动得到。 -/
structure StateHasDerivAt {ν : Measure α} {wx wy : α → ℝ}
    (U : ℝ → FieldState ν wx wy) (dU : FieldState ν wx wy) (t : ℝ) : Prop where
  v : HasDerivAt (fun s => (U s).v) dU.v t
  V : HasDerivAt (fun s => (U s).V) dU.V t
  R : HasDerivAt (fun s => (U s).R) dU.R t
  z : HasDerivAt (fun s => (U s).z) dU.z t
  ψx : HasDerivAt (fun s => (U s).ψx) dU.ψx t
  ψy : HasDerivAt (fun s => (U s).ψy) dU.ψy t
  Λx : HasDerivAt (fun s => (U s).Λx) dU.Λx t
  Λy : HasDerivAt (fun s => (U s).Λy) dU.Λy t

/-- V7 (6.3) 的同源两层路径。I 指定时间集合；未强迫全实轴满足方程。
base 对应 (u,E,P,q,φ,λ)，first 是它的真实导数层，second 是 first 的导数数据。
velocity 与 primitivePolar 分别给出 u_t=E、q_t=P。
未输入或证明“first 满足同一 primitive PDE”，这留给 v0.3.2。 -/
structure SameSourcePath (ν : Measure α) (wx wy : α → ℝ) (I : Set ℝ) where
  base : ℝ → FieldState ν wx wy
  first : ℝ → FieldState ν wx wy
  second : ℝ → FieldState ν wx wy
  deriv_base : ∀ t ∈ I, StateHasDerivAt base (first t) t
  deriv_first : ∀ t ∈ I, StateHasDerivAt first (second t) t
  velocity : ∀ t ∈ I, HasDerivAt (fun s => (base s).v) (base t).V t
  primitivePolar : ∀ t ∈ I, HasDerivAt (fun s => (base s).z) (base t).R t

/-- V7 (6.3) 同源对应的分析结论：导数唯一性给出 U₁.v=E、U₁.z=P。
U₀ 的 R_t 是 first.R=P_t；U₁ 的 R_t 是 second.R=P_tt，
均由上方真实路径证据取得，而不是因坐标名字含 t。 -/
theorem sameSource_coordinates {ν : Measure α} {wx wy : α → ℝ} {I : Set ℝ}
    (path : SameSourcePath ν wx wy I) {t : ℝ} (ht : t ∈ I) :
    (path.first t).v = (path.base t).V ∧
      (path.first t).z = (path.base t).R := by
  have hv_deriv := (path.deriv_base t ht).v
  have hz_deriv := (path.deriv_base t ht).z
  exact ⟨hv_deriv.unique (path.velocity t ht),
    hz_deriv.unique (path.primitivePolar t ht)⟩

/-- 由 V7 (6.3) 推出，原文未单列：在时间集合的内部，导数层也满足
自身的 v_t=V、z_t=R 时间坐标对应，即 second.v=first.V、second.z=first.R。
必须使用 t∈interior I：这样上一条坐标等式在 t 的邻域成立，才能传递导数。
这只核验同源时间坐标，不证明导数层满足同一 primitive PDE。 -/
theorem sameSource_first_coordinates_of_mem_interior
    {ν : Measure α} {wx wy : α → ℝ} {I : Set ℝ}
    (path : SameSourcePath ν wx wy I) {t : ℝ} (ht : t ∈ interior I) :
    (path.second t).v = (path.first t).V ∧
      (path.second t).z = (path.first t).R := by
  have ht_mem : t ∈ I := interior_subset ht
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ I := mem_interior_iff_mem_nhds.mp ht
  -- 把逐个 s∈I 的坐标等式升级成邻域等式，不能只用 t 处的相等。
  have hvelocity_eq : (fun s => (path.first s).v) =ᶠ[𝓝 t]
      (fun s => (path.base s).V) :=
    hnear.mono (fun s hs => (sameSource_coordinates path hs).1)
  have hpolar_eq : (fun s => (path.first s).z) =ᶠ[𝓝 t]
      (fun s => (path.base s).R) :=
    hnear.mono (fun s hs => (sameSource_coordinates path hs).2)
  -- 原层 V、R 的真实导数，沿邻域相等传递到导数层的 v、z。
  have hfirst_v : HasDerivAt (fun s => (path.first s).v) (path.first t).V t :=
    ((path.deriv_base t ht_mem).V).congr_of_eventuallyEq hvelocity_eq
  have hfirst_z : HasDerivAt (fun s => (path.first s).z) (path.first t).R t :=
    ((path.deriv_base t ht_mem).R).congr_of_eventuallyEq hpolar_eq
  exact ⟨((path.deriv_first t ht_mem).v).unique hfirst_v,
    ((path.deriv_first t ht_mem).z).unique hfirst_z⟩

/-- 条件性空间接口：在指定算子定义域中保存两个梯度分量。
这里只是有定义域的线性接口，不把它命名为已实现的矩形弱梯度。
后续必须以 H₀¹、弱导数和零迹构造具体实例；当前不含 Green 或 Poincaré。 -/
structure ConditionalSpatialDomain (ν : Measure α) where
  domain : Submodule ℝ (ScalarL2 ν)
  componentX : domain →ₗ[ℝ] ScalarL2 ν
  componentY : domain →ₗ[ℝ] ScalarL2 ν

/-- V7 (6.1) 的 Λ=∇v+ψ，当前使用上述条件性空间域。
physicalX/Y 必须是 WeightedL2 的已证明零延拓映射；Energy 中由物理系数构造。
这里不要求空间导数在整个 L² 上有界，也不暗藏目标能量结论。 -/
structure ConditionalSpatialConstraint {ν : Measure α} {wx wy : α → ℝ}
    (spatial : ConditionalSpatialDomain ν)
    (physicalX : WeightedL2 ν wx →L[ℝ] ScalarL2 ν)
    (physicalY : WeightedL2 ν wy →L[ℝ] ScalarL2 ν)
    (U : FieldState ν wx wy) : Prop where
  mem_domain : U.v ∈ spatial.domain
  fluxX : U.Λx = spatial.componentX ⟨U.v, mem_domain⟩ + physicalX U.ψx
  fluxY : U.Λy = spatial.componentY ⟨U.v, mem_domain⟩ + physicalY U.ψy

end LeanPML.PML
