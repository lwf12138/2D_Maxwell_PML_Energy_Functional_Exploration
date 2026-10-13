import LeanPML.PML.EnergyIntegrals

/-!
# V7 (7.5) 的条件性空间接口与同源路径正则性

本文件把梯度、散度、迹的定义域分开；Green 是一般测试函数—通量关系，
边界配对独立于能量。它们尚待后续矩形 Sobolev 阶段实例化。
路径接口只在时间集合 I 内联系实际状态；I 外的域内延拓没有物理含义。
所有交换条件均写成实际 L² 路径的 HasDerivAt，不从逐点可导推出空间可导。
阅读顺序：ConditionalGreenDomain → ConditionalSpatialPath。
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology
open LeanPML.Analysis

namespace LeanPML.PML

variable {α : Type*} [MeasurableSpace α]

/-- V7 primitive 主方程的左侧 μ[ε(v_tt+av_t+bv)+R_t+aR+bz]。
U、dU 是实际 L² 槽；只有配合 StateHasDerivAt 才有时间导数意义。
a、b 的空间乘法使用已构造的有界乘子，不涉及无界能量权重。 -/
def primitiveMain (ν : Measure α) (C : SpatialAbsorption α) (ε μ : ℝ)
    (U dU : FieldState ν C.wx C.wy) : ScalarL2 ν :=
  μ • (ε • (dU.V + C.aCoeff.operator ν U.V + C.bCoeff.operator ν U.v) +
    dU.R + C.aCoeff.operator ν U.R + C.bCoeff.operator ν U.z)

/-- V7 (7.5) 所需的一般 Green 接口，当前是条件而非已证矩形定理。
spatial.domain 是梯度定义域；fluxDomain 是散度定义域，两者不必等于整个 L²。
Boundary 是边界数据空间，trace 和 boundary 独立给出迹及双线性配对。
green 仅表达 ⟨v,div Λ⟩=−⟨∇v,Λ⟩+边界项，不含任何能量或耗散。 -/
structure ConditionalGreenDomain (ν : Measure α) (Boundary : Type*)
    [AddCommGroup Boundary] [Module ℝ Boundary] where
  spatial : ConditionalSpatialDomain ν
  fluxDomain : Submodule ℝ (ScalarL2 ν × ScalarL2 ν)
  divergence : fluxDomain →ₗ[ℝ] ScalarL2 ν
  trace : spatial.domain →ₗ[ℝ] Boundary
  boundary : Boundary →ₗ[ℝ] fluxDomain →ₗ[ℝ] ℝ
  green : ∀ (v : spatial.domain) (Λ : fluxDomain),
    ⟪(v : ScalarL2 ν), divergence Λ⟫_ℝ =
      -⟪spatial.componentX v, (Λ : ScalarL2 ν × ScalarL2 ν).1⟫_ℝ -
      ⟪spatial.componentY v, (Λ : ScalarL2 ν × ScalarL2 ν).2⟫_ℝ +
      boundary (trace v) Λ

/-- (7.5) 在零迹下的边界消失是线性代数结论；具体路径是否零迹仍需输入。
这没有将边界项定义为能量残差，且不要求散度在全部 L² 上有界。 -/
theorem boundary_eq_zero_of_trace_zero_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (v : G.spatial.domain) (Λ : G.fluxDomain)
    (htrace : G.trace v = 0) : G.boundary (G.trace v) Λ = 0 := by
  rw [htrace, map_zero]
  rfl

/-- V7 (7.5) 取测试函数 V+cv 的 Green 消去步骤。
定义域是线性子空间，所以这个组合仍在域中；各梯度项来自线性性。
这里保留独立边界配对，尚未施加零迹。 -/
theorem green_multiplier_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (c : ℝ)
    (v V : G.spatial.domain) (Λ : G.fluxDomain) :
    ⟪G.divergence Λ, (V : ScalarL2 ν) + c • (v : ScalarL2 ν)⟫_ℝ +
      ⟪G.spatial.componentX V + c • G.spatial.componentX v,
        (Λ : ScalarL2 ν × ScalarL2 ν).1⟫_ℝ +
      ⟪G.spatial.componentY V + c • G.spatial.componentY v,
        (Λ : ScalarL2 ν × ScalarL2 ν).2⟫_ℝ =
      G.boundary (G.trace (V + c • v)) Λ := by
  have hgreen := G.green (V + c • v) Λ
  simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul] at hgreen
  rw [real_inner_comm ((V : ScalarL2 ν) + c • (v : ScalarL2 ν))]
  simp only [map_add, map_smul]
  linarith

/-- V7 (7.5) 的零迹处理：v 与 V 分别零迹，故乘子 V+cv 零迹。
导数层要另用 E 与 E_t 的零迹，不能由原层的边界结论直接跳过。 -/
theorem boundary_multiplier_zero_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (c : ℝ)
    (v V : G.spatial.domain) (Λ : G.fluxDomain)
    (hv : G.trace v = 0) (hV : G.trace V = 0) :
    G.boundary (G.trace (V + c • v)) Λ = 0 := by
  apply boundary_eq_zero_of_trace_zero_Conditional
  simp only [map_add, map_smul, hv, hV, smul_zero, add_zero]

/-- V7 (6.6)、(6.3) 所需的条件性空间路径接口。
域内路径的 L² 值在 I 内分别等于 u、E、E、E_t 和 λ、λ_t。
grad_base/grad_first、div_base 是尚待具体空间证明的时间交换条件。
零迹逐项列出：原层使用 u、E；导数层使用 E、E_t，不能漏掉第二层边界。 -/
structure ConditionalSpatialPath {ν : Measure α} {Boundary : Type*}
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
    {I : Set ℝ} (path : SameSourcePath ν C.wx C.wy I) where
  base_v : ℝ → G.spatial.domain
  base_V : ℝ → G.spatial.domain
  first_v : ℝ → G.spatial.domain
  first_V : ℝ → G.spatial.domain
  base_flux : ℝ → G.fluxDomain
  first_flux : ℝ → G.fluxDomain
  base_v_eq : ∀ t ∈ I, (base_v t : ScalarL2 ν) = (path.base t).v
  base_V_eq : ∀ t ∈ I, (base_V t : ScalarL2 ν) = (path.base t).V
  first_v_eq : ∀ t ∈ I, (first_v t : ScalarL2 ν) = (path.first t).v
  first_V_eq : ∀ t ∈ I, (first_V t : ScalarL2 ν) = (path.first t).V
  base_flux_eq : ∀ t ∈ I,
    (base_flux t : ScalarL2 ν × ScalarL2 ν) = ((path.base t).Λx, (path.base t).Λy)
  first_flux_eq : ∀ t ∈ I,
    (first_flux t : ScalarL2 ν × ScalarL2 ν) = ((path.first t).Λx, (path.first t).Λy)
  grad_baseX : ∀ t ∈ interior I,
    HasDerivAt (fun s => G.spatial.componentX (base_v s))
      (G.spatial.componentX (first_v t)) t
  grad_baseY : ∀ t ∈ interior I,
    HasDerivAt (fun s => G.spatial.componentY (base_v s))
      (G.spatial.componentY (first_v t)) t
  grad_firstX : ∀ t ∈ interior I,
    HasDerivAt (fun s => G.spatial.componentX (first_v s))
      (G.spatial.componentX (first_V t)) t
  grad_firstY : ∀ t ∈ interior I,
    HasDerivAt (fun s => G.spatial.componentY (first_v s))
      (G.spatial.componentY (first_V t)) t
  div_base : ∀ t ∈ interior I,
    HasDerivAt (fun s => G.divergence (base_flux s))
      (G.divergence (first_flux t)) t
  trace_base_v : ∀ t ∈ I, G.trace (base_v t) = 0
  trace_base_V : ∀ t ∈ I, G.trace (base_V t) = 0
  trace_first_v : ∀ t ∈ I, G.trace (first_v t) = 0
  trace_first_V : ∀ t ∈ I, G.trace (first_V t) = 0

/-- 由同源真实导数的唯一性推出：原层速度与导数层位移在空间域中相同。
这让 grad_base 的输出确实等于 ∇E，而非任意名字为梯度的槽。 -/
theorem base_velocity_eq_first_position_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    {G : ConditionalGreenDomain ν Boundary} {C : SpatialAbsorption α} {I : Set ℝ}
    {path : SameSourcePath ν C.wx C.wy I} (regular : ConditionalSpatialPath G C path)
    {t : ℝ} (ht : t ∈ I) : regular.base_V t = regular.first_v t := by
  apply Subtype.ext
  rw [regular.base_V_eq t ht, regular.first_v_eq t ht]
  exact (sameSource_coordinates path ht).1.symm

end LeanPML.PML
