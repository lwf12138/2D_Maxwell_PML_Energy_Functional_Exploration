import LeanPML.PML.BalanceInterfaces

/-!
# V7 (6.3)：同源时间导数层的 primitive 演化

这里对时间邻域中成立的实际 L² 方程求导。主方程的系数乘子固定于时间；
梯度、散度的时间交换仅通过 BalanceInterfaces 中逐项列明的条件接口使用。
没有将“导数层满足同一 PDE”作为最终输入，也没有输入目标能量律。
-/

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace
open LeanPML.Analysis

namespace LeanPML.PML

variable {α : Type*} [MeasurableSpace α]

/-- 由 V7 (6.1) 推出，原文未单列：邻域内的 L² 极化约束可微，
则导数数据仍满足相同约束。单点相等不足，hnear 是必要的邻域证据。 -/
theorem polarConstraint_derivative_Conditional {ν : Measure α}
    {C : SpatialAbsorption α} (κ τ : ℝ)
    {U : ℝ → FieldState ν C.wx C.wy} {dU : FieldState ν C.wx C.wy} {t : ℝ}
    (hU : StateHasDerivAt U dU t)
    (hnear : ∀ᶠ s in 𝓝 t, PolarConstraint κ τ (U s)) :
    PolarConstraint κ τ dU := by
  have hleft : HasDerivAt (fun s => (U s).z + τ • (U s).R)
      (dU.z + τ • dU.R) t := hU.z.add (hU.R.const_smul τ)
  have hright : HasDerivAt (fun s => κ • (U s).v) (κ • dU.v) t :=
    hU.v.const_smul κ
  have hequal : (fun s => κ • (U s).v) =ᶠ[𝓝 t]
      (fun s => (U s).z + τ • (U s).R) :=
    hnear.mono (fun s hs => Eq.symm hs)
  exact hleft.unique (hright.congr_of_eventuallyEq hequal.symm)

/-- primitive 主方程左侧的实际求导。原层 dU 的导数由 ddU 给出；
固定有界乘子与求导可交换是连续线性映射的 mathlib 法则。
输出仍是同一个 primitiveMain 定义，系数与材料常数没有改变。 -/
theorem hasDerivAt_primitiveMain (ν : Measure α) (C : SpatialAbsorption α) (ε μ : ℝ)
    {U dU : ℝ → FieldState ν C.wx C.wy} {ddU : FieldState ν C.wx C.wy} {t : ℝ}
    (hU : StateHasDerivAt U (dU t) t) (hdU : StateHasDerivAt dU ddU t) :
    HasDerivAt (fun s => primitiveMain ν C ε μ (U s) (dU s))
      (primitiveMain ν C ε μ (dU t) ddU) t := by
  have haV := Analysis.hasDerivAt_operator (C.aCoeff.operator ν) hU.V
  have hbv := Analysis.hasDerivAt_operator (C.bCoeff.operator ν) hU.v
  have haR := Analysis.hasDerivAt_operator (C.aCoeff.operator ν) hU.R
  have hbz := Analysis.hasDerivAt_operator (C.bCoeff.operator ν) hU.z
  have helectric := ((hdU.V.add haV).add hbv).const_smul ε
  have hcombined := ((helectric.add hdU.R).add haR).add hbz
  exact hcombined.const_smul μ

/-- V7 primitive 演化在某个时刻的实际 L² 命题。
域内 v、Λ 已由空间路径接口与状态联系；辅助方程使用普通物理分量的导数，
但 dU.ψ 自身仍必须由加权空间中的真实 HasDerivAt 取得。 -/
structure PrimitiveAtConditional {ν : Measure α} {Boundary : Type*}
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    (U dU : FieldState ν C.wx C.wy) (v : G.spatial.domain) (Λ : G.fluxDomain) : Prop where
  main : primitiveMain ν C ε μ U dU = G.divergence Λ
  polar : PolarConstraint κ τ U
  spatialX : U.Λx = G.spatial.componentX v + physicalX ν C U.ψx
  spatialY : U.Λy = G.spatial.componentY v + physicalY ν C U.ψy
  auxiliaryX : physicalX ν C dU.ψx =
    C.rCoeff.operator ν (G.spatial.componentX v) - C.pCoeff.operator ν U.Λx
  auxiliaryY : physicalY ν C dU.ψy =
    C.pCoeff.operator ν (G.spatial.componentY v) - C.rCoeff.operator ν U.Λy

/-- (6.3) 中导数层主方程的真实推导。原层主方程必须在 t 的邻域成立；
右侧使用显式 div/time 交换，左侧使用上条连续乘子求导，再由导数唯一性得结论。 -/
theorem primitiveMain_first_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    {G : ConditionalGreenDomain ν Boundary} {C : SpatialAbsorption α} {I : Set ℝ}
    (ε μ : ℝ) (path : SameSourcePath ν C.wx C.wy I)
    (regular : ConditionalSpatialPath G C path) {t : ℝ} (ht : t ∈ interior I)
    (hmain : ∀ s ∈ I, primitiveMain ν C ε μ (path.base s) (path.first s) =
      G.divergence (regular.base_flux s)) :
    primitiveMain ν C ε μ (path.first t) (path.second t) =
      G.divergence (regular.first_flux t) := by
  have ht_mem : t ∈ I := interior_subset ht
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ I := mem_interior_iff_mem_nhds.mp ht
  have hleft := hasDerivAt_primitiveMain ν C ε μ
    (path.deriv_base t ht_mem) (path.deriv_first t ht_mem)
  have hequal : (fun s => G.divergence (regular.base_flux s)) =ᶠ[𝓝 t]
      (fun s => primitiveMain ν C ε μ (path.base s) (path.first s)) :=
    hnear.mono (fun s hs => (hmain s hs).symm)
  exact hleft.unique ((regular.div_base t ht).congr_of_eventuallyEq hequal.symm)

/-- 邻域恒等式两侧具有真实空间导数时，导数唯一性给出相同导数。
这是下方空间约束和辅助演化求导的共同步骤；不是从单点等式求导。 -/
theorem derivative_eq_of_eventuallyEq_Conditional
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f g : ℝ → H} {df dg : H} {t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t)
    (heq : f =ᶠ[𝓝 t] g) : df = dg :=
  hf.unique (hg.congr_of_eventuallyEq heq)

/-- V7 (6.3) 的核心条件性结论：对同源原层在 I 内成立的整个 primitive
系统求导，得到导数层系统。t 必须在 I 的内部，以合法使用邻域等式。
main 使用散度交换，spatial 使用梯度交换，auxiliary 使用固定空间乘子。
极化方程只用 z+τR=κv；没有额外加入教学 Debye 方程。 -/
theorem primitive_first_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    {G : ConditionalGreenDomain ν Boundary} {C : SpatialAbsorption α} {I : Set ℝ}
    (ε κ τ μ : ℝ) (path : SameSourcePath ν C.wx C.wy I)
    (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    PrimitiveAtConditional G C ε κ τ μ (path.first t) (path.second t)
      (regular.first_v t) (regular.first_flux t) := by
  have ht_mem : t ∈ I := interior_subset ht
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ I := mem_interior_iff_mem_nhds.mp ht
  have hbase_deriv := path.deriv_base t ht_mem
  have hfirst_deriv := path.deriv_first t ht_mem
  have hphysical_baseX := (physicalX ν C).hasFDerivAt.comp_hasDerivAt t hbase_deriv.ψx
  have hphysical_baseY := (physicalY ν C).hasFDerivAt.comp_hasDerivAt t hbase_deriv.ψy
  have hphysical_firstX := (physicalX ν C).hasFDerivAt.comp_hasDerivAt t hfirst_deriv.ψx
  have hphysical_firstY := (physicalY ν C).hasFDerivAt.comp_hasDerivAt t hfirst_deriv.ψy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact primitiveMain_first_Conditional ε μ path regular ht
      (fun s hs => (hbase s hs).main)
  · exact polarConstraint_derivative_Conditional κ τ hbase_deriv
      (hnear.mono (fun s hs => (hbase s hs).polar))
  · -- 对 Λx=∂xv+ψx 求导；这里 ∂x 的时间交换是明示空间接口。
    exact derivative_eq_of_eventuallyEq_Conditional hbase_deriv.Λx
      ((regular.grad_baseX t ht).add hphysical_baseX)
      (hnear.mono (fun s hs => (hbase s hs).spatialX))
  · exact derivative_eq_of_eventuallyEq_Conditional hbase_deriv.Λy
      ((regular.grad_baseY t ht).add hphysical_baseY)
      (hnear.mono (fun s hs => (hbase s hs).spatialY))
  · -- x 演化为 r∂xv−pΛx，方向次序不交换；r、p 的乘子与时间无关。
    have hright := (Analysis.hasDerivAt_operator (C.rCoeff.operator ν)
      (regular.grad_baseX t ht)).sub
      (Analysis.hasDerivAt_operator (C.pCoeff.operator ν) hbase_deriv.Λx)
    exact derivative_eq_of_eventuallyEq_Conditional hphysical_firstX hright
      (hnear.mono (fun s hs => (hbase s hs).auxiliaryX))
  · have hright := (Analysis.hasDerivAt_operator (C.pCoeff.operator ν)
      (regular.grad_baseY t ht)).sub
      (Analysis.hasDerivAt_operator (C.rCoeff.operator ν) hbase_deriv.Λy)
    exact derivative_eq_of_eventuallyEq_Conditional hphysical_firstY hright
      (hnear.mono (fun s hs => (hbase s hs).auxiliaryY))

end LeanPML.PML
