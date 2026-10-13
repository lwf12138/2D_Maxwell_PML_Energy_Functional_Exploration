import LeanPML.PML.BalanceBlocks
import LeanPML.PML.PrimitiveEvolution

/-!
# V7 (7.6)–(7.8)：条件性空间能量恒等式

阅读顺序：fieldEnergyRate_boundary_Conditional →
hasDerivAt_fieldEnergy_boundary_Conditional → hasDerivAt_energy7_Conditional。
Blocks 已把局部代数接到实际 L²/加权内积；这里代入 primitive 主方程，
用一般 Green 接口消去体积分，再逐层处理零迹。
Green、迹、空间域和时间交换尚待具体矩形实现；本文件不证明 D₇≥0 或单调性。
-/

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace
open LeanPML.Analysis

namespace LeanPML.PML

variable {α : Type*} [MeasurableSpace α]

/-- V7 (7.6)–(7.7) 的空间抵消步骤：实际内积导数值加 D_c 等于独立边界配对。
输入是 primitive 原演化、极化约束及其已求导版本、空间分量演化。
这一条是空间恒等式；下一条用 StateHasDerivAt 绑定真实时间导数。 -/
theorem fieldEnergyRate_boundary_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    (U dU : FieldState ν C.wx C.wy) (v V : G.spatial.domain) (Λ : G.fluxDomain)
    (hκ_ne : κ ≠ 0)
    (hv_value : (v : ScalarL2 ν) = U.v) (hV_value : (V : ScalarL2 ν) = U.V)
    (hΛ_value : (Λ : ScalarL2 ν × ScalarL2 ν) = (U.Λx, U.Λy))
    (hvelocity : dU.v = U.V) (hz : dU.z = U.R)
    (hprimitive : PrimitiveAtConditional G C ε κ τ μ U dU v Λ)
    (hpolar_derived : PolarConstraint κ τ dU)
    (hΛx_derived : dU.Λx = G.spatial.componentX V + physicalX ν C dU.ψx)
    (hΛy_derived : dU.Λy = G.spatial.componentY V + physicalY ν C dU.ψy) :
    fieldEnergyRate ν C ε κ τ μ U dU + fieldDissipation ν C ε κ τ μ U dU.R =
      G.boundary (G.trace (V + C.c • v)) Λ := by
  have hgradientX : spatialComponentX U = G.spatial.componentX v := by
    unfold spatialComponentX
    rw [hprimitive.spatialX]
    abel
  have hgradientY : spatialComponentY U = G.spatial.componentY v := by
    unfold spatialComponentY
    rw [hprimitive.spatialY]
    abel
  have hauxiliaryX : physicalX ν C dU.ψx =
      C.rCoeff.operator ν (spatialComponentX U) - C.pCoeff.operator ν U.Λx := by
    rw [hgradientX]
    exact hprimitive.auxiliaryX
  have hauxiliaryY : physicalY ν C dU.ψy =
      C.pCoeff.operator ν (spatialComponentY U) - C.rCoeff.operator ν U.Λy := by
    rw [hgradientY]
    exact hprimitive.auxiliaryY
  -- 三块求导值保留全部体积配对；没有把边界或物理区贡献设为零。
  have hblocks := fieldEnergyRate_blocks ν C ε κ τ μ U dU
    (G.spatial.componentX V) (G.spatial.componentY V) hκ_ne hvelocity hz
    hprimitive.polar hpolar_derived hauxiliaryX hauxiliaryY hΛx_derived hΛy_derived
  have hgreen := green_multiplier_Conditional G C.c v V Λ
  have hfluxX : (Λ : ScalarL2 ν × ScalarL2 ν).1 = U.Λx := congrArg Prod.fst hΛ_value
  have hfluxY : (Λ : ScalarL2 ν × ScalarL2 ν).2 = U.Λy := congrArg Prod.snd hΛ_value
  rw [hv_value, hV_value, hfluxX, hfluxY] at hgreen
  rw [hprimitive.main, hgradientX, hgradientY] at hblocks
  exact hblocks.trans hgreen

/-- V7 (7.6)：真实空间路径的单层能量导数是 −D_c 加边界配对。
hU 逐个提供普通/加权空间 HasDerivAt；代数约束的求导及梯度交换结果
在同源最终定理中由邻域原方程推出，不是把目标能量公式当作输入。 -/
theorem hasDerivAt_fieldEnergy_boundary_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    {U : ℝ → FieldState ν C.wx C.wy} {dU : FieldState ν C.wx C.wy} {t : ℝ}
    (v V : G.spatial.domain) (Λ : G.fluxDomain) (hκ_ne : κ ≠ 0)
    (hU : StateHasDerivAt U dU t)
    (hv_value : (v : ScalarL2 ν) = (U t).v) (hV_value : (V : ScalarL2 ν) = (U t).V)
    (hΛ_value : (Λ : ScalarL2 ν × ScalarL2 ν) = ((U t).Λx, (U t).Λy))
    (hvelocity : dU.v = (U t).V) (hz : dU.z = (U t).R)
    (hprimitive : PrimitiveAtConditional G C ε κ τ μ (U t) dU v Λ)
    (hpolar_derived : PolarConstraint κ τ dU)
    (hΛx_derived : dU.Λx = G.spatial.componentX V + physicalX ν C dU.ψx)
    (hΛy_derived : dU.Λy = G.spatial.componentY V + physicalY ν C dU.ψy) :
    HasDerivAt (fun s => fieldEnergy ν C ε κ τ μ (U s))
      (-fieldDissipation ν C ε κ τ μ (U t) dU.R +
        G.boundary (G.trace (V + C.c • v)) Λ) t := by
  have hbalance := fieldEnergyRate_boundary_Conditional G C ε κ τ μ (U t) dU
    v V Λ hκ_ne hv_value hV_value hΛ_value hvelocity hz hprimitive hpolar_derived
    hΛx_derived hΛy_derived
  apply (hasDerivAt_fieldEnergy ν C ε κ τ μ hU).congr_deriv
  linarith

/-- V7 (7.6) 的零迹版本：v 和速度 V 各自零迹，使边界配对消失。
结论是真实 HasDerivAt，不包含耗散符号承诺。 -/
theorem hasDerivAt_fieldEnergy_zeroTrace_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α) (ε κ τ μ : ℝ)
    {U : ℝ → FieldState ν C.wx C.wy} {dU : FieldState ν C.wx C.wy} {t : ℝ}
    (v V : G.spatial.domain) (Λ : G.fluxDomain) (hκ_ne : κ ≠ 0)
    (hU : StateHasDerivAt U dU t)
    (hv_value : (v : ScalarL2 ν) = (U t).v) (hV_value : (V : ScalarL2 ν) = (U t).V)
    (hΛ_value : (Λ : ScalarL2 ν × ScalarL2 ν) = ((U t).Λx, (U t).Λy))
    (hvelocity : dU.v = (U t).V) (hz : dU.z = (U t).R)
    (hprimitive : PrimitiveAtConditional G C ε κ τ μ (U t) dU v Λ)
    (hpolar_derived : PolarConstraint κ τ dU)
    (hΛx_derived : dU.Λx = G.spatial.componentX V + physicalX ν C dU.ψx)
    (hΛy_derived : dU.Λy = G.spatial.componentY V + physicalY ν C dU.ψy)
    (hv_zero : G.trace v = 0) (hV_zero : G.trace V = 0) :
    HasDerivAt (fun s => fieldEnergy ν C ε κ τ μ (U s))
      (-fieldDissipation ν C ε κ τ μ (U t) dU.R) t := by
  have hboundary := hasDerivAt_fieldEnergy_boundary_Conditional G C ε κ τ μ
    v V Λ hκ_ne hU hv_value hV_value hΛ_value hvelocity hz hprimitive hpolar_derived
    hΛx_derived hΛy_derived
  rw [boundary_multiplier_zero_Conditional G C.c v V Λ hv_zero hV_zero, add_zero]
    at hboundary
  exact hboundary

/-- V7 (7.8) 的最终条件性两层能量恒等式。
只输入 I 内原层 primitive 演化；导数层由 primitive_first_Conditional 真实求导取得。
u、E、E_t 的域与零迹、空间/时间交换逐项在 regular 中明示。
κ≠0 用于极化块消分母；K 固定为 (5.2) 的 scaleK。
不输入 D₇≥0，故本条不能单独推出能量单调性。 -/
theorem hasDerivAt_energy7_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    (G : ConditionalGreenDomain ν Boundary) (C : SpatialAbsorption α)
    (ε κ τ μ C_P : ℝ) (hκ_ne : κ ≠ 0) {I : Set ℝ}
    (path : SameSourcePath ν C.wx C.wy I) (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    HasDerivAt (energy7 ν C ε κ τ μ C_P path)
      (-dissipation7 ν C ε κ τ μ C_P path t) t := by
  have ht_mem : t ∈ I := interior_subset ht
  have hfirst_all : ∀ s ∈ interior I, PrimitiveAtConditional G C ε κ τ μ
      (path.first s) (path.second s) (regular.first_v s) (regular.first_flux s) :=
    fun s hs => primitive_first_Conditional ε κ τ μ path regular hbase hs
  have hfirst := hfirst_all t ht
  have hbase_coordinates := sameSource_coordinates path ht_mem
  have hfirst_coordinates := sameSource_first_coordinates_of_mem_interior path ht
  -- first 的极化约束在开集 interior I 内成立，故可再次求导得到 second 约束。
  have hnear_interior : ∀ᶠ s in 𝓝 t, s ∈ interior I :=
    isOpen_interior.mem_nhds ht
  have hsecond_polar : PolarConstraint κ τ (path.second t) :=
    polarConstraint_derivative_Conditional κ τ (path.deriv_first t ht_mem)
      (hnear_interior.mono (fun s hs => (hfirst_all s hs).polar))
  have hvelocity_domain := base_velocity_eq_first_position_Conditional regular ht_mem
  have hbase_Λx : (path.first t).Λx =
      G.spatial.componentX (regular.base_V t) + physicalX ν C (path.first t).ψx := by
    rw [hvelocity_domain]
    exact hfirst.spatialX
  have hbase_Λy : (path.first t).Λy =
      G.spatial.componentY (regular.base_V t) + physicalY ν C (path.first t).ψy := by
    rw [hvelocity_domain]
    exact hfirst.spatialY
  -- 对已导出的导数层空间约束再求导；交换条件针对 ∇E 和 ∇E_t，未省略高阶要求。
  have hfirst_physicalX := (physicalX ν C).hasFDerivAt.comp_hasDerivAt t
    (path.deriv_first t ht_mem).ψx
  have hfirst_physicalY := (physicalY ν C).hasFDerivAt.comp_hasDerivAt t
    (path.deriv_first t ht_mem).ψy
  have hfirst_Λx : (path.second t).Λx =
      G.spatial.componentX (regular.first_V t) + physicalX ν C (path.second t).ψx :=
    derivative_eq_of_eventuallyEq_Conditional (path.deriv_first t ht_mem).Λx
      ((regular.grad_firstX t ht).add hfirst_physicalX)
      (hnear_interior.mono (fun s hs => (hfirst_all s hs).spatialX))
  have hfirst_Λy : (path.second t).Λy =
      G.spatial.componentY (regular.first_V t) + physicalY ν C (path.second t).ψy :=
    derivative_eq_of_eventuallyEq_Conditional (path.deriv_first t ht_mem).Λy
      ((regular.grad_firstY t ht).add hfirst_physicalY)
      (hnear_interior.mono (fun s hs => (hfirst_all s hs).spatialY))
  have henergy_base := hasDerivAt_fieldEnergy_zeroTrace_Conditional G C ε κ τ μ
    (regular.base_v t) (regular.base_V t) (regular.base_flux t) hκ_ne
    (path.deriv_base t ht_mem) (regular.base_v_eq t ht_mem)
    (regular.base_V_eq t ht_mem) (regular.base_flux_eq t ht_mem)
    hbase_coordinates.1 hbase_coordinates.2 (hbase t ht_mem) hfirst.polar
    hbase_Λx hbase_Λy (regular.trace_base_v t ht_mem) (regular.trace_base_V t ht_mem)
  have henergy_first := hasDerivAt_fieldEnergy_zeroTrace_Conditional G C ε κ τ μ
    (regular.first_v t) (regular.first_V t) (regular.first_flux t) hκ_ne
    (path.deriv_first t ht_mem) (regular.first_v_eq t ht_mem)
    (regular.first_V_eq t ht_mem) (regular.first_flux_eq t ht_mem)
    hfirst_coordinates.1 hfirst_coordinates.2 hfirst hsecond_polar
    hfirst_Λx hfirst_Λy (regular.trace_first_v t ht_mem) (regular.trace_first_V t ht_mem)
  -- 与 v0.3.1 的同源 energy7 求导入口接通：导数唯一性识别两个内积率。
  have hbase_rate := (hasDerivAt_fieldEnergy ν C ε κ τ μ
    (path.deriv_base t ht_mem)).unique henergy_base
  have hfirst_rate := (hasDerivAt_fieldEnergy ν C ε κ τ μ
    (path.deriv_first t ht_mem)).unique henergy_first
  apply (hasDerivAt_energy7 ν C ε κ τ μ C_P path ht_mem).congr_deriv
  rw [hbase_rate, hfirst_rate]
  simp only [dissipation7, twoLayerDissipation]
  ring

end LeanPML.PML
