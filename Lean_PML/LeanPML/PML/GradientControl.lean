import LeanPML.PML.PrimitiveEvolution

/-!
# V7 §9.2：分配积分 J 与同源路径梯度估计

来源：V7_global_energy.md (9.2)–(9.5)。阅读顺序：fieldJ →
fieldSpatialDissipation_ge_J → gradient_evolution_Conditional → gradient_control_Conditional。
θ 是有界分配系数，和无界能量权重 w 不同；零区 θx=θy=1/2。
状态中的 Λ−ψ 是实际 L² 分量；只有空间约束成立时才等于梯度接口。
本文件先证明点态不等式，再使用可积性及 a.e. 等式合法积分。
最终 (9.5) 从真实同源路径、辅助演化和梯度/时间交换推出；
具体矩形梯度和交换仍是明示接口，不在此宣称已实现 PDE 空间。
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology
open LeanPML.Analysis

namespace LeanPML.PML
variable {α : Type*} [MeasurableSpace α]

namespace SpatialAbsorption

/-- V7 (9.2) 的实际 θx 系数，可测性来自分支定义，界来自旧 theta_partition。
这里构造的是有界 θ 乘子，绝不把无界 w 当作普通 L² 乘子。 -/
def thetaXCoeff (C : SpatialAbsorption α) : BoundedCoefficient α where
  value := fun x => thetaX (C.p x) (C.r x)
  measurable := Measurable.ite (measurableSet_lt measurable_const C.a_measurable)
    (C.p_measurable.div C.a_measurable) measurable_const
  bound := 1
  bound_nonneg := zero_le_one
  abs_le x := by
    have hpartition := theta_partition (C.p x) (C.r x) (C.p_nonneg x) (C.r_nonneg x)
    rw [abs_of_nonneg hpartition.1.1]
    exact hpartition.1.2

/-- V7 (9.2) 的 θy；x 梯度用 θy，而 y 梯度用 θx，方向不能混同。 -/
def thetaYCoeff (C : SpatialAbsorption α) : BoundedCoefficient α where
  value := fun x => thetaY (C.p x) (C.r x)
  measurable := Measurable.ite (measurableSet_lt measurable_const C.a_measurable)
    (C.r_measurable.div C.a_measurable) measurable_const
  bound := 1
  bound_nonneg := zero_le_one
  abs_le x := by
    have hpartition := theta_partition (C.p x) (C.r x) (C.p_nonneg x) (C.r_nonneg x)
    rw [abs_of_nonneg hpartition.2.1.1]
    exact hpartition.2.1.2

end SpatialAbsorption

/-- V7 (9.2) 的单方向密度：θi Λi²+θj hi²，其中 hi 待由空间约束解释。
这是辅助实数定义；其积分调用者 fieldJ 使用真正的 L² 状态。 -/
def directionalJ (p r h l : ℝ) : ℝ := thetaX p r*l^2+thetaY p r*h^2

/-- 由 (9.2) 推出，原文未单列：单方向密度非负只需吸收非负。 -/
theorem directionalJ_nonneg (p r h l : ℝ) (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r) :
    0 ≤ directionalJ p r h l := by
  have hpartition := theta_partition p r hp_nonneg hr_nonneg
  exact add_nonneg (mul_nonneg hpartition.1.1 (sq_nonneg l))
    (mul_nonneg hpartition.2.1.1 (sq_nonneg h))

/-- (9.2) 的方向交换规律；为 y 方向调用同一条点态引理服务。 -/
theorem directionalJ_swap (p r h l : ℝ) :
    directionalJ r p h l = thetaY p r*l^2+thetaX p r*h^2 := by
  simp only [directionalJ, thetaX, thetaY, absorptionSum, add_comm]

/-- V7 (9.2) 的实际密度。Λ、Λ−ψ 均为 L² 商类选定代表；
下方积分/内积对应保证积分不依赖代表选择。 -/
def fieldJDensity (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) (x : α) : ℝ :=
  (thetaX (C.p x) (C.r x)*(U.Λx x)^2+
    thetaY (C.p x) (C.r x)*(spatialComponentX U x)^2) +
  (thetaY (C.p x) (C.r x)*(U.Λy x)^2+
    thetaX (C.p x) (C.r x)*(spatialComponentY U x)^2)

/-- V7 (9.2) 的真实 J：四个有界系数 L² 内积，故定义于 a.e. 商类。
梯度槽采用 Λ−ψ，下一条空间约束引理把它接回梯度定义域。 -/
def fieldJ (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) : ℝ :=
  ⟪C.thetaXCoeff.operator ν U.Λx,U.Λx⟫_ℝ +
  ⟪C.thetaYCoeff.operator ν (spatialComponentX U),spatialComponentX U⟫_ℝ +
  ⟪C.thetaYCoeff.operator ν U.Λy,U.Λy⟫_ℝ +
  ⟪C.thetaXCoeff.operator ν (spatialComponentY U),spatialComponentY U⟫_ℝ

/-- (9.2) 的密度可积：θ 有界且四个场是实际 L²。
不借用不可积函数积分的总定义，也不要求能量权重 w 有界。 -/
theorem fieldJ_integrable (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) : Integrable (fieldJDensity ν C U) ν := by
  have hlx := C.thetaXCoeff.integrable_square ν U.Λx
  have hhx := C.thetaYCoeff.integrable_square ν (spatialComponentX U)
  have hly := C.thetaYCoeff.integrable_square ν U.Λy
  have hhy := C.thetaXCoeff.integrable_square ν (spatialComponentY U)
  exact (hlx.fun_add hhx).fun_add (hly.fun_add hhy)

/-- V7 (9.2) 的积分/内积对应。左边定义在 L² 商类上，因此右边代表元无关。
先取得可积证据，再用 integral_add，不从点态等式直接跳到无条件积分。 -/
theorem fieldJ_eq_integral (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) :
    fieldJ ν C U = ∫ x, fieldJDensity ν C U x ∂ν := by
  have hlx := C.thetaXCoeff.integrable_square ν U.Λx
  have hhx := C.thetaYCoeff.integrable_square ν (spatialComponentX U)
  have hly := C.thetaYCoeff.integrable_square ν U.Λy
  have hhy := C.thetaXCoeff.integrable_square ν (spatialComponentY U)
  simp only [fieldJ, BoundedCoefficient.inner_operator_square]
  simp only [fieldJDensity]
  change _ = ∫ x, (C.thetaXCoeff.value x*(U.Λx x)^2+
    C.thetaYCoeff.value x*(spatialComponentX U x)^2)+
    (C.thetaYCoeff.value x*(U.Λy x)^2+
    C.thetaXCoeff.value x*(spatialComponentY U x)^2) ∂ν
  rw [integral_add (hlx.fun_add hhx) (hly.fun_add hhy),
    integral_add hlx hhx, integral_add hly hhy]
  ring

/-- 由 (9.2) 推出：J 非负来自密度非负，不作为状态结构的输入。 -/
theorem fieldJ_nonneg (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) : 0 ≤ fieldJ ν C U := by
  rw [fieldJ_eq_integral]
  apply integral_nonneg
  intro x
  have hx := directionalJ_nonneg (C.p x) (C.r x) (spatialComponentX U x) (U.Λx x) (C.p_nonneg x) (C.r_nonneg x)
  have hy := directionalJ_nonneg (C.r x) (C.p x) (spatialComponentY U x) (U.Λy x) (C.r_nonneg x) (C.p_nonneg x)
  rw [directionalJ_swap] at hy
  exact add_nonneg hx hy

/-- (6.1) 空间约束使 (9.2) 中的 Λ−ψ 确实等于域接口的梯度。
该等式在实际 L² 商类中成立；具体矩形弱导数仍是后续实现。 -/
theorem spatialComponents_eq_gradient_Conditional (ν : Measure α) (C : SpatialAbsorption α)
    (spatial : ConditionalSpatialDomain ν) (U : FieldState ν C.wx C.wy)
    (hspace : ConditionalSpatialConstraint spatial (physicalX ν C) (physicalY ν C) U) :
    spatialComponentX U = spatial.componentX ⟨U.v,hspace.mem_domain⟩ ∧
    spatialComponentY U = spatial.componentY ⟨U.v,hspace.mem_domain⟩ := by
  constructor
  · unfold spatialComponentX
    rw [hspace.fluxX]
    abel
  · unfold spatialComponentY
    rw [hspace.fluxY]
    abel

/-- (9.2) 后的零区说明：θ=(1/2,1/2)，而加权空间恢复映射使 ψ=0 a.e.。
因此零区 J 密度是两梯度分量平方和，不是零；吸收为零本身没有替代兼容性。 -/
theorem fieldJDensity_zero_region (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) :
    ∀ᵐ x ∂ν, C.a x=0 → fieldJDensity ν C U x =
      (spatialComponentX U x)^2+(spatialComponentY U x)^2 := by
  filter_upwards [physicalL2_zero_on_zero ν C.wx C.wx_measurable C.wx_gap U.ψx,
    physicalL2_zero_on_zero ν C.wy C.wy_measurable C.wy_gap U.ψy,
    Lp.coeFn_sub U.Λx (physicalX ν C U.ψx),
    Lp.coeFn_sub U.Λy (physicalY ν C U.ψy)] with x hzeroX hzeroY hx hy
  intro ha_zero
  have hψx : physicalX ν C U.ψx x=0 := hzeroX ((C.wx_eq_zero_iff x).mpr ha_zero)
  have hψy : physicalY ν C U.ψy x=0 := hzeroY ((C.wy_eq_zero_iff x).mpr ha_zero)
  change spatialComponentX U x=U.Λx x-physicalX ν C U.ψx x at hx
  change spatialComponentY U x=U.Λy x-physicalY ν C U.ψy x at hy
  have hx_eq : spatialComponentX U x=U.Λx x := by simpa only [hψx, sub_zero] using hx
  have hy_eq : spatialComponentY U x=U.Λy x := by simpa only [hψy, sub_zero] using hy
  have hθ := weights_of_sum_zero C.c (C.p x) (C.r x) ha_zero
  simp only [fieldJDensity, hθ.2.2.1, hθ.2.2.2,
    hx_eq, hy_eq]
  ring

/-- 由 (9.2)–(9.3) 推出，原文未单列：正吸收方向的点态耗散控制。
零区另外输入 l=h，此条件来自加权辅助量的零延拓，不是除零约定。
S≥0 在有空间点时由 0≤p≤S 得到。 -/
theorem directional_dissipation_ge_J (c p r S h l : ℝ)
    (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (hp_le_S : p ≤ S) (hr_le_S : r ≤ S)
    (hzero : absorptionSum p r=0 → l=h) :
    (c-S)*directionalJ p r h l ≤ spatialDissipation c p r h l := by
  have hS_nonneg : 0 ≤ S := hp_nonneg.trans hp_le_S
  have hpartition := theta_partition p r hp_nonneg hr_nonneg
  by_cases ha_pos : 0 < absorptionSum p r
  · have ha_ne : absorptionSum p r ≠ 0 := ne_of_gt ha_pos
    have hplus : dissipationPlus c p r = thetaX p r*(c+p) := by
      simp only [dissipationPlus, thetaX, if_pos ha_pos]
      ring
    have hminus : dissipationMinus c r p = thetaY p r*(c-r) := by
      rw [thetaY, if_pos ha_pos]
      simp only [dissipationMinus, absorptionSum, add_comm r p]
      ring
    have hplus_bound : (c-S)*thetaX p r ≤ dissipationPlus c p r := by
      rw [hplus]
      nlinarith [mul_nonneg hpartition.1.1 (add_nonneg hS_nonneg hp_nonneg)]
    have hminus_bound : (c-S)*thetaY p r ≤ dissipationMinus c r p := by
      rw [hminus]
      nlinarith [mul_nonneg hpartition.2.1.1 (sub_nonneg.mpr hr_le_S)]
    have hl_bound := mul_le_mul_of_nonneg_right hplus_bound (sq_nonneg l)
    have hh_bound := mul_le_mul_of_nonneg_right hminus_bound (sq_nonneg h)
    simp only [spatialDissipation, if_pos ha_pos, directionalJ]
    nlinarith only [hl_bound,hh_bound]
  · have ha_zero : absorptionSum p r=0 :=
      le_antisymm (le_of_not_gt ha_pos) (absorptionSum_nonneg p r hp_nonneg hr_nonneg)
    have hl_eq : l=h := hzero ha_zero
    have hθ := weights_of_sum_zero c p r ha_zero
    simp only [spatialDissipation, if_neg ha_pos, directionalJ, hθ.2.2.1,hθ.2.2.2,hl_eq]
    nlinarith [mul_nonneg hS_nonneg (sq_nonneg h)]

/-- V7 (9.3)：已有实际空间耗散同时控制 (c−S)J 和 3cJ/4。
先在统一满测度集合上用零区兼容与两方向点态界，再由可积性取积分。
这一步不需要 Green、Poincaré 或吸收正下界。 -/
theorem fieldSpatialDissipation_ge_J (ν : Measure α) (C : SpatialAbsorption α)
    (U : FieldState ν C.wx C.wy) :
    (C.c-C.S)*fieldJ ν C U ≤ fieldSpatialDissipation ν C U ∧
    (3*C.c/4)*fieldJ ν C U ≤ fieldSpatialDissipation ν C U := by
  have hdensity : ∀ᵐ x ∂ν, (C.c-C.S)*fieldJDensity ν C U x ≤
      fieldSpatialDissipationDensity ν C U x := by
    filter_upwards [physicalL2_zero_on_zero ν C.wx C.wx_measurable C.wx_gap U.ψx,
      physicalL2_zero_on_zero ν C.wy C.wy_measurable C.wy_gap U.ψy,
      Lp.coeFn_sub U.Λx (physicalX ν C U.ψx),
      Lp.coeFn_sub U.Λy (physicalY ν C U.ψy)] with x hzeroX hzeroY hx hy
    change spatialComponentX U x=U.Λx x-physicalX ν C U.ψx x at hx
    change spatialComponentY U x=U.Λy x-physicalY ν C U.ψy x at hy
    have hlx_zero : absorptionSum (C.p x) (C.r x)=0 → U.Λx x=spatialComponentX U x := by
      intro ha_zero
      have hψzero : physicalX ν C U.ψx x=0 := hzeroX ((C.wx_eq_zero_iff x).mpr ha_zero)
      simpa only [hψzero,sub_zero] using hx.symm
    have hly_zero : absorptionSum (C.r x) (C.p x)=0 → U.Λy x=spatialComponentY U x := by
      intro ha_zero
      have hψzero : physicalY ν C U.ψy x=0 := hzeroY ((C.wy_eq_zero_iff x).mpr
        (by simpa only [SpatialAbsorption.a,absorptionSum,add_comm] using ha_zero))
      simpa only [hψzero,sub_zero] using hy.symm
    have hx_bound := directional_dissipation_ge_J C.c (C.p x) (C.r x) C.S
      (spatialComponentX U x) (U.Λx x) (C.p_nonneg x) (C.r_nonneg x)
      (C.p_le_S x) (C.r_le_S x) hlx_zero
    have hy_bound := directional_dissipation_ge_J C.c (C.r x) (C.p x) C.S
      (spatialComponentY U x) (U.Λy x) (C.r_nonneg x) (C.p_nonneg x)
      (C.r_le_S x) (C.p_le_S x) hly_zero
    rw [directionalJ_swap] at hy_bound
    dsimp only [fieldJDensity,fieldSpatialDissipationDensity,spatialDissipation2D]
    dsimp only [directionalJ] at hx_bound
    linarith
  have hlower : (C.c-C.S)*fieldJ ν C U ≤ fieldSpatialDissipation ν C U := by
    rw [fieldJ_eq_integral,fieldSpatialDissipation_eq_integral,← integral_const_mul]
    exact integral_mono_ae ((fieldJ_integrable ν C U).const_mul _) 
      (fieldSpatialDissipation_integrable ν C U) hdensity
  have hfactor : 3*C.c/4 ≤ C.c-C.S := by linarith [C.S_le_quarter]
  have hquarter := mul_le_mul_of_nonneg_right hfactor (fieldJ_nonneg ν C U)
  exact ⟨hlower,hquarter.trans hlower⟩

/-- V7 (9.5) 前的两个系数关系；全部零区和单向吸收都包含在内。
正区消分母前显式取得 a≠0；零区由非负 p,r 与 a=0 得 p=r=0。
这些系数界将在 θ 分配后的三项平方估计中调用。 -/
theorem theta_absorption_square_bounds (p r S : ℝ)
    (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (hp_le_S : p ≤ S) (hr_le_S : r ≤ S) :
    thetaX p r*r^2 ≤ S^2*thetaY p r ∧
    thetaX p r*p^2 ≤ S^2*thetaX p r := by
  have hS_nonneg : 0 ≤ S := hp_nonneg.trans hp_le_S
  have hp_square : p^2 ≤ S^2 := by nlinarith
  have hproduct : p*r ≤ S^2 := by
    calc
      p*r ≤ S*r := mul_le_mul_of_nonneg_right hp_le_S hr_nonneg
      _ ≤ S*S := mul_le_mul_of_nonneg_left hr_le_S hS_nonneg
      _ = S^2 := (pow_two S).symm
  have hpartition := theta_partition p r hp_nonneg hr_nonneg
  constructor
  · by_cases ha_pos : 0 < absorptionSum p r
    · have ha_ne : absorptionSum p r ≠ 0 := ne_of_gt ha_pos
      have hidentity : thetaX p r*r^2 = (p*r)*thetaY p r := by
        simp only [thetaX,thetaY,if_pos ha_pos]
        -- 正区两个比值用同一非零分母；field_simp 只清分母，ring 核验多项式。
        field_simp
      rw [hidentity]
      exact mul_le_mul_of_nonneg_right hproduct hpartition.2.1.1
    · have ha_zero : absorptionSum p r=0 :=
        le_antisymm (le_of_not_gt ha_pos) (absorptionSum_nonneg p r hp_nonneg hr_nonneg)
      have hzero := (absorptionSum_eq_zero_iff p r hp_nonneg hr_nonneg).mp ha_zero
      rw [hzero.2]
      simp only [zero_pow (by decide : 2 ≠ 0),mul_zero]
      exact mul_nonneg (sq_nonneg S) (theta_partition p 0 hp_nonneg le_rfl).2.1.1
  · calc
      thetaX p r*p^2 ≤ thetaX p r*S^2 :=
        mul_le_mul_of_nonneg_left hp_square hpartition.1.1
      _ = S^2*thetaX p r := mul_comm _ _

/-- V7 (9.5) 的单方向代数步骤：h₁=l₁−r h₀+p l₀ 对应 (9.4)。
θx 部分用三项平方和，θy h₁² 留在 J₁ 内；输出仍是点态辅助不等式，
后续 field_gradient_control 才证明可积并取空间积分。 -/
theorem directional_gradient_control (p r S h₀ l₀ h₁ l₁ : ℝ)
    (hp_nonneg : 0 ≤ p) (hr_nonneg : 0 ≤ r)
    (hp_le_S : p ≤ S) (hr_le_S : r ≤ S)
    (hevolution : h₁=l₁-r*h₀+p*l₀) :
    h₁^2 ≤ 3*directionalJ p r h₁ l₁+3*S^2*directionalJ p r h₀ l₀ := by
  have hpartition := theta_partition p r hp_nonneg hr_nonneg
  have hcoeff := theta_absorption_square_bounds p r S hp_nonneg hr_nonneg hp_le_S hr_le_S
  have hsquare : h₁^2 ≤ 3*(l₁^2+r^2*h₀^2+p^2*l₀^2) := by
    rw [hevolution]
    nlinarith only [sq_nonneg (l₁+r*h₀),sq_nonneg (l₁-p*l₀),sq_nonneg (r*h₀+p*l₀)]
  have hweighted := mul_le_mul_of_nonneg_left hsquare hpartition.1.1
  have hcross := mul_le_mul_of_nonneg_right hcoeff.1 (sq_nonneg h₀)
  have hself := mul_le_mul_of_nonneg_right hcoeff.2 (sq_nonneg l₀)
  have hremaining := mul_nonneg hpartition.2.1.1 (sq_nonneg h₁)
  have hsplit : h₁^2=thetaX p r*h₁^2+thetaY p r*h₁^2 := by
    nlinarith only [congrArg (fun k : ℝ => k*h₁^2) hpartition.2.2]
  unfold directionalJ
  nlinarith only [hweighted,hcross,hself,hremaining,hsplit]

/-- 由 (9.4) 推出，原文未单列：L² 乘子等式转成 a.e. 代表函数关系。
此辅助步骤只整理已有场等式，不声称点态求导自动给出 L² 求导。 -/
private theorem field_gradient_evolution_ae (ν : Measure α)
    (p r : BoundedCoefficient α) (h₀ l₀ h₁ l₁ : ScalarL2 ν)
    (hevolution : h₁=l₁-r.operator ν h₀+p.operator ν l₀) :
    ∀ᵐ x ∂ν, h₁ x=l₁ x-r.value x*h₀ x+p.value x*l₀ x := by
  rw [hevolution]
  filter_upwards [Lp.coeFn_add (l₁-r.operator ν h₀) (p.operator ν l₀),
    Lp.coeFn_sub l₁ (r.operator ν h₀),
    coeFn_boundedMul ν r.value r.measurable r.bound r.abs_le h₀,
    coeFn_boundedMul ν p.value p.measurable p.bound p.abs_le l₀]
    with x hadd hsub hr hp
  change (l₁-r.operator ν h₀+p.operator ν l₀) x=
    (l₁-r.operator ν h₀) x+(p.operator ν l₀) x at hadd
  change (l₁-r.operator ν h₀) x=l₁ x-(r.operator ν h₀) x at hsub
  change (r.operator ν h₀) x=r.value x*h₀ x at hr
  change (p.operator ν l₀) x=p.value x*l₀ x at hp
  rw [hadd,hsub,hr,hp]

/-- V7 (9.5) 的实际积分步骤。低层输入两方向 (9.4) 的 L² 等式；
后面的同源主入口将从原辅助演化证明它们，不把目标梯度界作为输入。
四个积分均有 L²/有界 θ 证据，方向 y 正确交换 p,r。 -/
theorem field_gradient_control (ν : Measure α) (C : SpatialAbsorption α)
    (U₀ U₁ : FieldState ν C.wx C.wy)
    (hx_evolution : spatialComponentX U₁=U₁.Λx-
      C.rCoeff.operator ν (spatialComponentX U₀)+C.pCoeff.operator ν U₀.Λx)
    (hy_evolution : spatialComponentY U₁=U₁.Λy-
      C.pCoeff.operator ν (spatialComponentY U₀)+C.rCoeff.operator ν U₀.Λy) :
    ‖spatialComponentX U₁‖^2+‖spatialComponentY U₁‖^2 ≤
      3*fieldJ ν C U₁+3*C.S^2*fieldJ ν C U₀ := by
  have hx_ae := field_gradient_evolution_ae ν C.pCoeff C.rCoeff
    (spatialComponentX U₀) U₀.Λx (spatialComponentX U₁) U₁.Λx hx_evolution
  have hy_ae := field_gradient_evolution_ae ν C.rCoeff C.pCoeff
    (spatialComponentY U₀) U₀.Λy (spatialComponentY U₁) U₁.Λy hy_evolution
  have hpointwise : ∀ᵐ x ∂ν,
      (spatialComponentX U₁ x)^2+(spatialComponentY U₁ x)^2 ≤
        3*fieldJDensity ν C U₁ x+3*C.S^2*fieldJDensity ν C U₀ x := by
    filter_upwards [hx_ae,hy_ae] with x hx hy
    have hx_bound := directional_gradient_control (C.p x) (C.r x) C.S
      (spatialComponentX U₀ x) (U₀.Λx x) (spatialComponentX U₁ x) (U₁.Λx x)
      (C.p_nonneg x) (C.r_nonneg x) (C.p_le_S x) (C.r_le_S x) hx
    have hy_bound := directional_gradient_control (C.r x) (C.p x) C.S
      (spatialComponentY U₀ x) (U₀.Λy x) (spatialComponentY U₁ x) (U₁.Λy x)
      (C.r_nonneg x) (C.p_nonneg x) (C.r_le_S x) (C.p_le_S x) hy
    simp only [directionalJ_swap] at hy_bound
    dsimp only [directionalJ] at hx_bound
    dsimp only [fieldJDensity]
    linarith
  have hhx := (Lp.memLp (spatialComponentX U₁)).integrable_sq
  have hhy := (Lp.memLp (spatialComponentY U₁)).integrable_sq
  have hJ₁ := (fieldJ_integrable ν C U₁).const_mul 3
  have hJ₀ := (fieldJ_integrable ν C U₀).const_mul (3*C.S^2)
  have hintegral := integral_mono_ae (hhx.fun_add hhy) (hJ₁.fun_add hJ₀) hpointwise
  -- 已证可积后拆积分；norm_sq_eq_integral 将左侧接回实际 L² 范数。
  rw [integral_add hhx hhy, integral_add hJ₁ hJ₀,
    integral_const_mul,integral_const_mul,
    ← norm_sq_eq_integral,← norm_sq_eq_integral,
    ← fieldJ_eq_integral,← fieldJ_eq_integral] at hintegral
  exact hintegral

/-- V7 (9.4)：原辅助演化推出 ∂i E=λi,t−σj∂i u+σiλi。
path 的 HasDerivAt 绑定 E、λt 到同一来源；regular.grad_base 提供梯度/时间交换。
邻域原层空间约束的求导由旧 primitive_first_Conditional 完成，不能只微分单点等式。
不使用教学 Debye 子系统方程，也没有把 (9.4) 作为模型输入。 -/
theorem gradient_evolution_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    {G : ConditionalGreenDomain ν Boundary} {C : SpatialAbsorption α} {I : Set ℝ}
    (ε κ τ μ : ℝ) (path : SameSourcePath ν C.wx C.wy I)
    (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    (G.spatial.componentX (regular.first_v t)=(path.first t).Λx-
      C.rCoeff.operator ν (G.spatial.componentX (regular.base_v t))+
      C.pCoeff.operator ν (path.base t).Λx) ∧
    (G.spatial.componentY (regular.first_v t)=(path.first t).Λy-
      C.pCoeff.operator ν (G.spatial.componentY (regular.base_v t))+
      C.rCoeff.operator ν (path.base t).Λy) := by
  have hbase_t := hbase t (interior_subset ht)
  have hfirst_t := primitive_first_Conditional ε κ τ μ path regular hbase ht
  constructor
  · rw [hfirst_t.spatialX,hbase_t.auxiliaryX]
    abel
  · rw [hfirst_t.spatialY,hbase_t.auxiliaryY]
    abel

/-- V7 (9.5) 的最终同源入口：原演化和真实时间导数给出实际梯度范数估计。
first_v 与 E 的对应由 sameSource_coordinates 和 regular.first_v_eq 保证；
输入只含原层 primitive、同源路径及明确空间交换接口；J 可积、非负和
跨层关系都在内部证明。零吸收、单向边层、双向角层使用同一结论。
具体矩形空间算子仍待后续实例化；本条不证明耗散闭合或时间单调性。 -/
theorem gradient_control_Conditional
    {ν : Measure α} {Boundary : Type*} [AddCommGroup Boundary] [Module ℝ Boundary]
    {G : ConditionalGreenDomain ν Boundary} {C : SpatialAbsorption α} {I : Set ℝ}
    (ε κ τ μ : ℝ) (path : SameSourcePath ν C.wx C.wy I)
    (regular : ConditionalSpatialPath G C path)
    (hbase : ∀ s ∈ I, PrimitiveAtConditional G C ε κ τ μ
      (path.base s) (path.first s) (regular.base_v s) (regular.base_flux s))
    {t : ℝ} (ht : t ∈ interior I) :
    ‖G.spatial.componentX (regular.first_v t)‖^2+
      ‖G.spatial.componentY (regular.first_v t)‖^2 ≤
      3*fieldJ ν C (path.first t)+3*C.S^2*fieldJ ν C (path.base t) := by
  have hbase_t := hbase t (interior_subset ht)
  have hfirst_t := primitive_first_Conditional ε κ τ μ path regular hbase ht
  have hbaseX : spatialComponentX (path.base t)=G.spatial.componentX (regular.base_v t) := by
    unfold spatialComponentX
    rw [hbase_t.spatialX]
    abel
  have hbaseY : spatialComponentY (path.base t)=G.spatial.componentY (regular.base_v t) := by
    unfold spatialComponentY
    rw [hbase_t.spatialY]
    abel
  have hfirstX : spatialComponentX (path.first t)=G.spatial.componentX (regular.first_v t) := by
    unfold spatialComponentX
    rw [hfirst_t.spatialX]
    abel
  have hfirstY : spatialComponentY (path.first t)=G.spatial.componentY (regular.first_v t) := by
    unfold spatialComponentY
    rw [hfirst_t.spatialY]
    abel
  have hevolution := gradient_evolution_Conditional ε κ τ μ path regular hbase ht
  have hx_evolution : spatialComponentX (path.first t)=(path.first t).Λx-
      C.rCoeff.operator ν (spatialComponentX (path.base t))+
      C.pCoeff.operator ν (path.base t).Λx := by rw [hfirstX,hbaseX]; exact hevolution.1
  have hy_evolution : spatialComponentY (path.first t)=(path.first t).Λy-
      C.pCoeff.operator ν (spatialComponentY (path.base t))+
      C.rCoeff.operator ν (path.base t).Λy := by rw [hfirstY,hbaseY]; exact hevolution.2
  have hfield := field_gradient_control ν C (path.base t) (path.first t) hx_evolution hy_evolution
  simpa only [hfirstX,hfirstY] using hfield

/-- (9.2)–(9.3) 全零吸收实例：不是把 J、空间耗散删除，而是保留 h²。
该调用只核验点态分支；一般场与同源路径定理已在上方独立证明。 -/
theorem directional_J_zero_example (h : ℝ) :
    directionalJ 0 0 h h=h^2 ∧ 3*directionalJ 0 0 h h ≤ spatialDissipation 4 0 0 h h := by
  have hbound := directional_dissipation_ge_J 4 0 0 1 h h (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun _ => rfl)
  constructor
  · norm_num [directionalJ,thetaX,thetaY,absorptionSum]
    ring
  · norm_num at hbound ⊢
    exact hbound

/-- (9.2)、(9.5) 的不对称边层核验：p=1,r=0 时 x 的 J 是 Λx²，
y 的 J 是 hy²。交换方向会改变被控制的槽；本例调用一般点态梯度定理。 -/
theorem directional_J_edge_examples (h l h₁ l₁ : ℝ)
    (hx : h₁=l₁+l) :
    directionalJ 1 0 h l=l^2 ∧ directionalJ 0 1 h l=h^2 ∧
    h₁^2 ≤ 3*directionalJ 1 0 h₁ l₁+3*directionalJ 1 0 h l := by
  have hbound := directional_gradient_control 1 0 1 h l h₁ l₁
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simpa using hx)
  refine ⟨?_,?_,?_⟩
  · norm_num [directionalJ,thetaX,thetaY,absorptionSum]
  · norm_num [directionalJ,thetaX,thetaY,absorptionSum]
  · simpa using hbound

/-- 与上一条配对的 y 边层调用：p=0,r=1，演化是 h₁=l₁−h₀。
这里单独调用一般估计，防止只检查 θ 数值而漏掉辅助演化中的方向次序。 -/
theorem directional_J_other_edge_example (h₀ l₀ h₁ l₁ : ℝ)
    (hy : h₁=l₁-h₀) :
    h₁^2 ≤ 3*directionalJ 0 1 h₁ l₁+3*directionalJ 0 1 h₀ l₀ := by
  have hbound := directional_gradient_control 0 1 1 h₀ l₀ h₁ l₁
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simpa using hy)
  simpa using hbound

/-- 双向吸收实例：p=1,r=2,S=2，两个 θ 为 1/3、2/3，避免只测对称角层。
本例调用一般系数与点态估计；并不声称构造二维 PDE 解。 -/
theorem directional_J_corner_example (h₀ l₀ h₁ l₁ : ℝ)
    (hevolution : h₁=l₁-2*h₀+l₀) :
    thetaX 1 2=1/3 ∧ thetaY 1 2=2/3 ∧
    h₁^2 ≤ 3*directionalJ 1 2 h₁ l₁+12*directionalJ 1 2 h₀ l₀ := by
  have hbound := directional_gradient_control 1 2 2 h₀ l₀ h₁ l₁
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simpa using hevolution)
  refine ⟨?_,?_,?_⟩
  · norm_num [thetaX,absorptionSum]
  · norm_num [thetaY,absorptionSum]
  · norm_num at hbound ⊢
    exact hbound

end LeanPML.PML
