import LeanPML.Analysis.EnergyCalculus
import LeanPML.PML.LocalSpatial
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# 空间系数：从原始幅度条件到实际 L² 乘子

V7 (5.3)、(5.5)–(5.6)、(7.2)。p、r 是可测空间函数，c、S 是时间常数。
SpatialAbsorption 只存原始非负、幅度假设；权重下界与耗散系数界调用 v0.2.1。
一般测度空间上的结论允许更一般 p、r；末尾 separated 构造保留物理模型 p(x)、r(y)。

BoundedCoefficient 记录“一个有界可测函数及已证明的界”，便于组合 (6.2) 中
a、b 的多项式系数；它不把论文待证界作为原始物理输入。
w 本身可能无界，所以不构造成 BoundedCoefficient，不用 boundedMul 乘 w。

建议先读 SpatialAbsorption → wx_gap/wy_gap → plusX/minusX。
真正的梯度、PEC 以及图范数估计不在本文件实现。
-/

noncomputable section
open MeasureTheory

namespace LeanPML.Analysis

/-- 构造 L² 有界乘子的分析数据，服务于 V7 (6.2)、(7.7) 的系数多项式。
value 是实际函数，measurable 是可测证据，bound/abs_le 是已证明的幅度控制。
这与物理模型原始参数结构不同：下方会从 p、r 的原假设构造它。 -/
structure BoundedCoefficient (α : Type*) [MeasurableSpace α] where
  value : α → ℝ
  measurable : Measurable value
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  abs_le : ∀ x, |value x| ≤ bound

namespace BoundedCoefficient
variable {α : Type*} [MeasurableSpace α]

/-- 常数系数：例如 (6.2) 中 c、τ、1。其幅度界取绝对值。 -/
def const (k : ℝ) : BoundedCoefficient α where
  value := fun _ => k
  measurable := measurable_const
  bound := |k|
  bound_nonneg := abs_nonneg k
  abs_le := fun _ => le_rfl

/-- 有界可测系数相加，界用三角不等式相加；用于构造 a 及能量多项式。 -/
def add (f g : BoundedCoefficient α) : BoundedCoefficient α where
  value := fun x => f.value x + g.value x
  measurable := f.measurable.add g.measurable
  bound := f.bound + g.bound
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  abs_le x := (abs_add_le _ _).trans (add_le_add (f.abs_le x) (g.abs_le x))

/-- 有界可测系数相减；保留 (7.7) 中可能符号不定的 a−c，不预设非负。 -/
def sub (f g : BoundedCoefficient α) : BoundedCoefficient α where
  value := fun x => f.value x - g.value x
  measurable := f.measurable.sub g.measurable
  bound := f.bound + g.bound
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  abs_le x := (abs_sub _ _).trans (add_le_add (f.abs_le x) (g.abs_le x))

/-- 有界可测系数相乘；界相乘只用两个已证明的非负幅度界。 -/
def mul (f g : BoundedCoefficient α) : BoundedCoefficient α where
  value := fun x => f.value x * g.value x
  measurable := f.measurable.mul g.measurable
  bound := f.bound * g.bound
  bound_nonneg := mul_nonneg f.bound_nonneg g.bound_nonneg
  abs_le x := by
    rw [abs_mul]
    exact mul_le_mul (f.abs_le x) (g.abs_le x) (abs_nonneg _) f.bound_nonneg

@[simp] theorem const_value (k : ℝ) (x : α) : (const k).value x = k := rfl
@[simp] theorem add_value (f g : BoundedCoefficient α) (x : α) :
    (f.add g).value x = f.value x + g.value x := rfl
@[simp] theorem sub_value (f g : BoundedCoefficient α) (x : α) :
    (f.sub g).value x = f.value x - g.value x := rfl
@[simp] theorem mul_value (f g : BoundedCoefficient α) (x : α) :
    (f.mul g).value x = f.value x * g.value x := rfl

/-- 将本系数变成实际 L² 连续乘子；连续性使用 EnergyCalculus 中已经证明的界。 -/
def operator (k : BoundedCoefficient α) (ν : Measure α) :
    ScalarL2 ν →L[ℝ] ScalarL2 ν :=
  boundedMul ν k.value k.measurable k.bound k.abs_le

/-- (6.2) 中的变系数交叉密度可积，供能量积分合法性使用。 -/
theorem integrable_product (k : BoundedCoefficient α) (ν : Measure α)
    (f g : ScalarL2 ν) : Integrable (fun x => k.value x * f x * g x) ν :=
  integrable_boundedMul_product ν k.value k.measurable k.bound k.abs_le f g

/-- (6.2) 的系数积分等于乘子内积；不使用代表元的逐点相等。 -/
theorem inner_operator (k : BoundedCoefficient α) (ν : Measure α)
    (f g : ScalarL2 ν) :
    inner ℝ (k.operator ν f) g = ∫ x, k.value x * f x * g x ∂ν :=
  inner_boundedMul_eq_integral ν k.value k.measurable k.bound k.abs_le f g

end BoundedCoefficient
end LeanPML.Analysis

namespace LeanPML.PML
open LeanPML.Analysis

/-- V7 (5.3) 的实际空间吸收场。所有条件都是原始假设：
p/r 可测、非负、不超过 S，S≤c/4，c>0；不要求吸收正下界或权重有界。
参数没有时间变量，因此本结构表达固定于时间的空间系数。 -/
structure SpatialAbsorption (α : Type*) [MeasurableSpace α] where
  c : ℝ
  S : ℝ
  c_pos : 0 < c
  p : α → ℝ
  r : α → ℝ
  p_measurable : Measurable p
  r_measurable : Measurable r
  p_nonneg : ∀ x, 0 ≤ p x
  r_nonneg : ∀ x, 0 ≤ r x
  p_le_S : ∀ x, p x ≤ S
  r_le_S : ∀ x, r x ≤ S
  S_le_quarter : S ≤ c / 4

namespace SpatialAbsorption
variable {α : Type*} [MeasurableSpace α]

/-- 实际吸收和 a(x)=p(x)+r(x)，复用既有点态定义。 -/
def a (C : SpatialAbsorption α) (x : α) := absorptionSum (C.p x) (C.r x)
/-- 实际吸收积 b(x)=p(x)r(x)。 -/
def b (C : SpatialAbsorption α) (x : α) := absorptionProduct (C.p x) (C.r x)
/-- V7 (5.5) 的实际 x 权重函数，零区取 0。 -/
def wx (C : SpatialAbsorption α) (x : α) := energyWeightX C.c (C.p x) (C.r x)
/-- V7 (5.5) 的实际 y 权重函数，零区取 0。 -/
def wy (C : SpatialAbsorption α) (x : α) := energyWeightY C.c (C.p x) (C.r x)

theorem a_measurable (C : SpatialAbsorption α) : Measurable C.a :=
  C.p_measurable.add C.r_measurable
theorem b_measurable (C : SpatialAbsorption α) : Measurable C.b :=
  C.p_measurable.mul C.r_measurable

/-- V7 (5.5) 权重可测：正吸收区是可测集，两分支是可测函数。
分母可以趋于零，可测性不需要正下界或本质有界。 -/
theorem wx_measurable (C : SpatialAbsorption α) : Measurable C.wx := by
  exact Measurable.ite (measurableSet_lt measurable_const C.a_measurable)
    ((measurable_const.sub C.r_measurable).div C.a_measurable) measurable_const

/-- 同一可测性论证用于 y 权重，分子改为 c−p。 -/
theorem wy_measurable (C : SpatialAbsorption α) : Measurable C.wy := by
  exact Measurable.ite (measurableSet_lt measurable_const C.a_measurable)
    ((measurable_const.sub C.p_measurable).div C.a_measurable) measurable_const

/-- 由 (5.5) 的旧权重界推出 w_x=0 或 w_x≥1；原下界实际为 3/2。
这是加权空间零延拓嵌入普通 L² 所需的间隙，不是新增的物理假设。 -/
theorem wx_gap (C : SpatialAbsorption α) (x : α) : C.wx x = 0 ∨ 1 ≤ C.wx x := by
  by_cases ha_pos : 0 < C.a x
  · right
    have hlower := (energyWeights_lower_bound C.c (C.p x) (C.r x) C.S
      ha_pos (C.p_le_S x) (C.r_le_S x) C.S_le_quarter).1
    change 1 ≤ energyWeightX C.c (C.p x) (C.r x)
    linarith
  · left
    exact if_neg ha_pos

/-- y 权重同样由原始幅度假设获得 0 或 ≥1 的间隙。 -/
theorem wy_gap (C : SpatialAbsorption α) (x : α) : C.wy x = 0 ∨ 1 ≤ C.wy x := by
  by_cases ha_pos : 0 < C.a x
  · right
    have hlower := (energyWeights_lower_bound C.c (C.p x) (C.r x) C.S
      ha_pos (C.p_le_S x) (C.r_le_S x) C.S_le_quarter).2
    change 1 ≤ energyWeightY C.c (C.p x) (C.r x)
    linarith
  · left
    exact if_neg ha_pos

/-- 零权重恰是零吸收区；用于明确论文 ψ=0 a.e. on Z 的对应。 -/
theorem wx_eq_zero_iff (C : SpatialAbsorption α) (x : α) : C.wx x = 0 ↔ C.a x = 0 := by
  have ha_nonneg := absorptionSum_nonneg (C.p x) (C.r x) (C.p_nonneg x) (C.r_nonneg x)
  constructor
  · intro hw_zero
    by_contra ha_ne
    have ha_pos : 0 < C.a x := lt_of_le_of_ne ha_nonneg (Ne.symm ha_ne)
    have hlower := (energyWeights_lower_bound C.c (C.p x) (C.r x) C.S
      ha_pos (C.p_le_S x) (C.r_le_S x) C.S_le_quarter).1
    change (3/2 : ℝ) ≤ C.wx x at hlower
    rw [hw_zero] at hlower
    norm_num at hlower
  · intro ha_zero
    exact (weights_of_sum_zero C.c (C.p x) (C.r x) ha_zero).1

theorem wy_eq_zero_iff (C : SpatialAbsorption α) (x : α) : C.wy x = 0 ↔ C.a x = 0 := by
  have ha_nonneg := absorptionSum_nonneg (C.p x) (C.r x) (C.p_nonneg x) (C.r_nonneg x)
  constructor
  · intro hw_zero
    by_contra ha_ne
    have ha_pos : 0 < C.a x := lt_of_le_of_ne ha_nonneg (Ne.symm ha_ne)
    have hlower := (energyWeights_lower_bound C.c (C.p x) (C.r x) C.S
      ha_pos (C.p_le_S x) (C.r_le_S x) C.S_le_quarter).2
    change (3/2 : ℝ) ≤ C.wy x at hlower
    rw [hw_zero] at hlower
    norm_num at hlower
  · intro ha_zero
    exact (weights_of_sum_zero C.c (C.p x) (C.r x) ha_zero).2.1

/-- p 的实际有界系数，由原始幅度假设构造；|S| 也覆盖空空间情形。 -/
def pCoeff (C : SpatialAbsorption α) : BoundedCoefficient α where
  value := C.p
  measurable := C.p_measurable
  bound := |C.S|
  bound_nonneg := abs_nonneg _
  abs_le x := by rw [abs_of_nonneg (C.p_nonneg x)]; exact (C.p_le_S x).trans (le_abs_self _)

/-- r 的实际有界系数，与 p 同理。 -/
def rCoeff (C : SpatialAbsorption α) : BoundedCoefficient α where
  value := C.r
  measurable := C.r_measurable
  bound := |C.S|
  bound_nonneg := abs_nonneg _
  abs_le x := by rw [abs_of_nonneg (C.r_nonneg x)]; exact (C.r_le_S x).trans (le_abs_self _)

/-- a=p+r 的有界性由系数相加导出。 -/
def aCoeff (C : SpatialAbsorption α) : BoundedCoefficient α := C.pCoeff.add C.rCoeff
/-- b=pr 的有界性由系数相乘导出。 -/
def bCoeff (C : SpatialAbsorption α) : BoundedCoefficient α := C.pCoeff.mul C.rCoeff

@[simp] theorem pCoeff_value (C : SpatialAbsorption α) (x : α) : C.pCoeff.value x = C.p x := rfl
@[simp] theorem rCoeff_value (C : SpatialAbsorption α) (x : α) : C.rCoeff.value x = C.r x := rfl
@[simp] theorem aCoeff_value (C : SpatialAbsorption α) (x : α) : C.aCoeff.value x = C.a x := rfl
@[simp] theorem bCoeff_value (C : SpatialAbsorption α) (x : α) : C.bCoeff.value x = C.b x := rfl

/-- 交换方向只交换 p、r；c、S 和原始幅度条件保持不变。 -/
def swap (C : SpatialAbsorption α) : SpatialAbsorption α where
  c := C.c
  S := C.S
  c_pos := C.c_pos
  p := C.r
  r := C.p
  p_measurable := C.r_measurable
  r_measurable := C.p_measurable
  p_nonneg := C.r_nonneg
  r_nonneg := C.p_nonneg
  p_le_S := C.r_le_S
  r_le_S := C.p_le_S
  S_le_quarter := C.S_le_quarter

private def plusValue (C : SpatialAbsorption α) (x : α) : ℝ :=
  if 0 < C.a x then dissipationPlus C.c (C.p x) (C.r x) else 0
private def minusValue (C : SpatialAbsorption α) (x : α) : ℝ :=
  if 0 < C.a x then dissipationMinus C.c (C.r x) (C.p x) else C.c

/-- (7.2) 中 l_x² 的系数在正区为 p(c+p)/a，零区取 0；非负和界来自 v0.2.1。 -/
theorem plusValue_bounds (C : SpatialAbsorption α) (x : α) :
    0 ≤ plusValue C x ∧ plusValue C x ≤ C.c + |C.S| := by
  by_cases ha_pos : 0 < C.a x
  · rw [plusValue, if_pos ha_pos]
    have hb := dissipationPlus_bounds C.c (C.p x) (C.r x) C.S C.c_pos.le
      (C.p_nonneg x) (C.r_nonneg x) ha_pos (C.p_le_S x)
    exact ⟨hb.1, hb.2.trans (add_le_add le_rfl (le_abs_self C.S))⟩
  · rw [plusValue, if_neg ha_pos]
    exact ⟨le_rfl, add_nonneg C.c_pos.le (abs_nonneg _)⟩

/-- (7.2) 中 h_x² 的系数在正区为 r(c−r)/a，零区必须保留 c。
非负、有界不要求 r、a 的正下界。 -/
theorem minusValue_bounds (C : SpatialAbsorption α) (x : α) :
    0 ≤ minusValue C x ∧ minusValue C x ≤ C.c := by
  by_cases ha_pos : 0 < C.a x
  · rw [minusValue, if_pos ha_pos]
    have hr_le_c : C.r x ≤ C.c := by
      have hr_le := (C.r_le_S x).trans C.S_le_quarter
      linarith [C.c_pos]
    have ha_swap : 0 < absorptionSum (C.r x) (C.p x) := by
      simpa [a, absorptionSum, add_comm] using ha_pos
    exact dissipationMinus_bounds C.c (C.r x) (C.p x)
      (C.r_nonneg x) (C.p_nonneg x) hr_le_c ha_swap
  · rw [minusValue, if_neg ha_pos]
    exact ⟨C.c_pos.le, le_rfl⟩

/-- 实际 x 方向正耗散系数；可测、幅度界均已从吸收场证明。 -/
def plusX (C : SpatialAbsorption α) : BoundedCoefficient α where
  value := plusValue C
  measurable := by
    apply Measurable.ite (measurableSet_lt measurable_const C.a_measurable)
    · exact (C.p_measurable.mul (measurable_const.add C.p_measurable)).div C.a_measurable
    · exact measurable_const
  bound := C.c + |C.S|
  bound_nonneg := add_nonneg C.c_pos.le (abs_nonneg _)
  abs_le x := by rw [abs_of_nonneg (C.plusValue_bounds x).1]; exact (C.plusValue_bounds x).2

/-- 实际 x 方向梯度耗散系数，零区值为 c，不能被分式零延拓删掉。 -/
def minusX (C : SpatialAbsorption α) : BoundedCoefficient α where
  value := minusValue C
  measurable := by
    apply Measurable.ite (measurableSet_lt measurable_const C.a_measurable)
    · simpa only [dissipationMinus, a, absorptionSum, add_comm] using
        (C.r_measurable.mul
          ((measurable_const : Measurable (fun _ : α => C.c)).sub C.r_measurable)).div C.a_measurable
    · exact measurable_const
  bound := C.c
  bound_nonneg := C.c_pos.le
  abs_le x := by rw [abs_of_nonneg (C.minusValue_bounds x).1]; exact (C.minusValue_bounds x).2

/-- y 方向 l_y² 的系数交换 p、r，正区为 r(c+r)/a。 -/
def plusY (C : SpatialAbsorption α) : BoundedCoefficient α := C.swap.plusX
/-- y 方向 h_y² 的系数交换 p、r，正区为 p(c−p)/a，零区仍为 c。 -/
def minusY (C : SpatialAbsorption α) : BoundedCoefficient α := C.swap.minusX

theorem plusX_nonneg (C : SpatialAbsorption α) (x : α) : 0 ≤ C.plusX.value x :=
  (C.plusValue_bounds x).1
theorem plusY_nonneg (C : SpatialAbsorption α) (x : α) : 0 ≤ C.plusY.value x :=
  (C.swap.plusValue_bounds x).1
theorem minusX_nonneg (C : SpatialAbsorption α) (x : α) : 0 ≤ C.minusX.value x :=
  (C.minusValue_bounds x).1
theorem minusY_nonneg (C : SpatialAbsorption α) (x : α) : 0 ≤ C.minusY.value x :=
  (C.swap.minusValue_bounds x).1

/-- 将四个实际有界系数接回 v0.2.3 的 (7.2) 点态分支耗散。
h/l 此处仍是实数分量；实际空间梯度尚待后续接口。两个零区各贡献 c h_i²。 -/
theorem spatialDissipation_eq (C : SpatialAbsorption α) (x : α) (hx hy lx ly : ℝ) :
    spatialDissipation2D C.c (C.p x) (C.r x) hx hy lx ly =
      C.plusX.value x * lx^2 + C.minusX.value x * hx^2 +
      C.plusY.value x * ly^2 + C.minusY.value x * hy^2 := by
  by_cases ha_pos : 0 < absorptionSum (C.p x) (C.r x)
  · have ha_swap : 0 < absorptionSum (C.r x) (C.p x) := by
      simpa only [absorptionSum, add_comm] using ha_pos
    simp only [spatialDissipation2D, spatialDissipation, plusX, minusX, plusY, minusY,
      plusValue, minusValue, swap, a, if_pos ha_pos, if_pos ha_swap]
    ring
  · have ha_swap : ¬0 < absorptionSum (C.r x) (C.p x) := by
      simpa only [absorptionSum, add_comm] using ha_pos
    simp only [spatialDissipation2D, spatialDissipation, plusX, minusX, plusY, minusY,
      plusValue, minusValue, swap, a, if_neg ha_pos, if_neg ha_swap, zero_mul]
    ring

/-- 物理模型的分离吸收入口：在整个二维空间令 p(x,y)=p₁(x)、r(x,y)=r₁(y)。
一般 SpatialAbsorption 定理的推广没有改变这一最终模型要求。 -/
def separated (c S : ℝ) (hc_pos : 0 < c) (p₁ r₁ : ℝ → ℝ)
    (hp_meas : Measurable p₁) (hr_meas : Measurable r₁)
    (hp_nonneg : ∀ x, 0 ≤ p₁ x) (hr_nonneg : ∀ y, 0 ≤ r₁ y)
    (hp_le : ∀ x, p₁ x ≤ S) (hr_le : ∀ y, r₁ y ≤ S)
    (hS_le : S ≤ c/4) : SpatialAbsorption (ℝ × ℝ) where
  c := c
  S := S
  c_pos := hc_pos
  p := fun x => p₁ x.1
  r := fun x => r₁ x.2
  p_measurable := hp_meas.comp measurable_fst
  r_measurable := hr_meas.comp measurable_snd
  p_nonneg := fun x => hp_nonneg x.1
  r_nonneg := fun x => hr_nonneg x.2
  p_le_S := fun x => hp_le x.1
  r_le_S := fun x => hr_le x.2
  S_le_quarter := hS_le

/-- 从仅 a.e. 满足幅度条件的可测系数选择全点有界代表。
由 V7 (5.3) 的本质上界条件推出，原文未单列：截断到 [0,S] 只修改零测集。
S≥0 是幅度上界的自然条件；后续积分可用此代表，未加强物理模型的 a.e. 假设。 -/
def ofAE (_ν : Measure α) (c S : ℝ) (hc_pos : 0 < c) (hS_nonneg : 0 ≤ S)
    (p r : α → ℝ) (hp_meas : Measurable p) (hr_meas : Measurable r)
    (hS_le : S ≤ c / 4) : SpatialAbsorption α where
  c := c
  S := S
  c_pos := hc_pos
  p := fun x => max 0 (min S (p x))
  r := fun x => max 0 (min S (r x))
  p_measurable := measurable_const.max (measurable_const.min hp_meas)
  r_measurable := measurable_const.max (measurable_const.min hr_meas)
  p_nonneg := fun _ => le_max_left _ _
  r_nonneg := fun _ => le_max_left _ _
  p_le_S := fun _ => max_le hS_nonneg (min_le_left _ _)
  r_le_S := fun _ => max_le hS_nonneg (min_le_left _ _)
  S_le_quarter := hS_le

/-- 上述代表与原 p 几乎处处一致；本定理才使用原 p 的 a.e. 幅度假设。
代表构造本身只是截断，而此等式确保它没有改变 L²/积分模型。 -/
theorem ofAE_p_ae (ν : Measure α) (c S : ℝ) (hc_pos : 0 < c)
    (hS_nonneg : 0 ≤ S) (p r : α → ℝ)
    (hp_meas : Measurable p) (hr_meas : Measurable r) (hS_le : S ≤ c / 4)
    (hp_bounds : ∀ᵐ x ∂ν, 0 ≤ p x ∧ p x ≤ S) :
    (ofAE ν c S hc_pos hS_nonneg p r hp_meas hr_meas hS_le).p =ᵐ[ν] p := by
  filter_upwards [hp_bounds] with x hx
  simp only [ofAE, min_eq_right hx.2, max_eq_right hx.1]

/-- r 分量同样只在零测集被修改。 -/
theorem ofAE_r_ae (ν : Measure α) (c S : ℝ) (hc_pos : 0 < c)
    (hS_nonneg : 0 ≤ S) (p r : α → ℝ)
    (hp_meas : Measurable p) (hr_meas : Measurable r) (hS_le : S ≤ c / 4)
    (hr_bounds : ∀ᵐ x ∂ν, 0 ≤ r x ∧ r x ≤ S) :
    (ofAE ν c S hc_pos hS_nonneg p r hp_meas hr_meas hS_le).r =ᵐ[ν] r := by
  filter_upwards [hr_bounds] with x hx
  simp only [ofAE, min_eq_right hx.2, max_eq_right hx.1]


end SpatialAbsorption

/-- V7 整个计算矩形 Ω=(x₀,x₁)×(y₀,y₁)，不缩小为物理区。 -/
def rectangleDomain (x₀ x₁ y₀ y₁ : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo x₀ x₁ ×ˢ Set.Ioo y₀ y₁

/-- 限制到整个 Ω 的二维 Lebesgue 测度；空间积分中的 ν 可取此测度。 -/
def rectangleMeasure (x₀ x₁ y₀ y₁ : ℝ) : Measure (ℝ × ℝ) :=
  volume.restrict (rectangleDomain x₀ x₁ y₀ y₁)

end LeanPML.PML
