import LeanPML.PML.MainRepresentedWeak

/-!
# 原八式与加权初值的 a.e. 系数换代表

V7 §1/§2：系数代表可以修改于零测集，弱方程和初始兼容不变。
本模块以实际乘子相等搬运原方程，不输入重新求解后的 OriginalAt。
加权平方根坐标保持原 L² 元素，物理恢复值经 a.e. 公式验证。
-/
noncomputable section
open MeasureTheory Set Filter
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML

/-- a.e. 相同的有界系数给出相同连续乘子。 -/
theorem BoundedCoefficient.operator_eq_ae {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (a b : BoundedCoefficient α) (heq : a.value =ᵐ[ν] b.value) :
    a.operator ν = b.operator ν := by
  ext X
  filter_upwards [a.coe_operator ν X,b.coe_operator ν X,heq] with z ha hb hz
  rw [ha,hb,hz]

/-- 原八式仅使用 p、r、p+r、pr 的有界乘子；四者均由两个系数的 a.e. 识别确定。 -/
theorem spatial_operators_eq_ae {D : Rect} (C B : SpatialAbsorption (ℝ × ℝ))
    (hp : C.p =ᵐ[D.measure] B.p) (hr : C.r =ᵐ[D.measure] B.r) :
    C.pCoeff.operator D.measure = B.pCoeff.operator D.measure ∧
    C.rCoeff.operator D.measure = B.rCoeff.operator D.measure ∧
    C.aCoeff.operator D.measure = B.aCoeff.operator D.measure ∧
    C.bCoeff.operator D.measure = B.bCoeff.operator D.measure := by
  refine ⟨BoundedCoefficient.operator_eq_ae _ _ _ hp,
    BoundedCoefficient.operator_eq_ae _ _ _ hr,?_,?_⟩
  · apply BoundedCoefficient.operator_eq_ae
    filter_upwards [hp,hr] with z hzp hzr
    change C.p z + C.r z = B.p z + B.r z
    rw [hzp,hzr]
  · apply BoundedCoefficient.operator_eq_ae
    filter_upwards [hp,hr] with z hzp hzr
    change C.p z*C.r z = B.p z*B.r z
    rw [hzp,hzr]

namespace Weak
/-- 对同一原场及真实时间导数，系数 a.e. 替换保留全部八条方程。 -/
theorem OriginalAt.changeCoefficients {D : Rect} {C B : SpatialAbsorption (ℝ × ℝ)}
    {ε κ τ μ t : ℝ} {F : ℝ → OriginalState D} {dF : OriginalState D}
    {e : zeroBoundaryGraph D} {L : weakHDivGraph D}
    (h : OriginalAt D C ε κ τ μ F dF t e L)
    (hp : C.p =ᵐ[D.measure] B.p) (hr : C.r =ᵐ[D.measure] B.r) :
    OriginalAt D B ε κ τ μ F dF t e L := by
  obtain ⟨hp',hr',ha',hb'⟩ := spatial_operators_eq_ae C B hp hr
  exact { h with
    electric := by simpa only [← ha'] using h.electric
    magneticX := by simpa only [← hp',← hr'] using h.magneticX
    magneticY := by simpa only [← hp',← hr'] using h.magneticY
    memory1 := by simpa only [← hb'] using h.memory1
    memory2 := by simpa only [← hb'] using h.memory2
    auxiliaryX := by simpa only [← hp',← hr'] using h.auxiliaryX
    auxiliaryY := by simpa only [← hp',← hr'] using h.auxiliaryY }

/-- 原场、导数槽、图空间路径和初值完全不动，只搬运已证明的原八式和初始兼容。
因此新入口可以直接接收原系数下的解，不重新假设其满足另一套方程。 -/
def OriginalInterval.changeCoefficients {D : Rect} {C B : SpatialAbsorption (ℝ × ℝ)}
    {ε κ τ μ T : ℝ} (O : OriginalInterval D C ε κ τ μ T)
    (hp : C.p =ᵐ[D.measure] B.p) (hr : C.r =ᵐ[D.measure] B.r) :
    OriginalInterval D B ε κ τ μ T :=
  { O with
    equations := fun t ht => (O.equations t ht).changeCoefficients hp hr
    initial_compatible := by
      obtain ⟨hp',hr',_,hb'⟩ := spatial_operators_eq_ae C B hp hr
      intro i
      simpa only [invariants,← hp',← hr',← hb'] using O.initial_compatible i }

end Weak

/-- 加权空间换代表的实际线性等距映射；底层平方根 L² 坐标不变。 -/
def weightedChangeRepresentative {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (w v : α → ℝ) (heq : w =ᵐ[ν] v) : WeightedL2 ν w ≃ₗᵢ[ℝ] WeightedL2 ν v where
  toFun X := ⟨X.val,by
    filter_upwards [X.property,heq] with z hz hw
    exact fun hv => hz (hw.trans hv)⟩
  invFun X := ⟨X.val,by
    filter_upwards [X.property,heq] with z hz hw
    exact fun hv => hz (hw.symm.trans hv)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- 同一加权平方根坐标在 a.e. 相同权重下恢复同一物理 L² 场。
不用逐点选择代表；零区值和无界正区均包含在此 a.e. 证明中。 -/
theorem physical_changeRepresentative {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (w v : α → ℝ) (heq : w =ᵐ[ν] v) (hw : Measurable w) (hv : Measurable v)
    (hgw : ∀ z, w z = 0 ∨ 1 ≤ w z) (hgv : ∀ z, v z = 0 ∨ 1 ≤ v z)
    (X : WeightedL2 ν w) :
    physicalL2 ν v hv hgv (weightedChangeRepresentative ν w v heq X) =
      physicalL2 ν w hw hgw X := by
  apply Lp.ext
  filter_upwards [physicalL2_coe ν v hv hgv (weightedChangeRepresentative ν w v heq X),
    physicalL2_coe ν w hw hgw X,heq] with z hvz hwz hz
  rw [hvz,hwz,hz]
  rfl

end LeanPML.PML
