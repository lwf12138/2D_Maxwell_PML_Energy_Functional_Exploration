import LeanPML.PML.MainSharpWeakRectangle
import LeanPML.PML.WeakCanonicalEnergy

/-!
# (6.6) 的正长度区间入口：端点导数由区间 Cᵏ 正则性选定

OriginalInterval 只在内部约束导数槽。这里保留全部原场和 PDE，
把 E/P 的导数槽选为真实 derivWithin，证明内部选择与原证据相同。
于是无需调用者对端点的任意旧槽另给识别条件。T=0 没有唯一的区间导数，
继续使用旧入口的独立初始导数层兼容；不从空开区间推导它。
-/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.Weak

/-- (6.6) 实际使用的 Cᵏ 部分，字段只含真实空间值 ContDiffOn。
φ 的加权成员/所需求导复用原演化的历史结果；未把 OriginalJet 当成字段。
这是充分性入口，不声称任意时间正则性表示之间双向等价。 -/
structure V7ClosedCkCore {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (O : OriginalInterval D C ε κ τ μ T) : Prop where
  u_graph : ContDiffOn ℝ 2 O.u (Icc 0 T)
  u_value : ContDiffOn ℝ 3 (fun t => (O.u t).val.val 0) (Icc 0 T)
  polar : ContDiffOn ℝ 2 (fun t => (O.fields t).P) (Icc 0 T)
  flux : ContDiffOn ℝ 1 O.flux (Icc 0 T)

namespace V7ClosedCkCore
variable {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
variable {O : OriginalInterval D C ε κ τ μ T} (R : V7ClosedCkCore O) (hT : 0 < T)

include hT

/-- 内部八式给出的 E/P 导数与区间导数一致；不要求端点 PDE。 -/
theorem interior_derivative_slots {t : ℝ} (ht : t ∈ Ioo 0 T) :
    derivWithin (fun s => (O.fields s).E) (Icc 0 T) t = (O.derivatives t).E ∧
    derivWithin (fun s => (O.fields s).P) (Icc 0 T) t = (O.derivatives t).P := by
  have hunique := uniqueDiffOn_Icc hT t (Ioo_subset_Icc_self ht)
  exact ⟨(O.equations t ht).E.hasDerivWithinAt.derivWithin hunique,
    (O.equations t ht).P.hasDerivWithinAt.derivWithin hunique⟩

/-- 只规范化 E/P 的导数槽，原八变量、PEC、初值与历史完全不变。
内部原方程通过已证导数唯一性保留，端点不添加 PDE。 -/
def canonicalInterval : OriginalInterval D C ε κ τ μ T :=
  { O with
    derivatives := fun t => { O.derivatives t with
      E := derivWithin (fun s => (O.fields s).E) (Icc 0 T) t
      P := derivWithin (fun s => (O.fields s).P) (Icc 0 T) t }
    equations := by
      intro t ht
      have hslots := interior_derivative_slots hT ht (O := O)
      simpa only [hslots.1,hslots.2] using O.equations t ht }

/-- 规范化后的场与输入原场逐时刻相同，结论仍控制实际输入 E/H/P/Z/Q。 -/
theorem canonical_fields : (canonicalInterval (O := O) hT).fields = O.fields := rfl

/-- 从真正 Cᵏ 字段填入先前桥接；端点识别现在由构造定义给出，不是新假设。 -/
def regularity : ClosedCkRegularity (canonicalInterval (O := O) hT) where
  u_graph := R.u_graph
  u_value := R.u_value
  polar := R.polar
  flux := R.flux
  electric_endpoint _ _ := rfl
  polar_endpoint _ _ := rfl

/-- (6.6) 的 Cᵏ 充分性、原方程和初始加权成员给出精确 CP 的主结论。
正长度区间无额外端点导数槽识别输入。本底层入口不负责构造系数连续代表；
WeakAbsorptionRepresentative.lean 已从区域弱导数证明代表存在，
最终入口 OriginalInterval.main_energy_GeneralWeakCk 在证明中构造并接入该代表。 -/
theorem main_energy
    (W₀x : WeightedL2 D.measure C.wx) (W₀y : WeightedL2 D.measure C.swap.wx)
    (hp : CoercivityParameters C ε κ τ μ (sharpPoincareConstant D))
    (hWx : physicalL2 D.measure C.wx C.wx_measurable C.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure C.swap.wx C.swap.wx_measurable C.swap.wx_gap W₀y = O.φy 0) :
    OriginalInterval.SharpEnergyConclusions (canonicalInterval (O := O) hT)
      ((R.regularity hT).toTimeRegularity hT).toOriginalJet W₀x W₀y ∧
    ∀ t ∈ Icc 0 T, OriginalInterval.SharpOriginalAuxiliaryBounds (canonicalInterval (O := O) hT)
      ((canonicalInterval (O := O) hT).sharpEnergy
        ((R.regularity hT).toTimeRegularity hT).toOriginalJet W₀x W₀y 0) t :=
  (R.regularity hT).main_energy_sharp hT W₀x W₀y hp hWx hWy
end V7ClosedCkCore

/-- 使用已选连续代表的区域系数入口：闭区间 Cᵏ、原八式、初始兼容及原 π 阈值。
连续代表明确包含在本入口的 A 中；一般区域弱系数应使用 MainGeneralWeak.lean
中的 OriginalInterval.main_energy_GeneralWeakCk，由已证代表构造接入本定理。 -/
theorem main_energy_RegionalSharpCk
    (D : Rect) (A : WeakRegionalAbsorption D) (ε κ τ μ T : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hμ : 0 < μ) (hT : 0 < T)
    (hsmall : A.c ≤ threshold ε κ τ μ (sharpPoincareConstant D))
    (O : OriginalInterval D A.spatial ε κ τ μ T) (R : V7ClosedCkCore O)
    (W₀x : WeightedL2 D.measure A.spatial.wx)
    (W₀y : WeightedL2 D.measure A.spatial.swap.wx)
    (hWx : physicalL2 D.measure A.spatial.wx A.spatial.wx_measurable A.spatial.wx_gap W₀x = O.φx 0)
    (hWy : physicalL2 D.measure A.spatial.swap.wx A.spatial.swap.wx_measurable A.spatial.swap.wx_gap W₀y = O.φy 0) :
    OriginalInterval.SharpEnergyConclusions (V7ClosedCkCore.canonicalInterval (O := O) hT)
      ((R.regularity hT).toTimeRegularity hT).toOriginalJet W₀x W₀y ∧
    ∀ t ∈ Icc 0 T, OriginalInterval.SharpOriginalAuxiliaryBounds
      (V7ClosedCkCore.canonicalInterval (O := O) hT)
      ((V7ClosedCkCore.canonicalInterval (O := O) hT).sharpEnergy
        ((R.regularity hT).toTimeRegularity hT).toOriginalJet W₀x W₀y 0) t := by
  exact R.main_energy hT W₀x W₀y
    ⟨hε,hκ,hτ,hμ,sharpPoincareConstant_pos D,hsmall⟩ hWx hWy
end LeanPML.PML.Weak
