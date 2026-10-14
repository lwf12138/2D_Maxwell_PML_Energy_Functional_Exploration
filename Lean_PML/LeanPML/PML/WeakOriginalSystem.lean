import LeanPML.Time.BanachHistory
import LeanPML.Rectangle.WeakPaths
import LeanPML.PML.WeightedMemoryBound

/-!
# V7 (2.1)–(2.4)：实际弱空间中的原八变量及历史提升

原场坐标都是整个矩形限制测度上的 L² 商类。电场的空间成员是 H₀¹ 图，
旋转磁通量 (μHy,−μHx) 的成员是 H(div) 图；梯度与散度来自真实弱导数。
时间导数逐个用 HasDerivAt 绑定，不使用总定义 fderiv 冒充弱可导性。
原系统定义只含八条原式、空间识别和真实时间导数；不含全时段兼容或能量结论。
系数暂复用可测有界的空间代表；区域分离 W¹,∞ 的更高入口另行连接。
-/
noncomputable section
-- H₀¹ 的双重图子类型含多个推断实例；提高 elaborator 配额，不改变内核检查。
set_option maxHeartbeats 800000
open MeasureTheory Set
open LeanPML.Analysis LeanPML.Rectangle LeanPML.Time
namespace LeanPML.PML.Weak

/-- (2.1) 的八个真实 L² 场值；下游时间路径是 ℝ→OriginalState D。 -/
structure OriginalState (D : Rect) where
  E : ScalarL2 D.measure
  Hx : ScalarL2 D.measure
  Hy : ScalarL2 D.measure
  P : ScalarL2 D.measure
  Z1 : ScalarL2 D.measure
  Z2 : ScalarL2 D.measure
  Qx : ScalarL2 D.measure
  Qy : ScalarL2 D.measure

/-- 原场的实际时间导数证据，dF 是与路径绑定的值而非任意代数槽。 -/
structure OriginalHasDerivAt {D : Rect} (F : ℝ → OriginalState D)
    (dF : OriginalState D) (t : ℝ) : Prop where
  E : HasDerivAt (fun s => (F s).E) dF.E t
  Hx : HasDerivAt (fun s => (F s).Hx) dF.Hx t
  Hy : HasDerivAt (fun s => (F s).Hy) dF.Hy t
  P : HasDerivAt (fun s => (F s).P) dF.P t
  Z1 : HasDerivAt (fun s => (F s).Z1) dF.Z1 t
  Z2 : HasDerivAt (fun s => (F s).Z2) dF.Z2 t
  Qx : HasDerivAt (fun s => (F s).Qx) dF.Qx t
  Qy : HasDerivAt (fun s => (F s).Qy) dF.Qy t

/-- 闭区间端点也需原场连续；它不含 PDE 或导数公式。 -/
structure OriginalContinuousOn {D : Rect} (F : ℝ → OriginalState D) (I : Set ℝ) : Prop where
  E : ContinuousOn (fun s => (F s).E) I
  Hx : ContinuousOn (fun s => (F s).Hx) I
  Hy : ContinuousOn (fun s => (F s).Hy) I
  P : ContinuousOn (fun s => (F s).P) I
  Z1 : ContinuousOn (fun s => (F s).Z1) I
  Z2 : ContinuousOn (fun s => (F s).Z2) I
  Qx : ContinuousOn (fun s => (F s).Qx) I
  Qy : ContinuousOn (fun s => (F s).Qy) I

/-- V7 (2.1) 的八条弱场原式。e 的成员表达整个矩形 PEC；L 是旋转磁通量。
电式乘以 μ 以使用 div(μHy,−μHx)；物理版本 μ>0 保证这与原式等价。
磁场不要求各分量 H¹、法向零或磁散度为零。这里只限制实际使用的 curl/H(div)。 -/
structure OriginalAt (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (ε κ τ μ : ℝ)
    (F : ℝ → OriginalState D) (dF : OriginalState D) (t : ℝ)
    (e : zeroBoundaryGraph D) (L : weakHDivGraph D) : Prop
    extends OriginalHasDerivAt F dF t where
  electric_value : e.val.val 0 = (F t).E
  flux_x : L.val 0 = μ • (F t).Hy
  flux_y : L.val 1 = -μ • (F t).Hx
  electric : μ • (ε • dF.E) = L.val 2 - μ •
    (ε • (C.aCoeff.operator D.measure (F t).E) + dF.P +
      C.aCoeff.operator D.measure (F t).P - (F t).Z1 - (F t).Z2)
  magneticX : μ • dF.Hx = -e.val.val 2 -
    μ • (C.rCoeff.operator D.measure (F t).Hx - C.pCoeff.operator D.measure (F t).Hx) + (F t).Qx
  magneticY : μ • dF.Hy = e.val.val 1 -
    μ • (C.pCoeff.operator D.measure (F t).Hy - C.rCoeff.operator D.measure (F t).Hy) + (F t).Qy
  debye : τ • dF.P + (F t).P = κ • (F t).E
  memory1 : dF.Z1 = -ε • C.bCoeff.operator D.measure (F t).E
  memory2 : dF.Z2 = -C.bCoeff.operator D.measure (F t).P
  auxiliaryX : dF.Qx = C.pCoeff.operator D.measure
    (-(F t).Qx + μ • (C.rCoeff.operator D.measure (F t).Hx - C.pCoeff.operator D.measure (F t).Hx))
  auxiliaryY : dF.Qy = C.rCoeff.operator D.measure
    (-(F t).Qy + μ • (C.pCoeff.operator D.measure (F t).Hy - C.rCoeff.operator D.measure (F t).Hy))

/-- H₀¹ 图的有界坐标，0 为函数，1/2 为弱偏导。历史积分可在图空间中构造。 -/
def zeroCoordinate (D : Rect) (i : Fin 3) : zeroBoundaryGraph D →L[ℝ] ScalarL2 D.measure :=
  (weakH1Coordinate D i).comp (zeroBoundaryGraph D).subtypeL

/-- 图范数真实导数经固定坐标投影成为 L² 导数。显式注明空间以避免子类型实例歧义。 -/
theorem zeroCoordinate_hasDerivAt (D : Rect) (i : Fin 3)
    {u : ℝ → zeroBoundaryGraph D} {du : zeroBoundaryGraph D} {t : ℝ}
    (hu : HasDerivAt u du t) : HasDerivAt (fun s => (u s).val.val i) (du.val.val i) t := by
  exact HasFDerivAt.comp_hasDerivAt (F := zeroBoundaryGraph D) (E := ScalarL2 D.measure) t
    (@ContinuousLinearMap.hasFDerivAt ℝ _ (zeroBoundaryGraph D) _ _ _
      (ScalarL2 D.measure) _ _ _ (zeroCoordinate D i) (u t)) hu

/-- (2.3)：电场 H₀¹ 路径的真实历史，初始原函数 u₀ 可任意合法零迹成员。 -/
def historyU (D : Rect) (e : ℝ → zeroBoundaryGraph D) (u₀ : zeroBoundaryGraph D) :=
  banachHistory e u₀

/-- (2.3)：极化路径的真实 L² 历史，不默认 q₀=0。 -/
def historyQ (D : Rect) (F : ℝ → OriginalState D) (q₀ : ScalarL2 D.measure) :=
  banachHistory (fun s => (F s).P) q₀

/-- H₀¹ 历史的函数/偏导坐标确为对应实际 Bochner 历史；原文未单列。 -/
theorem historyU_coordinate (D : Rect) (e : ℝ → zeroBoundaryGraph D)
    (u₀ : zeroBoundaryGraph D) (i : Fin 3) {T t : ℝ}
    (he : ContinuousOn e (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    (historyU D e u₀ t).val.val i =
      banachHistory (fun s => (e s).val.val i) (u₀.val.val i) t :=
  map_banachHistory (zeroCoordinate D i) e u₀ he ht

/-- 实际历史的两个原函数初值。T=0 也有效，不从空的内部方程推出额外事实。 -/
theorem history_initial (D : Rect) (e : ℝ → zeroBoundaryGraph D)
    (u₀ : zeroBoundaryGraph D) (F : ℝ → OriginalState D) (q₀ : ScalarL2 D.measure) :
    historyU D e u₀ 0 = u₀ ∧ historyQ D F q₀ 0 = q₀ :=
  ⟨banachHistory_initial e u₀, banachHistory_initial _ q₀⟩

/-- 实际 H₀¹ 历史求导，而非从逐点可导直接声称图范数可导。 -/
theorem historyU_hasDerivAt (D : Rect) (e : ℝ → zeroBoundaryGraph D)
    (u₀ : zeroBoundaryGraph D) {T t : ℝ}
    (he : ContinuousOn e (Icc 0 T)) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (historyU D e u₀) (e t) t := hasDerivAt_banachHistory e u₀ he ht

/-- 从 (2.3) 的梯度及磁通量定义物理辅助场；导数会由原磁方程推出。 -/
def phiX (D : Rect) (μ : ℝ) (u : ℝ → zeroBoundaryGraph D)
    (F : ℝ → OriginalState D) (t : ℝ) : ScalarL2 D.measure := μ • (F t).Hy - (u t).val.val 1

def phiY (D : Rect) (μ : ℝ) (u : ℝ → zeroBoundaryGraph D)
    (F : ℝ → OriginalState D) (t : ℝ) : ScalarL2 D.measure := -μ • (F t).Hx - (u t).val.val 2

/-- 原磁方程与 H₀¹ 历史的真实导数推出 φ 的实际 L² 演化。
这里还没有使用初始兼容，故含 Qx/Qy；五不变量随后把它们消去。 -/
theorem phi_hasDerivAt (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (ε κ τ μ : ℝ)
    (F : ℝ → OriginalState D) (dF : OriginalState D) (e : ℝ → zeroBoundaryGraph D)
    (u₀ : zeroBoundaryGraph D) {T t : ℝ} (L : weakHDivGraph D)
    (he : ContinuousOn e (Icc 0 T)) (ht : t ∈ Ioo 0 T)
    (hODE : OriginalAt D C ε κ τ μ F dF t (e t) L) :
    HasDerivAt (phiX D μ (historyU D e u₀) F)
      (-μ • (C.pCoeff.operator D.measure (F t).Hy - C.rCoeff.operator D.measure (F t).Hy) + (F t).Qy) t ∧
    HasDerivAt (phiY D μ (historyU D e u₀) F)
      (μ • (C.rCoeff.operator D.measure (F t).Hx - C.pCoeff.operator D.measure (F t).Hx) - (F t).Qx) t := by
  have hu := historyU_hasDerivAt D e u₀ he ht
  have hx := zeroCoordinate_hasDerivAt D 1 hu
  have hy := zeroCoordinate_hasDerivAt D 2 hu
  constructor
  · apply ((hODE.Hy.const_smul μ).sub hx).congr_deriv
    change μ • dF.Hy - (e t).val.val 1 = _
    rw [hODE.magneticY]
    simp only [neg_smul]
    abel
  · apply ((hODE.Hx.const_smul (-μ)).sub hy).congr_deriv
    change -μ • dF.Hx - (e t).val.val 2 = _
    rw [neg_smul, hODE.magneticX]
    abel

/-- (2.4) 的五个实际 L² 不变量，保留任意初值。
这里定义表达式，不把导数为零或兼容保持放入解的输入。 -/
def invariants (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (ε κ τ μ : ℝ)
    (F : ℝ → OriginalState D) (u : ℝ → zeroBoundaryGraph D)
    (q : ℝ → ScalarL2 D.measure) (t : ℝ) : Fin 5 → ScalarL2 D.measure :=
  ![q t + τ • (F t).P - κ • (u t).val.val 0,
    (F t).Z1 + ε • C.bCoeff.operator D.measure ((u t).val.val 0),
    (F t).Z2 + C.bCoeff.operator D.measure (q t),
    (F t).Qx - C.pCoeff.operator D.measure (phiY D μ u F t),
    (F t).Qy + C.rCoeff.operator D.measure (phiX D μ u F t)]

/-- 从全部原演化中实际用到的 Debye/记忆/磁辅助方程，推出五个 L² 零导数。
磁不变量使用刚由原磁方程证明的 φ 导数，不假设全时段兼容。
参数无需除法；包括全零及单向吸收。 -/
theorem invariants_hasDerivAt_zero (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (ε κ τ μ : ℝ)
    (F : ℝ → OriginalState D) (dF : OriginalState D) (e : ℝ → zeroBoundaryGraph D)
    (u₀ : zeroBoundaryGraph D) (q₀ : ScalarL2 D.measure) {T t : ℝ} (L : weakHDivGraph D)
    (he : ContinuousOn e (Icc 0 T)) (hP : ContinuousOn (fun s => (F s).P) (Icc 0 T))
    (ht : t ∈ Ioo 0 T) (hODE : OriginalAt D C ε κ τ μ F dF t (e t) L)
    (i : Fin 5) :
    HasDerivAt (fun s => invariants D C ε κ τ μ F (historyU D e u₀) (historyQ D F q₀) s i) 0 t := by
  have hu := zeroCoordinate_hasDerivAt D 0 (historyU_hasDerivAt D e u₀ he ht)
  have hq := hasDerivAt_banachHistory (fun s => (F s).P) q₀ hP ht
  have hphi := phi_hasDerivAt D C ε κ τ μ F dF e u₀ L he ht hODE
  fin_cases i
  · apply ((hq.add (hODE.P.const_smul τ)).sub (hu.const_smul κ)).congr_deriv
    change (F t).P + τ • dF.P - κ • (e t).val.val 0 = 0
    rw [hODE.electric_value, add_comm (F t).P, hODE.debye, sub_self]
  · apply (hODE.Z1.add (((C.bCoeff.operator D.measure).hasFDerivAt.comp_hasDerivAt t hu).const_smul ε)).congr_deriv
    change dF.Z1 + ε • C.bCoeff.operator D.measure ((e t).val.val 0) = 0
    rw [hODE.electric_value, hODE.memory1, neg_smul, neg_add_cancel]
  · apply (hODE.Z2.add ((C.bCoeff.operator D.measure).hasFDerivAt.comp_hasDerivAt t hq)).congr_deriv
    rw [hODE.memory2, neg_add_cancel]
  · apply (hODE.Qx.sub ((C.pCoeff.operator D.measure).hasFDerivAt.comp_hasDerivAt t hphi.2)).congr_deriv
    rw [hODE.auxiliaryX]
    abel
  · apply (hODE.Qy.add ((C.rCoeff.operator D.measure).hasFDerivAt.comp_hasDerivAt t hphi.1)).congr_deriv
    rw [hODE.auxiliaryY, ← map_add]
    simp only [neg_smul]
    have hzero : -(F t).Qy + μ • (C.pCoeff.operator D.measure (F t).Hy - C.rCoeff.operator D.measure (F t).Hy) +
        (-(μ • (C.pCoeff.operator D.measure (F t).Hy - C.rCoeff.operator D.measure (F t).Hy)) + (F t).Qy) = 0 := by abel
    rw [hzero, map_zero]

/-- 五个实际不变量的闭区间连续性，来自原场连续及真实历史；
没有要求它们已经等于初值。所有乘子只对时间不变的有界空间系数使用。 -/
theorem invariants_continuousOn (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (ε κ τ μ : ℝ)
    (F : ℝ → OriginalState D) (e : ℝ → zeroBoundaryGraph D)
    (u₀ : zeroBoundaryGraph D) (q₀ : ScalarL2 D.measure) {T : ℝ} (hT : 0 ≤ T)
    (he : ContinuousOn e (Icc 0 T)) (hF : OriginalContinuousOn F (Icc 0 T))
    (i : Fin 5) :
    ContinuousOn (fun s => invariants D C ε κ τ μ F (historyU D e u₀) (historyQ D F q₀) s i)
      (Icc 0 T) := by
  have hu := continuousOn_banachHistory e u₀ hT he
  have hq := continuousOn_banachHistory (fun s => (F s).P) q₀ hT hF.P
  have hcoord (j : Fin 3) : ContinuousOn (fun s => (historyU D e u₀ s).val.val j) (Icc 0 T) :=
    (zeroCoordinate D j).continuous.comp_continuousOn hu
  have hpx : ContinuousOn (phiX D μ (historyU D e u₀) F) (Icc 0 T) :=
    (hF.Hy.const_smul μ).sub (hcoord 1)
  have hpy : ContinuousOn (phiY D μ (historyU D e u₀) F) (Icc 0 T) :=
    (hF.Hx.const_smul (-μ)).sub (hcoord 2)
  fin_cases i
  · exact (hq.add (hF.P.const_smul τ)).sub ((hcoord 0).const_smul κ)
  · exact hF.Z1.add (((C.bCoeff.operator D.measure).continuous.comp_continuousOn (hcoord 0)).const_smul ε)
  · exact hF.Z2.add ((C.bCoeff.operator D.measure).continuous.comp_continuousOn hq)
  · exact hF.Qx.sub ((C.pCoeff.operator D.measure).continuous.comp_continuousOn hpy)
  · exact hF.Qy.add ((C.rCoeff.operator D.measure).continuous.comp_continuousOn hpx)

/-- V7 (2.4) 的全部五个真实 L² 不变量保持。原方程仅在 (0,T)，
历史在 H₀¹/L² 内通过实际积分构造；先保留任意初始常数场。
两个磁辅助不变量也在同一定理中，不再只是三个固定空间点实数结论。 -/
theorem all_invariants_eq_initial (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (ε κ τ μ : ℝ)
    (F dF : ℝ → OriginalState D) (e : ℝ → zeroBoundaryGraph D)
    (L : ℝ → weakHDivGraph D) (u₀ : zeroBoundaryGraph D) (q₀ : ScalarL2 D.measure)
    {T t : ℝ} (he : ContinuousOn e (Icc 0 T)) (hF : OriginalContinuousOn F (Icc 0 T))
    (hODE : ∀ s ∈ Ioo 0 T, OriginalAt D C ε κ τ μ F (dF s) s (e s) (L s))
    (ht : t ∈ Icc 0 T) (i : Fin 5) :
    invariants D C ε κ τ μ F (historyU D e u₀) (historyQ D F q₀) t i =
      invariants D C ε κ τ μ F (historyU D e u₀) (historyQ D F q₀) 0 i := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  apply banach_eq_initial_of_hasDerivAt_zero
    (fun s => invariants D C ε κ τ μ F (historyU D e u₀) (historyQ D F q₀) s i)
    (invariants_continuousOn D C ε κ τ μ F e u₀ q₀ hT he hF i) _ ht
  intro s hs
  exact invariants_hasDerivAt_zero D C ε κ τ μ F (dF s) e u₀ q₀ (L s)
    he hF.P hs (hODE s hs) i

/-- (2.5)：只从初始时刻五个不变量为零，推出整个有限闭区间兼容。
不是把全时段兼容放进弱原解定义；T=0 时结论就是给定初值。 -/
theorem all_invariants_zero_of_initial (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (ε κ τ μ : ℝ)
    (F dF : ℝ → OriginalState D) (e : ℝ → zeroBoundaryGraph D)
    (L : ℝ → weakHDivGraph D) (u₀ : zeroBoundaryGraph D) (q₀ : ScalarL2 D.measure)
    {T t : ℝ} (he : ContinuousOn e (Icc 0 T)) (hF : OriginalContinuousOn F (Icc 0 T))
    (hODE : ∀ s ∈ Ioo 0 T, OriginalAt D C ε κ τ μ F (dF s) s (e s) (L s))
    (hinitial : ∀ i, invariants D C ε κ τ μ F (historyU D e u₀) (historyQ D F q₀) 0 i = 0)
    (ht : t ∈ Icc 0 T) (i : Fin 5) :
    invariants D C ε κ τ μ F (historyU D e u₀) (historyQ D F q₀) t i = 0 := by
  rw [all_invariants_eq_initial D C ε κ τ μ F dF e L u₀ q₀ he hF hODE ht i]
  exact hinitial i

end LeanPML.PML.Weak
