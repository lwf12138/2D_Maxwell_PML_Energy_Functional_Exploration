import LeanPML.PML.WeakV7Regularity

/-!
# 命题 2.1 的弱图空间反向对应

标量路径 u、E 属于真实 H₀¹ 图，通量属于真实 H(div) 图。
辅助场定义为 λ−∇u；其演化与主方程是 primitive 输入，八条原式是输出。
这里只用内部邻域求导，不输入端点 PDE，不要求磁场法向为零。
-/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
open LeanPML.Analysis LeanPML.Rectangle
namespace LeanPML.PML.Weak

/-- (2.5) 的实际 L² 重构。μ≠0 在下游恢复磁方程时使用。 -/
def reverseFields (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (ε μ : ℝ)
    (u e : ℝ → zeroBoundaryGraph D) (L : ℝ → weakHDivGraph D)
    (P q : ℝ → ScalarL2 D.measure) (t : ℝ) : OriginalState D where
  E := (e t).val.val 0
  Hx := -(μ⁻¹ • (L t).val 1)
  Hy := μ⁻¹ • (L t).val 0
  P := P t
  Z1 := -ε • C.bCoeff.operator D.measure ((u t).val.val 0)
  Z2 := -C.bCoeff.operator D.measure (q t)
  Qx := C.pCoeff.operator D.measure ((L t).val 1 - (u t).val.val 2)
  Qy := -C.rCoeff.operator D.measure ((L t).val 0 - (u t).val.val 1)

/-- 原八个导数值；下条用 HasDerivAt 将其与重构路径绑定。
Ldot 是 H(div) 路径的导数值，Edot/Pdot 为真实 L² 导数。 -/
def reverseDerivatives (D : Rect) (C : SpatialAbsorption (ℝ × ℝ)) (ε μ : ℝ)
    (e : zeroBoundaryGraph D) (Ldot : weakHDivGraph D)
    (P Edot Pdot : ScalarL2 D.measure) : OriginalState D where
  E := Edot
  Hx := -(μ⁻¹ • Ldot.val 1)
  Hy := μ⁻¹ • Ldot.val 0
  P := Pdot
  Z1 := -ε • C.bCoeff.operator D.measure (e.val.val 0)
  Z2 := -C.bCoeff.operator D.measure P
  Qx := C.pCoeff.operator D.measure (Ldot.val 1 - e.val.val 2)
  Qy := -C.rCoeff.operator D.measure (Ldot.val 0 - e.val.val 1)

/-- (2.5) 经真实图空间投影和固定有界乘子求导，得到全部八个导数。
这里尚未使用 primitive 方程，故不会循环假设原八式。 -/
theorem reverse_hasDerivAt
    {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε μ t : ℝ}
    {u e : ℝ → zeroBoundaryGraph D} {L : ℝ → weakHDivGraph D}
    {P q : ℝ → ScalarL2 D.measure} {Ldot : weakHDivGraph D}
    {Edot Pdot : ScalarL2 D.measure}
    (hu : HasDerivAt u (e t) t) (he : HasDerivAt (fun s => (e s).val.val 0) Edot t)
    (hL : HasDerivAt L Ldot t) (hP : HasDerivAt P Pdot t)
    (hq : HasDerivAt q (P t) t) :
    OriginalHasDerivAt (reverseFields D C ε μ u e L P q)
      (reverseDerivatives D C ε μ (e t) Ldot (P t) Edot Pdot) t := by
  have hux := zeroCoordinate_hasDerivAt D 1 hu
  have huy := zeroCoordinate_hasDerivAt D 2 hu
  have hLx := hasDerivAt_weakHDiv_coordinate D 0 hL
  have hLy := hasDerivAt_weakHDiv_coordinate D 1 hL
  exact ⟨he, (hLy.const_smul μ⁻¹).neg, hLx.const_smul μ⁻¹, hP,
    (Analysis.hasDerivAt_operator (C.bCoeff.operator D.measure)
      (zeroCoordinate_hasDerivAt D 0 hu)).const_smul (-ε),
    (Analysis.hasDerivAt_operator (C.bCoeff.operator D.measure) hq).neg,
    Analysis.hasDerivAt_operator (C.pCoeff.operator D.measure) (hLy.sub huy),
    (Analysis.hasDerivAt_operator (C.rCoeff.operator D.measure) (hLx.sub hux)).neg⟩

/-- 命题 2.1 的反向、单个内部时刻版本。q+τP=κu 需在邻域成立才能求导；
辅助输入是实际 φ=λ−∇u 的 HasDerivAt，不是原磁方程或八式的预设。
输出带 H₀¹ 电场成员（PEC）、H(div) 通量成员和全部八式。 -/
theorem primitive_to_original_WeakAt
    {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ t : ℝ}
    {u e : ℝ → zeroBoundaryGraph D} {L : ℝ → weakHDivGraph D}
    {P q : ℝ → ScalarL2 D.measure} {Ldot : weakHDivGraph D}
    {Edot Pdot : ScalarL2 D.measure}
    (hμ : μ ≠ 0)
    (hu : HasDerivAt u (e t) t) (he : HasDerivAt (fun s => (e s).val.val 0) Edot t)
    (hL : HasDerivAt L Ldot t) (hP : HasDerivAt P Pdot t)
    (hq : HasDerivAt q (P t) t)
    (hpolar : ∀ᶠ s in 𝓝 t, q s + τ • P s = κ • (u s).val.val 0)
    (hx : HasDerivAt (fun s => (L s).val 0 - (u s).val.val 1)
      (C.rCoeff.operator D.measure ((u t).val.val 1) - C.pCoeff.operator D.measure ((L t).val 0)) t)
    (hy : HasDerivAt (fun s => (L s).val 1 - (u s).val.val 2)
      (C.pCoeff.operator D.measure ((u t).val.val 2) - C.rCoeff.operator D.measure ((L t).val 1)) t)
    (hmain : μ • (ε • (Edot + C.aCoeff.operator D.measure ((e t).val.val 0) +
        C.bCoeff.operator D.measure ((u t).val.val 0)) + Pdot +
        C.aCoeff.operator D.measure (P t) + C.bCoeff.operator D.measure (q t)) = (L t).val 2) :
    OriginalAt D C ε κ τ μ (reverseFields D C ε μ u e L P q)
      (reverseDerivatives D C ε μ (e t) Ldot (P t) Edot Pdot) t (e t) (L t) := by
  have hdx := ((hasDerivAt_weakHDiv_coordinate D 0 hL).sub
    (zeroCoordinate_hasDerivAt D 1 hu)).unique hx
  have hdy := ((hasDerivAt_weakHDiv_coordinate D 1 hL).sub
    (zeroCoordinate_hasDerivAt D 2 hu)).unique hy
  have hfluxX := sub_eq_iff_eq_add.mp hdx
  have hfluxY := sub_eq_iff_eq_add.mp hdy
  have hdebye : P t + τ • Pdot = κ • (e t).val.val 0 :=
    (hq.add (hP.const_smul τ)).unique
      (((zeroCoordinate_hasDerivAt D 0 hu).const_smul κ).congr_of_eventuallyEq hpolar)
  refine { reverse_hasDerivAt hu he hL hP hq with
    electric_value := rfl
    flux_x := ?_, flux_y := ?_, electric := ?_, magneticX := ?_, magneticY := ?_
    debye := ?_, memory1 := rfl, memory2 := rfl, auxiliaryX := ?_, auxiliaryY := ?_ }
  · simp [reverseFields, smul_smul, hμ]
  · simp [reverseFields, smul_smul, hμ]
  · change μ • (ε • Edot) = _
    rw [← hmain]
    dsimp [reverseFields, reverseDerivatives]
    simp only [smul_add, neg_smul, sub_neg_eq_add]
    abel
  · dsimp [reverseFields, reverseDerivatives]
    simp only [map_neg, map_smul, smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hμ,
      one_smul, map_sub]
    rw [hfluxY]
    try simp only [map_add, map_sub, map_neg]
    abel
  · dsimp [reverseFields, reverseDerivatives]
    simp only [map_neg, map_smul, smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hμ,
      one_smul, map_sub]
    rw [hfluxX]
    try simp only [map_add, map_sub, map_neg]
    abel
  · exact (add_comm _ _).trans hdebye
  · dsimp [reverseFields, reverseDerivatives]
    simp only [map_neg, map_smul, smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hμ,
      one_smul, map_sub]
    rw [hfluxY]
    try simp only [map_add, map_sub, map_neg]
    abel
  · dsimp [reverseFields, reverseDerivatives]
    simp only [map_neg, map_smul, smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hμ,
      one_smul, map_sub]
    rw [hfluxX]
    try simp only [map_add, map_sub, map_neg]
    abel

/-- 弱 primitive 的区间输入：图空间成员、真实时间导数、主/辅助演化与极化约束。
仅在 (0,T) 要求演化；闭区间极化关系属于 primitive 解类本身，不是原解的输入。
本结构不含 OriginalAt，也不含能量结论。 -/
structure PrimitiveIntervalData (D : Rect) (C : SpatialAbsorption (ℝ × ℝ))
    (ε κ τ μ T : ℝ) where
  u : ℝ → zeroBoundaryGraph D
  e : ℝ → zeroBoundaryGraph D
  flux : ℝ → weakHDivGraph D
  fluxDot : ℝ → weakHDivGraph D
  P : ℝ → ScalarL2 D.measure
  q : ℝ → ScalarL2 D.measure
  Edot : ℝ → ScalarL2 D.measure
  Pdot : ℝ → ScalarL2 D.measure
  hu : ∀ t ∈ Ioo 0 T, HasDerivAt u (e t) t
  he : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => (e s).val.val 0) (Edot t) t
  hflux : ∀ t ∈ Ioo 0 T, HasDerivAt flux (fluxDot t) t
  hP : ∀ t ∈ Ioo 0 T, HasDerivAt P (Pdot t) t
  hq : ∀ t ∈ Ioo 0 T, HasDerivAt q (P t) t
  polar : ∀ t ∈ Icc 0 T, q t + τ • P t = κ • (u t).val.val 0
  auxiliaryX : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => (flux s).val 0 - (u s).val.val 1)
      (C.rCoeff.operator D.measure ((u t).val.val 1) - C.pCoeff.operator D.measure ((flux t).val 0)) t
  auxiliaryY : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => (flux s).val 1 - (u s).val.val 2)
      (C.pCoeff.operator D.measure ((u t).val.val 2) - C.rCoeff.operator D.measure ((flux t).val 1)) t
  main : ∀ t ∈ Ioo 0 T,
    μ • (ε • (Edot t + C.aCoeff.operator D.measure ((e t).val.val 0) +
      C.bCoeff.operator D.measure ((u t).val.val 0)) + Pdot t +
      C.aCoeff.operator D.measure (P t) + C.bCoeff.operator D.measure (q t)) = (flux t).val 2

/-- 命题 2.1 反向的有限开区间包装：确实调用上面的八式及导数证明。
PEC 由 e∈H₀¹ 给出；没有假设端点 PDE 或磁场法向条件。 -/
theorem primitive_to_original_WeakOn
    {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (Q : PrimitiveIntervalData D C ε κ τ μ T) (hμ : μ ≠ 0) :
    ∀ t ∈ Ioo 0 T, OriginalAt D C ε κ τ μ
      (reverseFields D C ε μ Q.u Q.e Q.flux Q.P Q.q)
      (reverseDerivatives D C ε μ (Q.e t) (Q.fluxDot t) (Q.P t) (Q.Edot t) (Q.Pdot t))
      t (Q.e t) (Q.flux t) := by
  intro t ht
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 T := isOpen_Ioo.mem_nhds ht
  exact primitive_to_original_WeakAt hμ (Q.hu t ht) (Q.he t ht) (Q.hflux t ht)
    (Q.hP t ht) (Q.hq t ht)
    (hnear.mono fun s hs => Q.polar s (Ioo_subset_Icc_self hs))
    (Q.auxiliaryX t ht) (Q.auxiliaryY t ht) (Q.main t ht)

/-- 重构自动满足五个兼容关系，作为实际 L² 商类等式。
极化关系来自 primitive 约束，另外四条来自已规定的重构；不是原解输入。 -/
theorem reverse_compatible
    {D : Rect} {C : SpatialAbsorption (ℝ × ℝ)} {ε κ τ μ T : ℝ}
    (Q : PrimitiveIntervalData D C ε κ τ μ T) (hμ : μ ≠ 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    invariants D C ε κ τ μ (reverseFields D C ε μ Q.u Q.e Q.flux Q.P Q.q) Q.u Q.q t = 0 := by
  funext i
  fin_cases i <;>
    simp [invariants, reverseFields, phiX, phiY, smul_smul, hμ, Q.polar t ht]
end LeanPML.PML.Weak
