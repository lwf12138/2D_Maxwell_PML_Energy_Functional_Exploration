import LeanPML.Rectangle.Boundary
import LeanPML.PML.OriginalSystem
import LeanPML.Time.Constancy

/-!
# v0.4.3：PEC、历史提升和两层外边界

对应 V7 (2.2)、(2.3)、(6.3)、(7.5)。边界取整个矩形四边，包含角点。
u 的零迹来自 u₀ 零迹和 u_t=E；仅 E=0 本身不足以推出 u=0。
E_t 的内部零迹来自对真实时间常值函数求导；T>0 时由闭区间连续性延到端点。
T=0 无内部信息，明确保留初始图状态 E_t(0) 的零迹兼容，绝不以空条件推导它。
没有磁场法向约束，也不处理内部子区边界。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open LeanPML.PML.Concrete
namespace LeanPML.Rectangle

/-- 整个矩形外边界：闭矩形中至少一个坐标位于端点，包含四个角点。 -/
def Rect.boundarySet (D : Rect) : Set (ℝ × ℝ) :=
  {z | z ∈ D.closedSet ∧
    (z.1 = D.xhi ∨ z.1 = D.xlo ∨ z.2 = D.yhi ∨ z.2 = D.ylo)}

/-- 四边逐条零迹与整个外边界上的零值一致；供原系统 PEC 的集合表示使用。 -/
theorem zeroBoundary_iff_forall_boundary (D : Rect) (f : ℝ × ℝ → ℝ) :
    ZeroBoundary D f ↔ ∀ z ∈ D.boundarySet, f z = 0 := by
  constructor
  · intro hzero z hz
    rcases z with ⟨x,y⟩
    rcases hz with ⟨hclosed,hside⟩
    rcases hside with hright | hleft | htop | hbottom
    · change x = D.xhi at hright
      rw [hright]
      exact hzero.1 y hclosed.2
    · change x = D.xlo at hleft
      rw [hleft]
      exact hzero.2.1 y hclosed.2
    · change y = D.yhi at htop
      rw [htop]
      exact hzero.2.2.1 x hclosed.1
    · change y = D.ylo at hbottom
      rw [hbottom]
      exact hzero.2.2.2 x hclosed.1
  · intro hzero
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy
      exact hzero (D.xhi,y) ⟨⟨⟨D.x_lt.le,le_rfl⟩,hy⟩,Or.inl rfl⟩
    · intro y hy
      exact hzero (D.xlo,y) ⟨⟨⟨le_rfl,D.x_lt.le⟩,hy⟩,Or.inr (Or.inl rfl)⟩
    · intro x hx
      exact hzero (x,D.yhi) ⟨⟨hx,⟨D.y_lt.le,le_rfl⟩⟩,Or.inr (Or.inr (Or.inl rfl))⟩
    · intro x hx
      exact hzero (x,D.ylo) ⟨⟨hx,⟨le_rfl,D.y_lt.le⟩⟩,Or.inr (Or.inr (Or.inr rfl))⟩

/-- V7 (2.2)、(2.3)→原层位移的零迹。
闭时间连续 + 内部真实 u_t=E + u₀ 零迹 + PEC 是输入；全时段 u 零迹是结论。
调用旧 Time 常值定理，所以不需要时间端点的双侧导数。 -/
theorem zeroBoundary_of_velocity_PEC (D : Rect) (u E : Field) (T : ℝ)
    (hT : 0 ≤ T)
    (hu_cont : ∀ z ∈ D.boundarySet, ContinuousOn (fun t => u t z) (Icc 0 T))
    (hu_deriv : ∀ t ∈ Ioo 0 T, ∀ z ∈ D.boundarySet,
      HasDerivAt (fun s => u s z) (E t z) t)
    (hu_initial : ZeroBoundary D (u 0))
    (hPEC : ∀ t ∈ Icc 0 T, ZeroBoundary D (E t))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ZeroBoundary D (u t) := by
  apply (zeroBoundary_iff_forall_boundary D (u t)).mpr
  intro z hz
  have hzero_deriv : ∀ s ∈ Ioo 0 T, HasDerivAt (fun a => u a z) 0 s := by
    intro s hs
    have hEzero := (zeroBoundary_iff_forall_boundary D (E s)).mp
      (hPEC s ⟨hs.1.le,hs.2.le⟩) z hz
    simpa only [hEzero] using hu_deriv s hs z hz
  have hconstant := LeanPML.Time.eq_initial_of_hasDerivAt_zero
    (fun s => u s z) T hT (hu_cont z hz) hzero_deriv ht
  exact hconstant.trans ((zeroBoundary_iff_forall_boundary D (u 0)).mp hu_initial z hz)

/-- 真历史提升调用上面的保持定理；初始原函数不默认零，只要求四边零迹。
这里全实轴连续仅是延拓正则性，方程和 PEC 仍只在 [0,T] 使用。 -/
theorem integralLift_zeroBoundary (D : Rect) (E : Field) (u₀ : Point → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hE_cont : ∀ z ∈ D.boundarySet, Continuous (fun t => E t z))
    (hu₀ : ZeroBoundary D u₀) (hPEC : ∀ t ∈ Icc 0 T, ZeroBoundary D (E t))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ZeroBoundary D (integralLift E u₀ t) := by
  apply zeroBoundary_of_velocity_PEC D (integralLift E u₀) E T hT
  · intro z hz
    exact (continuous_integralLift E u₀ z (hE_cont z hz)).continuousOn
  · intro s hs z hz
    exact hasDerivAt_integralLift E u₀ z (hE_cont z hz) s
  · simpa [ZeroBoundary, integralLift] using hu₀
  · exact hPEC
  · exact ht

/-- PEC 的真实时间导数在开区间的四边为零。
零导数由邻域内 E=0 推出；只在一个时刻 E=0 不能作此推断。 -/
theorem velocity_PEC_on_Ioo (D : Rect) (E Edot : Field) (T : ℝ)
    (hPEC : ∀ t ∈ Icc 0 T, ZeroBoundary D (E t))
    (hEdot : ∀ t ∈ Ioo 0 T, ∀ z ∈ D.boundarySet,
      HasDerivAt (fun s => E s z) (Edot t z) t)
    {t : ℝ} (ht : t ∈ Ioo 0 T) : ZeroBoundary D (Edot t) := by
  apply (zeroBoundary_iff_forall_boundary D (Edot t)).mpr
  intro z hz
  have hnear : (fun s => E s z) =ᶠ[𝓝 t] (fun _ => (0:ℝ)) :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) (fun s hs =>
      (zeroBoundary_iff_forall_boundary D (E s)).mp
        (hPEC s ⟨hs.1.le,hs.2.le⟩) z hz)
  have hzero_deriv : HasDerivAt (fun s => E s z) 0 t :=
    (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hnear
  exact (hEdot t ht z hz).unique hzero_deriv

/-- T>0 时，E_t 的闭区间连续性把内部零迹延到两个端点。
这里不额外要求端点处 E 的普通双侧导数。 -/
theorem velocity_PEC_on_Icc_of_pos (D : Rect) (E Edot : Field) (T : ℝ)
    (hT : 0 < T) (hPEC : ∀ t ∈ Icc 0 T, ZeroBoundary D (E t))
    (hEdot : ∀ t ∈ Ioo 0 T, ∀ z ∈ D.boundarySet,
      HasDerivAt (fun s => E s z) (Edot t z) t)
    (hEdot_cont : ∀ z ∈ D.boundarySet, ContinuousOn (fun t => Edot t z) (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ZeroBoundary D (Edot t) := by
  apply (zeroBoundary_iff_forall_boundary D (Edot t)).mpr
  intro z hz
  have hzero_open : EqOn (fun s => Edot s z) (fun _ => (0:ℝ)) (Ioo 0 T) := by
    intro s hs
    exact (zeroBoundary_iff_forall_boundary D (Edot s)).mp
      (velocity_PEC_on_Ioo D E Edot T hPEC hEdot hs) z hz
  have hclosure : Icc (0:ℝ) T ⊆ closure (Ioo 0 T) := by
    rw [closure_Ioo hT.ne]
  exact hzero_open.of_subset_closure (hEdot_cont z hz) continuousOn_const
    Ioo_subset_Icc_self hclosure ht

/-- 含 T=0 的导数层零迹入口。退化时仅使用单独给出的初始图状态迹兼容；
T>0 时该附加条件完全不被使用，而由上一条真实分析结果提供全部端点。 -/
theorem velocity_PEC_on_Icc (D : Rect) (E Edot : Field) (T : ℝ)
    (hT : 0 ≤ T) (hPEC : ∀ t ∈ Icc 0 T, ZeroBoundary D (E t))
    (hEdot : ∀ t ∈ Ioo 0 T, ∀ z ∈ D.boundarySet,
      HasDerivAt (fun s => E s z) (Edot t z) t)
    (hEdot_cont : ∀ z ∈ D.boundarySet, ContinuousOn (fun t => Edot t z) (Icc 0 T))
    (hzero_time : T = 0 → ZeroBoundary D (Edot 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ZeroBoundary D (Edot t) := by
  by_cases hTzero : T = 0
  · have htzero : t = 0 := by rw [hTzero] at ht; exact le_antisymm ht.2 ht.1
    rw [htzero]
    exact hzero_time hTzero
  · exact velocity_PEC_on_Icc_of_pos D E Edot T
      (lt_of_le_of_ne hT (Ne.symm hTzero)) hPEC hEdot hEdot_cont ht

/-- 两层所需四项边界：U₀ 用 u、E，U₁ 用 E、E_t。
相同的 E 零迹只记录一次；所有结论来自真实提升/导数及初始兼容。 -/
theorem twoLayer_zeroBoundary (D : Rect) (u E Edot : Field) (T : ℝ)
    (hT : 0 ≤ T)
    (hu_cont : ∀ z ∈ D.boundarySet, ContinuousOn (fun t => u t z) (Icc 0 T))
    (hu_deriv : ∀ t ∈ Ioo 0 T, ∀ z ∈ D.boundarySet,
      HasDerivAt (fun s => u s z) (E t z) t)
    (hu_initial : ZeroBoundary D (u 0))
    (hPEC : ∀ t ∈ Icc 0 T, ZeroBoundary D (E t))
    (hEdot : ∀ t ∈ Ioo 0 T, ∀ z ∈ D.boundarySet,
      HasDerivAt (fun s => E s z) (Edot t z) t)
    (hEdot_cont : ∀ z ∈ D.boundarySet, ContinuousOn (fun t => Edot t z) (Icc 0 T))
    (hzero_time : T = 0 → ZeroBoundary D (Edot 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ZeroBoundary D (u t) ∧ ZeroBoundary D (E t) ∧ ZeroBoundary D (Edot t) :=
  ⟨zeroBoundary_of_velocity_PEC D u E T hT hu_cont hu_deriv hu_initial hPEC ht,
    hPEC t ht, velocity_PEC_on_Icc D E Edot T hT hPEC hEdot hEdot_cont hzero_time ht⟩

end LeanPML.Rectangle
