import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import LeanPML.Analysis.EnergyCalculus

/-!
# v0.4.3：真实时间与空间导数的交换

V7 (6.6)、(2.3) 与 (7.5) 所需的混合求导；原文未为这些辅助分析结论单列编号。
本轮选用联合 C∞ 延拓，这是比 V7 弱空间正则性更强的输入，但不要求域外满足方程。
空间方向导数使用实际 fderiv，时间导数由 HasDerivAt 绑定。
先从 mathlib 的二阶导数对称性证明交换，再连接真实函数的时间导数。
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace LeanPML.Rectangle

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- 联合光滑函数的空间导数等于全导数作用在 (0,v) 上。
由真实链式法则推出，不是给导数槽起一个名称。下游用于混合求导。 -/
theorem spaceFDeriv_eq_full {F : ℝ → X → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) (x v : X) :
    fderiv ℝ (F t) x v = fderiv ℝ (Function.uncurry F) (t,x) (0,v) := by
  have hfull := (hF.differentiable (by simp) (t,x)).hasFDerivAt
  have hslice := hfull.comp x (hasFDerivAt_prodMk_right t x)
  have hderiv := congrArg (fun A : X →L[ℝ] ℝ => A v) hslice.fderiv
  simpa [Function.comp_def, Function.uncurry] using hderiv

/-- 联合光滑函数的实际时间导数等于全导数作用在 (1,0) 上。
这是证明内时段混合导数的辅助分析结论，不要求任何 PDE。 -/
theorem timeDeriv_eq_full {F : ℝ → X → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) (x : X) :
    deriv (fun s => F s x) t = fderiv ℝ (Function.uncurry F) (t,x) (1,0) := by
  have hfull := (hF.differentiable (by simp) (t,x)).hasFDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => (s,x)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (hfull.comp_hasDerivAt t hcurve).deriv

/-- V7 (6.6) 的光滑实现：∂t(∂v F)=∂v(∂t F)。
输入联合 C∞；实际证明只在这里使用 C² 所提供的二阶导数对称性。
没有将微分交换写进正则性字段；导数来自链式法则与 mathlib 的对称性定理。 -/
theorem hasDerivAt_spaceFDeriv {F : ℝ → X → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) (x v : X) :
    HasDerivAt (fun s => fderiv ℝ (F s) x v)
      (fderiv ℝ (fun y => deriv (fun s => F s y) t) x v) t := by
  let g := Function.uncurry F
  have hsecond : Differentiable ℝ (fderiv ℝ g) :=
    ((contDiff_infty_iff_fderiv.mp hF).2).differentiable (by simp)
  have heval (w : ℝ × X) : HasFDerivAt (fun z => fderiv ℝ g z w)
      ((fderiv ℝ (fderiv ℝ g) (t,x)).flip w) (t,x) := by
    simpa using (hsecond (t,x)).hasFDerivAt.clm_apply
      (hasFDerivAt_const w (t,x))
  have hcurve : HasDerivAt (fun s : ℝ => (s,x)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have htime := (heval (0,v)).comp_hasDerivAt t hcurve
  have hspace := (heval (1,0)).comp x (hasFDerivAt_prodMk_right t x)
  have hspace_value := congrArg (fun A : X →L[ℝ] ℝ => A v) hspace.fderiv
  have hsymm := (hF.contDiffAt (x := (t,x))).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) (1,0) (0,v)
  have htime_function : (fun s => fderiv ℝ (F s) x v) =
      (fun s => fderiv ℝ g (s,x) (0,v)) :=
    funext (fun s => spaceFDeriv_eq_full hF s x v)
  have hspace_function : (fun y => deriv (fun s => F s y) t) =
      (fun y => fderiv ℝ g (t,y) (1,0)) :=
    funext (fun y => timeDeriv_eq_full hF t y)
  rw [htime_function, hspace_function]
  apply htime.congr_deriv
  exact (hspace_value.trans hsymm.symm).symm

/-- 实际使用的时间—空间交换接口：若 F_t=E 在 x 的空间邻域成立，
则 (∂v F)_t=∂v E。邻域条件只需来自矩形内部，不要求域外 PDE。
HasDerivAt 的函数是原时间切片、值是 E(t,y)、点是 t；单点等式不够用于空间求导。 -/
theorem hasDerivAt_spaceFDeriv_of_timeDeriv {F E : ℝ → X → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) (x v : X)
    (hnear : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s => F s y) (E t y) t) :
    HasDerivAt (fun s => fderiv ℝ (F s) x v) (fderiv ℝ (E t) x v) t := by
  have hsame : (fun y => deriv (fun s => F s y) t) =ᶠ[𝓝 x] E t :=
    hnear.mono (fun y hy => hy.deriv)
  have hspatial : fderiv ℝ (fun y => deriv (fun s => F s y) t) x =
      fderiv ℝ (E t) x := hsame.fderiv_eq
  rw [← hspatial]
  exact hasDerivAt_spaceFDeriv hF t x v

end LeanPML.Rectangle
