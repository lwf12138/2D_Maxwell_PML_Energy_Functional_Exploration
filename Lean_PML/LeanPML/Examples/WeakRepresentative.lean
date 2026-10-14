import LeanPML.Analysis.WeakIntervalRepresentative

/-!
# 非恒定弱系数的一维代表构造调用

f(x)=x+1 在 (-1,1) 的弱导数为 1。这里先证明真实测试积分关系，
再调用一般代表构造；不是把 Lipschitz 代表存在作为输入。
二维分离区域及最终 PDE 入口的调用在后续桥接模块完成。
-/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace LeanPML.Examples.WeakRepresentative
open LeanPML.Analysis

/-- 非恒定区域系数的实际弱导数证据。 -/
theorem affine_weak (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (-1 : ℝ) 1) :
    (∫ x, deriv η x*(x+1)) = -(∫ x, η x*(1 : ℝ)) := by
  have hprimitive := integral_primitive_weak_derivative (by norm_num : (-1 : ℝ)<1)
    (fun _ => (1 : ℝ)) continuous_const.locallyIntegrable η hη hc hs
  simpa using hprimitive

/-- 输入并非恒定系数；一般弱代表定理实际用于仿射剖面。
返回的是 a.e. 等价与 Lipschitz 性，尚不宣称已完成二维系数总装。 -/
theorem affine_representative :
    ∃ F : ℝ → ℝ, LipschitzWith 1 F ∧
      (fun x : ℝ => x+1) =ᵐ[volume.restrict (Ioo (-1) 1)] F := by
  apply exists_lipschitz_representative (by norm_num : (-1 : ℝ)<1)
    (fun x => x+1) (fun _ => 1)
    (continuous_id.add continuous_const).locallyIntegrable continuous_const.locallyIntegrable
    (1 : NNReal) (by filter_upwards [] with x; norm_num)
  exact affine_weak

end LeanPML.Examples.WeakRepresentative
