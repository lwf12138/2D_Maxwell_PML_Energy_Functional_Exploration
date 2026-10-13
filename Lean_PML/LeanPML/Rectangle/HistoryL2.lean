import LeanPML.Rectangle.L2Paths
import LeanPML.PML.OriginalSystem

/-!
# v0.4.4：逐点历史积分与真实 L² Bochner 历史的一致性

V7 (2.3)。初始原函数 f₀ 保留为任意光滑函数，绝不默认零。
先在 C(闭矩形) 中构造历史，再由求值连续线性映射证明它恰为逐点积分；
由 continuousToL2 的积分交换证明同一个历史在真实 L² 中也成立。
积分合法性由闭时间区间的一致范数连续性得到，包含 T=0 和 t=0。
本文件不证明一般解存在性，也不证明提升规范唯一性。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology
open LeanPML.Analysis LeanPML.PML.Concrete
namespace LeanPML.Rectangle

/-- (2.3) 在 C(K) 中的真实 Bochner 历史构造。
只有输入曲线实际可积时，下方定理才登记其分析含义。 -/
def continuousHistory (D : Rect) (F : ℝ → SmoothField) (f₀ : SmoothField)
    (t : ℝ) : ContinuousField D :=
  restrictContinuous D f₀ + ∫ s in (0:ℝ)..t, restrictContinuous D (F s)

/-- 闭区间一致范数连续性给历史积分的实际可积性。
只使用 [0,T] 上连续；不要求区间外的 PDE 或时间导数。 -/
theorem history_intervalIntegrable (D : Rect) (F : ℝ → SmoothField) (T : ℝ)
    (hF : ContinuousOn (fun s => restrictContinuous D (F s)) (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s => restrictContinuous D (F s)) volume 0 t :=
  (hF.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

/-- 求值与 Bochner 积分交换，所以 C(K) 历史不是另一个不相干的定义：
每个闭矩形点的值严格等于 OriginalSystem.integralLift 的真实逐点历史。 -/
theorem continuousHistory_apply (D : Rect) (F : ℝ → SmoothField) (f₀ : SmoothField)
    (t : ℝ) (hintegrable : IntervalIntegrable (fun s => restrictContinuous D (F s))
      volume 0 t) (z : D.closedSet) :
    continuousHistory D F f₀ t z =
      integralLift (fun s x => F s x) f₀ t z := by
  have heval := (ContinuousMap.evalCLM ℝ z : ContinuousField D →L[ℝ] ℝ).intervalIntegral_comp_comm hintegrable
  change f₀ z + (∫ s in (0:ℝ)..t, restrictContinuous D (F s)) z =
    f₀ z + ∫ s in (0:ℝ)..t, F s z
  congr 1
  exact heval.symm

/-- 实际 L² 历史与 C(K) 历史一致。两边是真实函数空间积分，
不是把任意数命名为历史或范数；积分交换由连续线性映射的 mathlib 定理完成。 -/
theorem continuousHistory_toL2 (D : Rect) (F : ℝ → SmoothField) (f₀ : SmoothField)
    (t : ℝ) (hintegrable : IntervalIntegrable (fun s => restrictContinuous D (F s))
      volume 0 t) :
    continuousToL2 D (continuousHistory D F f₀ t) =
      SmoothField.toL2 D f₀ + ∫ s in (0:ℝ)..t, SmoothField.toL2 D (F s) := by
  have hmap := (continuousToL2 D).intervalIntegral_comp_comm hintegrable
  rw [continuousHistory, map_add, continuousToL2_restrict]
  congr 1
  simpa only [continuousToL2_restrict] using hmap.symm

/-- 任意光滑 u 切片若等于实际逐点历史，则其旧 toL2 表示等于 Bochner 历史。
输入只识别函数，不预设导数、五不变量或能量性质；总装用历史定义本身提供它。 -/
theorem toL2_integralLift (D : Rect) (F : ℝ → SmoothField) (f₀ u : SmoothField)
    (t : ℝ) (hintegrable : IntervalIntegrable (fun s => restrictContinuous D (F s))
      volume 0 t)
    (hu : ∀ z : D.closedSet, u z = integralLift (fun s x => F s x) f₀ t z) :
    SmoothField.toL2 D u = SmoothField.toL2 D f₀ +
      ∫ s in (0:ℝ)..t, SmoothField.toL2 D (F s) := by
  have hfunctions : restrictContinuous D u = continuousHistory D F f₀ t := by
    apply ContinuousMap.ext
    intro z
    exact (hu z).trans (continuousHistory_apply D F f₀ t hintegrable z).symm
  rw [← continuousToL2_restrict D u, hfunctions]
  exact continuousHistory_toL2 D F f₀ t hintegrable

/-- [0,T] 入口自动给出可积证据，并将逐点历史接到实际 L² 积分。
当 T=0 时 ht 强制 t=0，数学式仍成立；无内部导数需求。 -/
theorem toL2_integralLift_on_Icc (D : Rect) (F : ℝ → SmoothField) (f₀ : SmoothField)
    (u : ℝ → SmoothField) (T : ℝ)
    (hF : ContinuousOn (fun s => restrictContinuous D (F s)) (Icc 0 T))
    (hu : ∀ t ∈ Icc 0 T, ∀ z : D.closedSet,
      u t z = integralLift (fun s x => F s x) f₀ t z)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    SmoothField.toL2 D (u t) = SmoothField.toL2 D f₀ +
      ∫ s in (0:ℝ)..t, SmoothField.toL2 D (F s) :=
  toL2_integralLift D F f₀ (u t) t (history_intervalIntegrable D F T hF ht) (hu t ht)

end LeanPML.Rectangle
