import LeanPML.Rectangle.WeakPoincare

/-!
# 弱图范数路径的真实时间导数

由 V7 (6.6) 引出的接口连接，原文未单列。
采用真实 H¹/H(div) 图范数中的 HasDerivAt；连续投影给出函数、梯度及散度
各自在 L² 中的时间导数。没有假设坐标逐点可导就自动得到图范数可导。
这放宽空间 C∞，但不自动建立原系统的弱路径或加权传播。
-/
noncomputable section
open MeasureTheory
open LeanPML.Analysis
namespace LeanPML.Rectangle

/-- H¹ 图的第 i 个坐标是有界线性映射；i=0 是函数，i=1,2 是真实弱偏导。
界由既有最大值图范数控制给出，不把梯度误建为整个 L² 上的有界算子。 -/
def weakH1Coordinate (D : Rect) (i : Fin 3) : weakH1Graph D →L[ℝ] ScalarL2 D.measure :=
  (((LinearMap.proj i).comp (weakH1Graph D).subtype)).mkContinuous 1
    (fun U => by simpa using weakH1_coordinate_norm_le D U i)

/-- H(div) 图的有界坐标投影；i=2 恰为真实弱散度。 -/
def weakHDivCoordinate (D : Rect) (i : Fin 3) : weakHDivGraph D →L[ℝ] ScalarL2 D.measure :=
  (((LinearMap.proj i).comp (weakHDivGraph D).subtype)).mkContinuous 1
    (fun U => by simpa using weakHDiv_coordinate_norm_le D U i)

/-- 若 H¹ 图路径真实可导，则梯度与时间求导交换。
更准确地，结论对三个坐标逐一成立，导数是图导数的相同坐标。
正则性输入是图范数 HasDerivAt，未输入目标交换公式。 -/
theorem hasDerivAt_weakH1_coordinate (D : Rect) (i : Fin 3)
    {U : ℝ → weakH1Graph D} {Udot : weakH1Graph D} {t : ℝ}
    (hpath : HasDerivAt U Udot t) :
    HasDerivAt (fun s => (U s).val i) (Udot.val i) t :=
  (weakH1Coordinate D i).hasFDerivAt.comp_hasDerivAt t hpath

/-- 同理，H(div) 图路径可导推出散度的 L² 时间导数。
用于导数层空间正则性；不要求通量每个分量都属于 H¹。 -/
theorem hasDerivAt_weakHDiv_coordinate (D : Rect) (i : Fin 3)
    {L : ℝ → weakHDivGraph D} {Ldot : weakHDivGraph D} {t : ℝ}
    (hpath : HasDerivAt L Ldot t) :
    HasDerivAt (fun s => (L s).val i) (Ldot.val i) t :=
  (weakHDivCoordinate D i).hasFDerivAt.comp_hasDerivAt t hpath

end LeanPML.Rectangle
