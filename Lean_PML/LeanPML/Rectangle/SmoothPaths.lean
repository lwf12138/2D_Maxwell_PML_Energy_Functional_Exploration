import LeanPML.Rectangle.TimeSpace
import LeanPML.Rectangle.L2Paths
import LeanPML.PML.WeightedCalculus

/-!
# v0.4.3：光滑场的同源时间层

为兑现 V7 (6.6) 所需接口，本阶段采用更强的技术正则性：联合 C∞ 延拓，
以及闭矩形一致范数曲线的连续/可微性。这些额外条件不是从 (6.6) 推出的；
下方证明是在这些条件下得到真实混合导数与 L² 导数，原文未单列。
技术延拓只提供导数，原 PDE 仍只在 (0,T)×Ω 成立。
`SmoothTimeJet` 中每个导数值均绑定实际 HasDerivAt；空间交换则是下方证明，
绝不把交换恒等式放进结构。普通路径由 C(K)→L² 连续线性映射取得。
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
open LeanPML.Analysis
namespace LeanPML.Rectangle

/-- 一个实际时空场及其前两阶时间导数。两个 HasDerivAt 字段是实际时间
正则性，不能用普通数值等式替代。用于历史提升 u 时，首个字段由 FTC 填入。
联合光滑字段供真实混合导数交换使用；不含 PDE、边界、兼容或能量条件。 -/
structure SmoothTimeJet where
  value : ℝ → SmoothField
  first : ℝ → SmoothField
  second : ℝ → SmoothField
  joint_value : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => value z.1 z.2)
  joint_first : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => first z.1 z.2)
  deriv_value : ∀ t x, HasDerivAt (fun s => value s x) (first t x) t
  deriv_first : ∀ t x, HasDerivAt (fun s => first s x) (second t x) t

/-- 所选光滑延拓的一致范数正则性。输入只说 C(K) 路径连续/可微，
不预设其导数值或 L² 求导结论。梯度路径也需统一控制，不能仅靠逐点可导。
这些全轴条件仅为技术延拓正则性；本轮没有让 PDE 在全轴成立。 -/
structure UniformTimeJet (D : Rect) (J : SmoothTimeJet) : Prop where
  continuous_value : Continuous (fun t => restrictContinuous D (J.value t))
  continuous_first : Continuous (fun t => restrictContinuous D (J.first t))
  continuous_second : Continuous (fun t => restrictContinuous D (J.second t))
  differentiable_value : Differentiable ℝ (fun t => restrictContinuous D (J.value t))
  differentiable_first : Differentiable ℝ (fun t => restrictContinuous D (J.first t))
  differentiable_dx_value : Differentiable ℝ
    (fun t => restrictContinuous D (J.value t).derivativeX)
  differentiable_dy_value : Differentiable ℝ
    (fun t => restrictContinuous D (J.value t).derivativeY)
  differentiable_dx_first : Differentiable ℝ
    (fun t => restrictContinuous D (J.first t).derivativeX)
  differentiable_dy_first : Differentiable ℝ
    (fun t => restrictContinuous D (J.first t).derivativeY)

/-- 真正 L² 中 value 的导数是同源 first。先在 C(K) 用点值识别，再用连续
线性映射传到 L²；不是直接将逐点导数当成 L² 导数。 -/
theorem hasDerivAt_jet_value_L2 (D : Rect) (J : SmoothTimeJet)
    (hregular : UniformTimeJet D J) (t : ℝ) :
    HasDerivAt (fun s => SmoothField.toL2 D (J.value s))
      (SmoothField.toL2 D (J.first t)) t :=
  hasDerivAt_toL2_of_pointwise D J.value (J.first t) t
    (hregular.differentiable_value t) (fun x => J.deriv_value t x)

/-- 第二次真实 L² 求导。同源 second 在极化槽中就是 P_tt，
其连续性另由 uniform 正则性提供，供有限区间积分平衡使用。 -/
theorem hasDerivAt_jet_first_L2 (D : Rect) (J : SmoothTimeJet)
    (hregular : UniformTimeJet D J) (t : ℝ) :
    HasDerivAt (fun s => SmoothField.toL2 D (J.first s))
      (SmoothField.toL2 D (J.second t)) t :=
  hasDerivAt_toL2_of_pointwise D J.first (J.second t) t
    (hregular.differentiable_first t) (fun x => J.deriv_first t x)

/-- 时间—x 偏导交换后的真实 L² 导数。联合 C∞ 给出真实混合导数相等，
一致范数可微性负责合法进入 L²；两种论证均不可省。 -/
theorem hasDerivAt_jet_gradientX (D : Rect) (J : SmoothTimeJet)
    (hregular : UniformTimeJet D J) (t : ℝ) :
    HasDerivAt (fun s => SmoothField.toL2 D (J.value s).derivativeX)
      (SmoothField.toL2 D (J.first t).derivativeX) t := by
  apply hasDerivAt_toL2_of_pointwise D _ _ t (hregular.differentiable_dx_value t)
  intro x
  exact hasDerivAt_spaceFDeriv_of_timeDeriv
    (F := fun s y => J.value s y) (E := fun s y => J.first s y) J.joint_value t (x : ℝ × ℝ) (1,0)
    (Filter.Eventually.of_forall (fun y => J.deriv_value t y))

/-- 时间—y 偏导的同一证明；保持 x/y 两方向独立。 -/
theorem hasDerivAt_jet_gradientY (D : Rect) (J : SmoothTimeJet)
    (hregular : UniformTimeJet D J) (t : ℝ) :
    HasDerivAt (fun s => SmoothField.toL2 D (J.value s).derivativeY)
      (SmoothField.toL2 D (J.first t).derivativeY) t := by
  apply hasDerivAt_toL2_of_pointwise D _ _ t (hregular.differentiable_dy_value t)
  intro x
  exact hasDerivAt_spaceFDeriv_of_timeDeriv
    (F := fun s y => J.value s y) (E := fun s y => J.first s y) J.joint_value t (x : ℝ × ℝ) (0,1)
    (Filter.Eventually.of_forall (fun y => J.deriv_value t y))

/-- 导数层的 x 混合求导；不能只完成原层 u/E 而跳过 E/E_t。 -/
theorem hasDerivAt_jet_first_gradientX (D : Rect) (J : SmoothTimeJet)
    (hregular : UniformTimeJet D J) (t : ℝ) :
    HasDerivAt (fun s => SmoothField.toL2 D (J.first s).derivativeX)
      (SmoothField.toL2 D (J.second t).derivativeX) t := by
  apply hasDerivAt_toL2_of_pointwise D _ _ t (hregular.differentiable_dx_first t)
  intro x
  exact hasDerivAt_spaceFDeriv_of_timeDeriv
    (F := fun s y => J.first s y) (E := fun s y => J.second s y) J.joint_first t (x : ℝ × ℝ) (1,0)
    (Filter.Eventually.of_forall (fun y => J.deriv_first t y))

/-- 导数层的 y 混合求导。 -/
theorem hasDerivAt_jet_first_gradientY (D : Rect) (J : SmoothTimeJet)
    (hregular : UniformTimeJet D J) (t : ℝ) :
    HasDerivAt (fun s => SmoothField.toL2 D (J.first s).derivativeY)
      (SmoothField.toL2 D (J.second t).derivativeY) t := by
  apply hasDerivAt_toL2_of_pointwise D _ _ t (hregular.differentiable_dy_first t)
  intro x
  exact hasDerivAt_spaceFDeriv_of_timeDeriv
    (F := fun s y => J.first s y) (E := fun s y => J.second s y) J.joint_first t (x : ℝ × ℝ) (0,1)
    (Filter.Eventually.of_forall (fun y => J.deriv_first t y))

/-- 实际散度的时间交换由两条已证分量导数相加得到。
后续用它填 ConditionalSpatialPath.div_base，不将散度交换留作输入。 -/
theorem hasDerivAt_jet_divergence (D : Rect) (X Y : SmoothTimeJet)
    (hX : UniformTimeJet D X) (hY : UniformTimeJet D Y) (t : ℝ) :
    HasDerivAt (fun s => SmoothField.toL2 D (X.value s).derivativeX +
      SmoothField.toL2 D (Y.value s).derivativeY)
      (SmoothField.toL2 D (X.first t).derivativeX +
       SmoothField.toL2 D (Y.first t).derivativeY) t :=
  (hasDerivAt_jet_gradientX D X hX t).add (hasDerivAt_jet_gradientY D Y hY t)

/-- 三层实际普通 L² 路径连续；restrict 到 [0,T] 即为后续闭区间接口。
第三分量尤其提供 P_tt 的时间可积性所需连续性。 -/
theorem continuous_jet_L2 (D : Rect) (J : SmoothTimeJet)
    (hregular : UniformTimeJet D J) :
    Continuous (fun t => SmoothField.toL2 D (J.value t)) ∧
    Continuous (fun t => SmoothField.toL2 D (J.first t)) ∧
    Continuous (fun t => SmoothField.toL2 D (J.second t)) := by
  have pass (F : ℝ → SmoothField)
      (hF : Continuous (fun t => restrictContinuous D (F t))) :
      Continuous (fun t => SmoothField.toL2 D (F t)) := by
    simpa only [Function.comp_def, continuousToL2_restrict] using (continuousToL2 D).continuous.comp hF
  exact ⟨pass _ hregular.continuous_value, pass _ hregular.continuous_first,
    pass _ hregular.continuous_second⟩

end LeanPML.Rectangle
