import LeanPML.Rectangle.RegionalCoefficients

/-!
# v0.5 实例复用的常值时间路径

常值只指时间，空间函数可以非零且不均匀。本文件逐项构造实际 HasDerivAt、
C(K) 路径正则性以及加权路径正则性，供 StaticMode 调用，不能把正则性当作空字段。
加权成员仍须从具体空间函数与权重证明；不要求权重全域有界。
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff Topology
open LeanPML.Analysis LeanPML.PML LeanPML.Rectangle
namespace LeanPML.Examples

/-- 固定光滑空间函数的真实常值时间 jet：一、二阶时间导数均为零。 -/
def constantJet (f : SmoothField) : SmoothTimeJet where
  value := fun _ => f
  first := fun _ => 0
  second := fun _ => 0
  joint_value := f.contDiff.comp contDiff_snd
  joint_first := contDiff_const
  deriv_value := fun t x => hasDerivAt_const t (f x)
  deriv_first := fun t _ => hasDerivAt_const t (0:ℝ)

/-- 所有普通 C(K) 路径及空间梯度路径均为常值，因此具有实际连续和可微证据。 -/
theorem constantJet_regular (D : Rect) (f : SmoothField) : UniformTimeJet D (constantJet f) := by
  constructor
  all_goals dsimp only [constantJet]
  all_goals first | exact continuous_const | exact differentiable_const _

/-- 零函数在任意权重下平方可积，包括无界权重与零区。 -/
theorem weighted_zero_memLp (D : Rect) (w : (ℝ×ℝ)→ℝ) :
    MemLp (fun X => Real.sqrt (w X)*(0:ℝ)) 2 D.measure := by
  simpa only [mul_zero] using
    D.memLp_of_continuous (f := fun _ : ℝ×ℝ => (0:ℝ)) continuous_const 2

/-- 实际加权空间中零物理函数就是零元素；用于实例的有限图平方计算。 -/
@[simp] theorem weightedOfFunction_zero (D : Rect) (w : (ℝ×ℝ)→ℝ)
    (hmem : MemLp (fun X=>Real.sqrt (w X)*(0:ℝ)) 2 D.measure) :
    weightedOfFunction D.measure w (fun _=>0) hmem = 0 := by
  apply Subtype.ext
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [weightedOfFunction_coe D.measure w (fun _=>0) hmem] with X hX
  simpa only [mul_zero,Pi.zero_apply] using hX

/-- 与函数空间零元记号0对应的同一简化规则。 -/
@[simp] theorem weightedOfFunction_zeroFun (D : Rect) (w : (ℝ×ℝ)→ℝ)
    (hmem : MemLp (fun X=>Real.sqrt (w X)*(0:ℝ)) 2 D.measure) :
    weightedOfFunction D.measure w (0 : (ℝ×ℝ)→ℝ) hmem = 0 :=
  weightedOfFunction_zero D w hmem

/-- 光滑零代表对应的同一规则；保留函数零元与商空间零元的区别。 -/
@[simp] theorem weightedOfFunction_zeroSmooth (D : Rect) (w : (ℝ×ℝ)→ℝ)
    (hmem : MemLp (fun X=>Real.sqrt (w X)*(0:ℝ)) 2 D.measure) :
    weightedOfFunction D.measure w (0 : SmoothField) hmem = 0 :=
  weightedOfFunction_zero D w hmem

/-- 常值加权路径的正则性。唯一实质性成员输入是 √w f∈L²；
时间常值性证明所有连续和可微字段，不重新要求待证导数值。 -/
def constantJet_weightedRegular (D : Rect) (w : (ℝ×ℝ)→ℝ) (f : SmoothField)
    (hweighted : MemLp (fun X => Real.sqrt (w X)*f X) 2 D.measure) :
    WeightedJetRegular D w (constantJet f) where
  mem_value := fun _ => hweighted
  mem_first := fun _ => weighted_zero_memLp D w
  mem_second := fun _ => weighted_zero_memLp D w
  continuous_value := by
    change Continuous (fun _ : ℝ => weightedOfFunction D.measure w f hweighted)
    exact continuous_const
  continuous_first := by
    change Continuous (fun _ : ℝ => weightedOfFunction D.measure w (0 : SmoothField) (weighted_zero_memLp D w))
    exact continuous_const
  differentiable_value := by
    change Differentiable ℝ (fun _ : ℝ => weightedOfFunction D.measure w f hweighted)
    exact differentiable_const _
  differentiable_first := by
    change Differentiable ℝ (fun _ : ℝ => weightedOfFunction D.measure w (0 : SmoothField) (weighted_zero_memLp D w))
    exact differentiable_const _

/-- 一个实际空间快照的常值路径；是否满足原 PDE 在 StaticMode 中另行逐条核验。 -/
def constantStateData (s : SmoothStateCoordinates) : SmoothStateData where
  v := constantJet s.v
  V := constantJet s.V
  R := constantJet s.R
  z := constantJet s.z
  Λx := constantJet s.Λx
  Λy := constantJet s.Λy
  φx := constantJet s.ψx
  φy := constantJet s.ψy

/-- 给定两个加权成员证明，构造全部八槽的实际普通/加权时间正则性。 -/
def constantStateRegular (D : Rect) (C : SpatialAbsorption (ℝ×ℝ))
    (s : SmoothStateCoordinates)
    (hx : MemLp (fun X => Real.sqrt (C.wx X)*s.ψx X) 2 D.measure)
    (hy : MemLp (fun X => Real.sqrt (C.wy X)*s.ψy X) 2 D.measure) :
    SmoothStateRegular D C (constantStateData s) where
  v := constantJet_regular D s.v
  V := constantJet_regular D s.V
  R := constantJet_regular D s.R
  z := constantJet_regular D s.z
  Λx := constantJet_regular D s.Λx
  Λy := constantJet_regular D s.Λy
  φx := constantJet_regular D s.ψx
  φy := constantJet_regular D s.ψy
  weightedX := constantJet_weightedRegular D C.wx s.ψx hx
  weightedY := constantJet_weightedRegular D C.wy s.ψy hy



/-- 常数空间倍乘的真实 x 偏导线性性，供 affineJet 的梯度路径使用。 -/
theorem derivativeX_smul (a : ℝ) (f : SmoothField) :
    (a • f).derivativeX=a • f.derivativeX := by
  apply Subtype.ext
  funext X
  change fderiv ℝ (a • (f : ℝ×ℝ→ℝ)) X (1,0)=a*(fderiv ℝ (f : ℝ×ℝ→ℝ) X (1,0))
  rw [fderiv_const_smul_field]
  rfl

/-- 同一条真实求导规则的 y 分量。 -/
theorem derivativeY_smul (a : ℝ) (f : SmoothField) :
    (a • f).derivativeY=a • f.derivativeY := by
  apply Subtype.ext
  funext X
  change fderiv ℝ (a • (f : ℝ×ℝ→ℝ)) X (0,1)=a*(fderiv ℝ (f : ℝ×ℝ→ℝ) X (0,1))
  rw [fderiv_const_smul_field]
  rfl

/-- 仿射时间延拓 (α+βt)f 的真实 jet；用于初值导数证书，不声称它在区间内满足 PDE。 -/
def affineJet (α β : ℝ) (f : SmoothField) : SmoothTimeJet where
  value := fun t => (α+β*t) • f
  first := fun _ => β • f
  second := fun _ => 0
  joint_value := by
    change ContDiff ℝ ∞ (fun z : ℝ×(ℝ×ℝ) => (α+β*z.1)*f z.2)
    exact (contDiff_const.add (contDiff_const.mul contDiff_fst)).mul
      (f.contDiff.comp contDiff_snd)
  joint_first := by
    change ContDiff ℝ ∞ (fun z : ℝ×(ℝ×ℝ) => β*f z.2)
    exact contDiff_const.mul (f.contDiff.comp contDiff_snd)
  deriv_value := by
    intro t X
    change HasDerivAt (fun s => (α+β*s)*f X) (β*f X) t
    have h := ((hasDerivAt_const t α).add ((hasDerivAt_id t).const_mul β)).mul_const (f X)
    simpa only [mul_one,zero_add,Pi.add_apply,id_eq] using h
  deriv_first := fun t X => hasDerivAt_const t (β*f X)

/-- 仿射路径在 C(K) 中可微；梯度路径使用前面实际偏导的线性性。
这里显式通过连续函数空间求导，不从逐点可导直接跳到 L²。 -/
theorem affineJet_regular (D : Rect) (α β : ℝ) (f : SmoothField) :
    UniformTimeJet D (affineJet α β f) := by
  constructor <;>
    simp only [affineJet,derivativeX_smul,derivativeY_smul,map_smul] <;> fun_prop

end LeanPML.Examples
