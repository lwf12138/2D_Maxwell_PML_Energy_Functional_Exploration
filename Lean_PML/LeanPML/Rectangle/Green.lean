import LeanPML.Rectangle.Boundary
import LeanPML.PML.BalanceInterfaces
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Topology.ContinuousMap.Ordered

/-!
# v0.4.2：真实矩形四边 Green 公式

对应 V7 (7.5)。先对光滑函数调用 mathlib 的矩形散度定理，
对乘积 fΛ 求导得到体积分与四条外边积分，符号为右+、左−、上+、下−。
随后用 v0.4.1 已证明代表无关的 L² 域和连续边界迹构造原工程的 Green 接口。
边界配对独立定义为四边积分，绝不是能量或 Green 等式的残差。

建议顺序：green_smooth_functions → green_L2 → greenDomain。
这里是全空间 C∞ 延拓在整个矩形上的光滑版本，不是一般弱 H¹–H(div) 理论。
-/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace
open LeanPML.Analysis LeanPML.PML
namespace LeanPML.Rectangle

/-- V7 (7.5) 的实际光滑函数版本。输入仅是函数光滑性及矩形端点顺序。
mathlib 的矩形散度公式应用于 (fX,fY)；乘积求导和已证可积性给出四边 Green。
后面的 L² 商类定理使用它，不重新输入 Green 作为假设。 -/
theorem green_smooth_functions (a b : ℝ × ℝ) (hab : a ≤ b) (f X Y : ℝ × ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    (∫ z in Icc a b, f z * (fderiv ℝ X z (1,0) + fderiv ℝ Y z (0,1))) =
    -(∫ z in Icc a b, fderiv ℝ f z (1,0) * X z) -
      (∫ z in Icc a b, fderiv ℝ f z (0,1) * Y z) +
      (((∫ x in a.1..b.1, f (x,b.2)*Y (x,b.2)) -
       (∫ x in a.1..b.1, f (x,a.2)*Y (x,a.2))) +
       (∫ y in a.2..b.2, f (b.1,y)*X (b.1,y)) -
       (∫ y in a.2..b.2, f (a.1,y)*X (a.1,y))) := by
  have hdf := hf.differentiable (by simp)
  have hdX := hX.differentiable (by simp)
  have hdY := hY.differentiable (by simp)
  have hfx : Continuous (fun z => fderiv ℝ f z (1,0)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfy : Continuous (fun z => fderiv ℝ f z (0,1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hXx : Continuous (fun z => fderiv ℝ X z (1,0)) :=
    (hX.continuous_fderiv (by simp)).clm_apply continuous_const
  have hYy : Continuous (fun z => fderiv ℝ Y z (0,1)) :=
    (hY.continuous_fderiv (by simp)).clm_apply continuous_const
  have hprodX : ContDiff ℝ ∞ (fun z => f z * X z) := hf.mul hX
  have hprodY : ContDiff ℝ ∞ (fun z => f z * Y z) := hf.mul hY
  have hdiv_cont : Continuous (fun z =>
      fderiv ℝ (fun z => f z * X z) z (1,0) +
      fderiv ℝ (fun z => f z * Y z) z (0,1)) :=
    ((hprodX.continuous_fderiv (by simp)).clm_apply continuous_const).add
      ((hprodY.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hgreen := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (fun z => f z*X z) (fun z => f z*Y z)
    (fderiv ℝ (fun z => f z*X z)) (fderiv ℝ (fun z => f z*Y z))
    a b hab hprodX.continuous.continuousOn hprodY.continuous.continuousOn
    (fun z _ => (hprodX.differentiable (by simp) z).hasFDerivAt)
    (fun z _ => (hprodY.differentiable (by simp) z).hasFDerivAt)
    hdiv_cont.integrableOn_Icc
  have hexpand : ∀ z, fderiv ℝ (fun z => f z*X z) z (1,0) +
      fderiv ℝ (fun z => f z*Y z) z (0,1) =
      f z * (fderiv ℝ X z (1,0) + fderiv ℝ Y z (0,1)) +
      fderiv ℝ f z (1,0)*X z + fderiv ℝ f z (0,1)*Y z := by
    intro z
    change fderiv ℝ (f * X) z (1,0) + fderiv ℝ (f * Y) z (0,1) = _
    rw [fderiv_mul (hdf z) (hdX z), fderiv_mul (hdf z) (hdY z)]
    simp only [add_apply, smul_apply,
      smul_eq_mul]
    ring
  simp_rw [hexpand] at hgreen
  have hiMain : Integrable (fun z => f z * (fderiv ℝ X z (1,0) + fderiv ℝ Y z (0,1)))
      (volume.restrict (Icc a b)) := (hf.continuous.mul (hXx.add hYy)).integrableOn_Icc
  have hiX : Integrable (fun z => fderiv ℝ f z (1,0)*X z)
      (volume.restrict (Icc a b)) := (hfx.mul hX.continuous).integrableOn_Icc
  have hiY : Integrable (fun z => fderiv ℝ f z (0,1)*Y z)
      (volume.restrict (Icc a b)) := (hfy.mul hY.continuous).integrableOn_Icc
  have hsum := integral_add (hiMain.add hiX) hiY
  have hsumMain := integral_add hiMain hiX
  simp only [Pi.add_apply] at hsum hsumMain
  rw [hsum, hsumMain] at hgreen
  linarith


/-- 四边配对的单边积积分。连续边界数据先按端点常值延拓到实轴；
在原闭区间上延拓等于原值。每个乘积连续可积，因此积分确实是双线性的。
这是 (7.5) 的辅助构造，原文未单列。 -/
def edgePair (a b : ℝ) (hab : a ≤ b) :
    C(Icc a b,ℝ) →ₗ[ℝ] C(Icc a b,ℝ) →ₗ[ℝ] ℝ where
  toFun u := {
    toFun := fun v => ∫ s in a..b, (u.IccExtend hab s) * (v.IccExtend hab s)
    map_add' := by
      intro v w
      change (∫ s in a..b, (u.IccExtend hab s) * ((v+w).IccExtend hab s)) = _
      have hexpand : ∀ s, u.IccExtend hab s * (v+w).IccExtend hab s =
          u.IccExtend hab s * v.IccExtend hab s + u.IccExtend hab s * w.IccExtend hab s := by
        intro s
        change u _ * (v _ + w _) = _
        exact mul_add _ _ _
      simp_rw [hexpand]
      exact intervalIntegral.integral_add
        (((u.IccExtend hab).continuous.mul (v.IccExtend hab).continuous).intervalIntegrable a b)
        (((u.IccExtend hab).continuous.mul (w.IccExtend hab).continuous).intervalIntegrable a b)
    map_smul' := by
      intro r v
      change (∫ s in a..b, (u.IccExtend hab s) * ((r • v).IccExtend hab s)) = _
      have hexpand : ∀ s, u.IccExtend hab s * (r • v).IccExtend hab s =
          r * (u.IccExtend hab s * v.IccExtend hab s) := by
        intro s
        change u _ * (r * v _) = _
        dsimp [ContinuousMap.IccExtend, Set.IccExtend]
        ring
      simp_rw [hexpand]
      exact intervalIntegral.integral_const_mul _ _ }
  map_add' := by
    intro u v
    ext w
    change (∫ s in a..b, ((u+v).IccExtend hab s) * (w.IccExtend hab s)) = _
    have hexpand : ∀ s, (u+v).IccExtend hab s * w.IccExtend hab s =
        u.IccExtend hab s * w.IccExtend hab s + v.IccExtend hab s * w.IccExtend hab s := by
      intro s
      change (u _ + v _) * w _ = _
      exact add_mul _ _ _
    simp_rw [hexpand]
    exact intervalIntegral.integral_add
      (((u.IccExtend hab).continuous.mul (w.IccExtend hab).continuous).intervalIntegrable a b)
      (((v.IccExtend hab).continuous.mul (w.IccExtend hab).continuous).intervalIntegrable a b)
  map_smul' := by
    intro r u
    ext w
    change (∫ s in a..b, ((r • u).IccExtend hab s) * (w.IccExtend hab s)) = _
    have hexpand : ∀ s, (r • u).IccExtend hab s * w.IccExtend hab s =
        r * (u.IccExtend hab s * w.IccExtend hab s) := by
      intro s
      change (r * u _) * w _ = _
      dsimp [ContinuousMap.IccExtend, Set.IccExtend]
      ring
    simp_rw [hexpand]
    exact intervalIntegral.integral_const_mul _ _

/-- 散度定义域：两个分量都具有光滑代表的实际 L² 通量；不等于全部 L²²。 -/
def fluxDomain (D : Rect) : Submodule ℝ (ScalarL2 D.measure × ScalarL2 D.measure) :=
  (fieldDomain D).prod (fieldDomain D)

/-- 通量的 x 分量仍在光滑梯度域中，后面用其真实 x 导数定义散度。 -/
def fluxX (D : Rect) : fluxDomain D →ₗ[ℝ] fieldDomain D where
  toFun L := ⟨L.val.1, L.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 通量的 y 分量投影。 -/
def fluxY (D : Rect) : fluxDomain D →ₗ[ℝ] fieldDomain D where
  toFun L := ⟨L.val.2, L.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 真实散度为 ∂xΛx+∂yΛy 的 L² 类；代表独立性由 Fields 的偏导结果保证。 -/
def divergence (D : Rect) : fluxDomain D →ₗ[ℝ] ScalarL2 D.measure :=
  (spatialDomain D).componentX.comp (fluxX D) +
    (spatialDomain D).componentY.comp (fluxY D)

/-- 四条边使用对应法向分量：右/左取 Λx，上/下取 Λy。
外法向的正负号在下一条 boundaryPair 中处理。 -/
def normalComponents (D : Rect) : fluxDomain D →ₗ[ℝ] BoundaryData D where
  toFun L := ((trace D (fluxX D L)).1, (trace D (fluxX D L)).2.1,
    (trace D (fluxY D L)).2.2.1, (trace D (fluxY D L)).2.2.2)
  map_add' L M := by simp only [map_add]; rfl
  map_smul' r L := by simp only [map_smul]; rfl

/-- 四条真实边界积分的数值表达，顺序为右−左+上−下。 -/
def boundaryValue (D : Rect) (B N : BoundaryData D) : ℝ :=
  edgePair D.ylo D.yhi D.y_lt.le B.1 N.1 -
  edgePair D.ylo D.yhi D.y_lt.le B.2.1 N.2.1 +
  edgePair D.xlo D.xhi D.x_lt.le B.2.2.1 N.2.2.1 -
  edgePair D.xlo D.xhi D.x_lt.le B.2.2.2 N.2.2.2

/-- V7 (7.5) 的真实四边配对：右−左+上−下。
所有输入都是连续边界数据，单边可积性及双线性已由 edgePair 证明。 -/
def boundaryPair (D : Rect) : BoundaryData D →ₗ[ℝ] BoundaryData D →ₗ[ℝ] ℝ where
  toFun B := {
    toFun := boundaryValue D B
    map_add' N M := by
      simp only [boundaryValue, Prod.fst_add, Prod.snd_add, map_add]
      ring
    map_smul' r N := by
      simp only [boundaryValue, Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]
      ring }
  map_add' B C := by
    apply LinearMap.ext
    intro N
    change boundaryValue D (B+C) N = boundaryValue D B N + boundaryValue D C N
    simp only [boundaryValue, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
    ring
  map_smul' r B := by
    apply LinearMap.ext
    intro N
    change boundaryValue D (r•B) N = r * boundaryValue D B N
    simp only [boundaryValue, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring

/-- 连接独立边界迹与通量法向分量的配对。没有任何能量对象参与定义。 -/
def boundaryForm (D : Rect) : BoundaryData D →ₗ[ℝ] fluxDomain D →ₗ[ℝ] ℝ where
  toFun B := (boundaryPair D B).comp (normalComponents D)
  map_add' B C := by ext L; simp
  map_smul' r B := by ext L; simp

/-- 光滑代表的 L² 内积恰为原实际乘积积分；只在 a.e. 意义替换代表元。 -/
theorem inner_toL2 (D : Rect) (f g : SmoothField) :
    ⟪SmoothField.toL2 D f, SmoothField.toL2 D g⟫_ℝ = ∫ z, f z*g z ∂D.measure := by
  rw [Analysis.inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [SmoothField.coe_toL2 D f, SmoothField.coe_toL2 D g] with z hf hg
  rw [hf,hg]

/-- 普通 L² 平方范数与代表平方的空间积分一致，Poincaré 使用该对应。 -/
theorem norm_toL2_sq (D : Rect) (f : SmoothField) :
    ‖SmoothField.toL2 D f‖^2 = ∫ z, (f z)^2 ∂D.measure := by
  rw [Analysis.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [SmoothField.coe_toL2 D f] with z hf
  rw [hf]

/-- 单边连续延拓积分与实际函数边界积分相同。
这里只在原区间上比较，端点以外延拓如何选择不影响积分。 -/
theorem edgePair_eq_integral (a b : ℝ) (hab : a ≤ b)
    (B N : C(Icc a b,ℝ)) (f g : ℝ → ℝ)
    (hB : ∀ x (hx : x ∈ Icc a b), B ⟨x,hx⟩ = f x)
    (hN : ∀ x (hx : x ∈ Icc a b), N ⟨x,hx⟩ = g x) :
    edgePair a b hab B N = ∫ x in a..b, f x*g x := by
  change (∫ x in a..b, B.IccExtend hab x * N.IccExtend hab x) = _
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  simp only [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem hab _ hx, hB x hx, hN x hx]

/-- 四边边界配对在光滑代表上展开为右−左+上−下的原文积分。
这是检查法向方向的定理，不是把边界定义成体积分残差。 -/
theorem boundaryForm_smooth (D : Rect) (f X Y : SmoothField) :
    boundaryForm D (smoothTrace D f)
      ⟨(SmoothField.toL2 D X, SmoothField.toL2 D Y), ⟨⟨X,rfl⟩,⟨Y,rfl⟩⟩⟩ =
      ((∫ y in D.ylo..D.yhi, f (D.xhi,y)*X (D.xhi,y)) -
       (∫ y in D.ylo..D.yhi, f (D.xlo,y)*X (D.xlo,y))) +
      ((∫ x in D.xlo..D.xhi, f (x,D.yhi)*Y (x,D.yhi)) -
       (∫ x in D.xlo..D.xhi, f (x,D.ylo)*Y (x,D.ylo))) := by
  change boundaryPair D (smoothTrace D f)
    ((trace D ⟨SmoothField.toL2 D X, ⟨X,rfl⟩⟩).1,
     (trace D ⟨SmoothField.toL2 D X, ⟨X,rfl⟩⟩).2.1,
     (trace D ⟨SmoothField.toL2 D Y, ⟨Y,rfl⟩⟩).2.2.1,
     (trace D ⟨SmoothField.toL2 D Y, ⟨Y,rfl⟩⟩).2.2.2) = _
  rw [trace_toL2, trace_toL2]
  change edgePair _ _ _ (smoothTrace D f).1 (smoothTrace D X).1 -
      edgePair _ _ _ (smoothTrace D f).2.1 (smoothTrace D X).2.1 +
      edgePair _ _ _ (smoothTrace D f).2.2.1 (smoothTrace D Y).2.2.1 -
      edgePair _ _ _ (smoothTrace D f).2.2.2 (smoothTrace D Y).2.2.2 = _
  rw [edgePair_eq_integral _ _ _ _ _ (fun y => f (D.xhi,y)) (fun y => X (D.xhi,y))
      (fun _ _ => rfl) (fun _ _ => rfl),
    edgePair_eq_integral _ _ _ _ _ (fun y => f (D.xlo,y)) (fun y => X (D.xlo,y))
      (fun _ _ => rfl) (fun _ _ => rfl),
    edgePair_eq_integral _ _ _ _ _ (fun x => f (x,D.yhi)) (fun x => Y (x,D.yhi))
      (fun _ _ => rfl) (fun _ _ => rfl),
    edgePair_eq_integral _ _ _ _ _ (fun x => f (x,D.ylo)) (fun x => Y (x,D.ylo))
      (fun _ _ => rfl) (fun _ _ => rfl)]
  ring

/-- V7 (7.5) 在实际 L² 商类上的矩形光滑 Green。
所有体积分先由连续性证明可积；代表选择无关由 Fields/Boundary 兑现。
调用者只给受限域内的场，不提供 hGreen。 -/
theorem green_L2 (D : Rect) (U : fieldDomain D) (L : fluxDomain D) :
    ⟪(U : ScalarL2 D.measure), divergence D L⟫_ℝ =
      -⟪(spatialDomain D).componentX U, (L : ScalarL2 D.measure × ScalarL2 D.measure).1⟫_ℝ -
       ⟪(spatialDomain D).componentY U, (L : ScalarL2 D.measure × ScalarL2 D.measure).2⟫_ℝ +
       boundaryForm D (trace D U) L := by
  rcases U with ⟨_,f,rfl⟩
  obtain ⟨X,hX⟩ := L.property.1
  obtain ⟨Y,hY⟩ := L.property.2
  have hL : L = ⟨(SmoothField.toL2 D X, SmoothField.toL2 D Y),
      ⟨⟨X,rfl⟩,⟨Y,rfl⟩⟩⟩ := by
    apply Subtype.ext
    exact Prod.ext hX.symm hY.symm
  rw [hL]
  change ⟪SmoothField.toL2 D f,
      (spatialDomain D).componentX ⟨SmoothField.toL2 D X,⟨X,rfl⟩⟩ +
      (spatialDomain D).componentY ⟨SmoothField.toL2 D Y,⟨Y,rfl⟩⟩⟫_ℝ = _
  erw [componentX_toL2, componentY_toL2, componentX_toL2, componentY_toL2,
    trace_toL2, boundaryForm_smooth, inner_add_right, inner_toL2, inner_toL2,
    inner_toL2, inner_toL2]
  have hraw := green_smooth_functions (D.xlo,D.ylo) (D.xhi,D.yhi)
    ⟨D.x_lt.le,D.y_lt.le⟩ f X Y f.contDiff X.contDiff Y.contDiff
  have hiX : Integrable (fun z => f z * dx X z) D.measure :=
    D.integrable_of_continuous (f.continuous.mul X.derivativeX.continuous)
  have hiY : Integrable (fun z => f z * dy Y z) D.measure :=
    D.integrable_of_continuous (f.continuous.mul Y.derivativeY.continuous)
  have hsum : (∫ z, f z*(dx X z+dy Y z) ∂D.measure) =
      (∫ z, f z*dx X z ∂D.measure) + ∫ z, f z*dy Y z ∂D.measure := by
    simp_rw [mul_add]
    exact integral_add hiX hiY
  rw [D.measure_eq_closed, D.closedSet_eq_Icc] at hsum ⊢
  change (∫ z in Icc (D.xlo,D.ylo) (D.xhi,D.yhi), f z*dx X z) +
      (∫ z in Icc (D.xlo,D.ylo) (D.xhi,D.yhi), f z*dy Y z) = _
  rw [← hsum]
  dsimp [dx,dy] at ⊢
  linarith

/-- 用上条已证 Green 填入旧抽象接口。构造没有 hGreen 参数；
梯度、散度、迹与独立四边配对均来自具体光滑矩形。 -/
def greenDomain (D : Rect) : ConditionalGreenDomain D.measure (BoundaryData D) where
  spatial := spatialDomain D
  fluxDomain := fluxDomain D
  divergence := divergence D
  trace := trace D
  boundary := boundaryForm D
  green := green_L2 D

/-- 实际零迹使四边配对消失，供两层乘子逐层调用。 -/
theorem boundary_zero (D : Rect) (U : fieldDomain D) (L : fluxDomain D)
    (htrace : trace D U = 0) : boundaryForm D (trace D U) L = 0 := by
  rw [htrace,map_zero]
  rfl

/-- 两层能量乘子 V+cv 的边界消失：必须分别输入 v、V 的四边零迹。
这是已证矩形 Green 域的调用，不再要求抽象 Green 假设。 -/
theorem boundary_multiplier_zero (D : Rect) (c : ℝ) (v V : fieldDomain D)
    (L : fluxDomain D) (hv : trace D v = 0) (hV : trace D V = 0) :
    boundaryForm D (trace D (V+c•v)) L = 0 := by
  exact boundary_multiplier_zero_Conditional (greenDomain D) c v V L hv hV

/-- 光滑标量场进入真实梯度域的规范入口；保留实际 L² 值。 -/
def fieldOfSmooth (D : Rect) : SmoothField →ₗ[ℝ] fieldDomain D :=
  (SmoothField.toL2 D).rangeRestrict

/-- 两个光滑通量分量进入实际散度域，不引入任何散度关系假设。 -/
def fluxOfSmooth (D : Rect) (X Y : SmoothField) : fluxDomain D :=
  ⟨(SmoothField.toL2 D X,SmoothField.toL2 D Y),⟨⟨X,rfl⟩,⟨Y,rfl⟩⟩⟩

/-- 规范光滑通量的实际散度正是两条真实偏导的 L² 和。 -/
theorem divergence_ofSmooth (D : Rect) (X Y : SmoothField) :
    divergence D (fluxOfSmooth D X Y) =
      SmoothField.toL2 D X.derivativeX + SmoothField.toL2 D Y.derivativeY := by
  change (spatialDomain D).componentX ⟨SmoothField.toL2 D X,⟨X,rfl⟩⟩ +
    (spatialDomain D).componentY ⟨SmoothField.toL2 D Y,⟨Y,rfl⟩⟩ = _
  rw [componentX_toL2,componentY_toL2]

/-- 非零零边界泡函数对自身梯度的真实 Green 调用。
输出 ⟨f,Δf⟩=−‖f_x‖²−‖f_y‖²，验证域和边界配对均非空实现。
它只测试空间算子，不声称泡函数满足 PML 演化。 -/
theorem rectangleBubble_green (D : Rect) :
    let f := rectangleBubble D
    ⟪SmoothField.toL2 D f,
      divergence D (fluxOfSmooth D f.derivativeX f.derivativeY)⟫_ℝ =
      -‖SmoothField.toL2 D f.derivativeX‖^2 - ‖SmoothField.toL2 D f.derivativeY‖^2 := by
  dsimp only
  have htrace : trace D (fieldOfSmooth D (rectangleBubble D)) = 0 := by
    erw [trace_toL2]
    exact (smoothTrace_eq_zero_iff D _).mpr (rectangleBubble_zeroBoundary D)
  have hgreen := green_L2 D (fieldOfSmooth D (rectangleBubble D))
    (fluxOfSmooth D (rectangleBubble D).derivativeX (rectangleBubble D).derivativeY)
  rw [boundary_zero D _ _ htrace, add_zero] at hgreen
  change ⟪SmoothField.toL2 D (rectangleBubble D), _⟫_ℝ = _ at hgreen
  erw [componentX_toL2,componentY_toL2] at hgreen
  simpa only [fluxOfSmooth,real_inner_self_eq_norm_sq] using hgreen

end LeanPML.Rectangle
