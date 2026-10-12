import LeanPML.PML.LocalElectric
import LeanPML.PML.LocalDebye
import LeanPML.PML.LocalSpatial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# 单层能量不是终点

来源：V7 (6.2)、(7.7) 及 §11.1 的未编号初值/负耗散公式。
§11.1 中“精确导数见 (7.7)”是交叉引用笔误：导数关系是 (7.6)，(7.7) 定义耗散。
本文件按“块组合 → 初值兼容 → 初始导数 → 负耗散 → 实际积分 → 第二层”组织。

ε、κ、τ、μ、c 是时间常参数；p、r 是固定空间点的吸收值，ξ 是 f 在该点的值。
数值导数槽不自带可导性；只有 HasDerivAt 将它连接到真实时间函数。
积分部分使用真实测度与函数，并给出整个矩形上的入口；不构造加权状态空间。
本阶段不证明 PDE 解存在、Green/PEC、一般积分求导或两层耗散闭合。
-/

open MeasureTheory
open scoped Topology

namespace LeanPML.PML.Obstructions

/-- V7 (6.2) 的单层局部密度：μF_e+μF_D+F_sp。
电块已含 ε/2，极化块已含 1/(2κ)，空间块已含 1/2；这里不再重复乘这些因子。
输入都是当前数值。用常值路径把空间块取值接回既有定义，不宣称这些路径满足 PDE。 -/
noncomputable def singleLayerEnergy (ε κ τ μ c p r v vDot R z hx hy lx ly : ℝ) : ℝ :=
  μ * electricEnergy ε (absorptionSum p r) (absorptionProduct p r) c v vDot +
  μ * polarEnergy (absorptionSum p r) (absorptionProduct p r) c κ τ R z +
  spatialEnergy2D c p r (fun _ => hx) (fun _ => hy) (fun _ => lx) (fun _ => ly) 0

/-- V7 (7.7) 的单层耗散密度：μD_e+μD_D+D_sp，尚未作空间积分。
RDot 是导数值槽；a−c 等系数可以为负，名称并不预设耗散非负。
下方初值计算直接调用这三个旧块，不另造一套无关表达式。 -/
noncomputable def singleLayerDissipation
    (ε κ τ μ c p r v vDot R z RDot hx hy lx ly : ℝ) : ℝ :=
  μ * electricRemainder ε (absorptionSum p r) (absorptionProduct p r) c v vDot +
  μ * polarRemainder (absorptionSum p r) (absorptionProduct p r) c κ τ R z RDot +
  spatialDissipation2D c p r hx hy lx ly

/-- §11.1 特殊初值的密度。 取兼容的初始值：填入 u₀=0、E₀=ξ、P₀=κξ、q₀=−τκξ、Pₜ₀=0，
以及 ∇u₀=λ₀=0。Pₜ₀=0 由下方初始方程推出；这里仅命名待计算的表达式。
ξ 是实数；实际空间函数 f 及其支撑条件在积分定理中出现。 -/
noncomputable def initialDissipation (ε κ τ μ c p r ξ : ℝ) : ℝ :=
  singleLayerDissipation ε κ τ μ c p r 0 ξ (κ * ξ) (-τ * κ * ξ) 0 0 0 0 0

/-- §11.1 的支撑条件在一点上的推论：ξ≠0 时 p=r=0，故 aξ=bξ=0。
ξ=0 的点允许任意 p,r；这使后面的计算覆盖整个域，未把全域改成零吸收。
本引理供初始兼容及原方程的初始化简调用。 -/
theorem absorption_mul_initial_zero (p r ξ : ℝ)
    (hsupport : ξ ≠ 0 → p = 0 ∧ r = 0) :
    absorptionSum p r * ξ = 0 ∧ absorptionProduct p r * ξ = 0 := by
  by_cases hξ_zero : ξ = 0
  · simp [hξ_zero]
  · obtain ⟨hp_zero, hr_zero⟩ := hsupport hξ_zero
    simp [hp_zero, hr_zero, absorptionSum, absorptionProduct]

/-- §11.1 初值代入 (2.4)：五个不变量的初始数值都为零。
第一项是 q₀+τP₀=κu₀；中间两项对应 Z₁、Z₂；最后两项用 Q₀=φ₀=0。
hsupport 仅用于 bq₀=0。这里只核验初始代数，不证明磁不变量的时间保持、
λ=旋转磁场的空间对应，或完整兼容函数空间成员资格。 -/
theorem initial_compatibility (ε κ τ p r ξ : ℝ)
    (hsupport : ξ ≠ 0 → p = 0 ∧ r = 0) :
    (-τ * κ * ξ) + τ * (κ * ξ) = κ * 0 ∧
    0 + ε * absorptionProduct p r * 0 = 0 ∧
    0 + absorptionProduct p r * (-τ * κ * ξ) = 0 ∧
    0 - p * 0 = 0 ∧ 0 + r * 0 = 0 := by
  have hbξ_zero : absorptionProduct p r * ξ = 0 :=
    (absorption_mul_initial_zero p r ξ hsupport).2
  refine ⟨by ring, by ring, ?_, by ring, by ring⟩
  calc
    0 + absorptionProduct p r * (-τ * κ * ξ) =
        -τ * κ * (absorptionProduct p r * ξ) := by ring
    _ = 0 := by rw [hbξ_zero]; ring

/-- §11.1，原 (2.1) 在初值处给出 dP=dE=0。
hDebye 是 τdP+κξ=κξ；hElectric 保留原电方程的 aE、aP 项，
仅把 curl H₀、Z₁₀、Z₂₀ 代为零。支撑条件使 aξ=0，才化为 εdE=−dP。
ε≠0、τ≠0 用于乘积消零。这里 dE、dP 只是代数数据；下一条绑定真实函数。 -/
theorem initial_derivative_values (ε κ τ p r ξ dE dP : ℝ)
    (hε_ne : ε ≠ 0) (hτ_ne : τ ≠ 0)
    (hsupport : ξ ≠ 0 → p = 0 ∧ r = 0)
    (hDebye : τ * dP + κ * ξ = κ * ξ)
    (hElectric : ε * dE =
      0 - ε * absorptionSum p r * ξ - dP - absorptionSum p r * (κ * ξ) + 0 + 0) :
    dP = 0 ∧ dE = 0 := by
  have hτdP_zero : τ * dP = 0 := by linarith only [hDebye]
  have hdP_zero : dP = 0 := (mul_eq_zero.mp hτdP_zero).resolve_left hτ_ne
  have haξ_zero : absorptionSum p r * ξ = 0 :=
    (absorption_mul_initial_zero p r ξ hsupport).1
  have hεdE_zero : ε * dE = 0 := by
    -- 用 aξ=0 消去两项吸收；不是向一般 PML 额外添加教学方程。
    calc
      ε * dE = -(ε + κ) * (absorptionSum p r * ξ) - dP := by
        rw [hElectric]
        ring
      _ = 0 := by rw [haξ_zero, hdP_zero]; ring
  exact ⟨hdP_zero, (mul_eq_zero.mp hεdE_zero).resolve_left hε_ne⟩

/-- §11.1 初始导数的真实时间版本：HasDerivAt E dE 0、HasDerivAt P dP 0
把代数槽连接到实际函数，再用原方程初值化简推出两份零导数证据。
hE_initial、hP_initial 只约束初始时刻；未假设全时段兼容或能量律。
普通双侧导数是本局部版本的明确条件；PDE 端点单侧/延拓接口仍待处理。 -/
theorem hasDerivAt_initial_fields_zero (ε κ τ p r ξ dE dP : ℝ)
    (E P : ℝ → ℝ) (hε_ne : ε ≠ 0) (hτ_ne : τ ≠ 0)
    (hsupport : ξ ≠ 0 → p = 0 ∧ r = 0)
    (hE : HasDerivAt E dE 0) (hP : HasDerivAt P dP 0)
    (hE_initial : E 0 = ξ) (hP_initial : P 0 = κ * ξ)
    (hDebye : τ * dP + P 0 = κ * E 0)
    (hElectric : ε * dE =
      0 - ε * absorptionSum p r * E 0 - dP - absorptionSum p r * P 0 + 0 + 0) :
    HasDerivAt P 0 0 ∧ HasDerivAt E 0 0 := by
  have hvalues : dP = 0 ∧ dE = 0 :=
    initial_derivative_values ε κ τ p r ξ dE dP hε_ne hτ_ne hsupport
      (by simpa only [hE_initial, hP_initial] using hDebye)
      (by simpa only [hE_initial, hP_initial] using hElectric)
  exact ⟨hP.congr_deriv hvalues.1, hE.congr_deriv hvalues.2⟩

/-- §11.1 物理区初值的电块贡献：D_e=−εcξ²；没有额外 μ。
纯多项式化简，无正性假设。总耗散计算会再乘 μ。 -/
theorem electricRemainder_initial (ε c ξ : ℝ) :
    electricRemainder ε 0 0 c 0 ξ = -ε * c * ξ ^ 2 := by
  dsimp [electricRemainder]
  ring

/-- §11.1 极化块贡献：D_D=−κcξ²。κ≠0 仅用于消去既有定义中的 κ 分母。
Pₜ₀=0、P₀=κξ、q₀=−τκξ 已填入；本式不是能量求导定理。 -/
theorem polarRemainder_initial (κ τ c ξ : ℝ) (hκ_ne : κ ≠ 0) :
    polarRemainder 0 0 c κ τ (κ * ξ) (-τ * κ * ξ) 0 = -κ * c * ξ ^ 2 := by
  dsimp [polarRemainder]
  -- 分母 κ 已知非零，field_simp 后仅剩多项式等式。
  field_simp [hκ_ne]
  ring

/-- §11.1 的 ∇u₀=λ₀=0 使空间块耗散为零，任意吸收分支均成立。
这是零初始空间数值造成的，不能据此把物理区的一般空间耗散删掉。 -/
theorem spatialDissipation_initial (c p r : ℝ) :
    spatialDissipation2D c p r 0 0 0 0 = 0 := by
  simp [spatialDissipation2D, spatialDissipation]

/-- §11.1 未编号负耗散公式的点态版：
D_initial(ξ)=−μc(ε+κ)ξ²。κ≠0 用于极化分母；hsupport 只限制 ξ≠0 的点。
证明先分 ξ=0 与非零两支，再调用三个旧块的初值结果。正性另在后两条证明。 -/
theorem initialDissipation_eq (ε κ τ μ c p r ξ : ℝ)
    (hκ_ne : κ ≠ 0) (hsupport : ξ ≠ 0 → p = 0 ∧ r = 0) :
    initialDissipation ε κ τ μ c p r ξ = -μ * c * (ε + κ) * ξ ^ 2 := by
  by_cases hξ_zero : ξ = 0
  · simp [hξ_zero, initialDissipation, singleLayerDissipation,
      electricRemainder, polarRemainder, spatialDissipation_initial]
  · obtain ⟨hp_zero, hr_zero⟩ := hsupport hξ_zero
    subst p
    subst r
    -- a=0、b=0 是化简等式，不是 Lean 的定义相等；先显式展开再使用块引理。
    simp only [initialDissipation, singleLayerDissipation, absorptionSum,
      absorptionProduct, zero_add, zero_mul]
    rw [electricRemainder_initial, polarRemainder_initial κ τ c ξ hκ_ne,
      spatialDissipation_initial]
    ring

/-- §11.1 点态符号：ε、κ、μ、c>0 给非负前因子，平方非负使 D_initial≤0。
τ 的正性不参与这一初始值的符号，因此不作多余假设。 -/
theorem initialDissipation_nonpos (ε κ τ μ c p r ξ : ℝ)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ) (hμ_pos : 0 < μ) (hc_pos : 0 < c)
    (hsupport : ξ ≠ 0 → p = 0 ∧ r = 0) :
    initialDissipation ε κ τ μ c p r ξ ≤ 0 := by
  rw [initialDissipation_eq ε κ τ μ c p r ξ hκ_pos.ne' hsupport]
  have hproduct_nonneg : 0 ≤ μ * c * (ε + κ) * ξ ^ 2 := by positivity
  nlinarith only [hproduct_nonneg]

/-- §11.1 的严格点态负性需 ξ≠0，保证 ξ²>0；其余点可为零。
这不是“非零函数必有正平方积分”的空间命题，后者在积分部分另列条件。 -/
theorem initialDissipation_neg (ε κ τ μ c p r ξ : ℝ)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ) (hμ_pos : 0 < μ) (hc_pos : 0 < c)
    (hξ_ne : ξ ≠ 0) (hsupport : ξ ≠ 0 → p = 0 ∧ r = 0) :
    initialDissipation ε κ τ μ c p r ξ < 0 := by
  rw [initialDissipation_eq ε κ τ μ c p r ξ hκ_pos.ne' hsupport]
  have hξ_sq_pos : 0 < ξ ^ 2 := sq_pos_of_ne_zero hξ_ne
  have hproduct_pos : 0 < μ * c * (ε + κ) * ξ ^ 2 := by positivity
  nlinarith only [hproduct_pos]

/-- §11.1 同一物理区初值的能量密度为 μ[ε+κ(1−cτ)]ξ²/2。
直接调用既有三块定义核对 ε、κ、μ、1/2 因子；本式也在 κ=0 时成立，故不另加正性。
此数值公式未声称一般正定性，更没有从能量正性推出单调性。 -/
theorem singleLayerEnergy_initial (ε κ τ μ c ξ : ℝ) :
    singleLayerEnergy ε κ τ μ c 0 0 0 ξ (κ * ξ) (-τ * κ * ξ) 0 0 0 0 =
      μ * (ε + κ * (1 - c * τ)) * ξ ^ 2 / 2 := by
  by_cases hκ_zero : κ = 0
  · subst κ
    simp [singleLayerEnergy, electricEnergy, polarEnergy, spatialEnergy2D,
      absorptionSum, absorptionProduct]
    ring
  · dsimp [singleLayerEnergy, electricEnergy, polarEnergy, polarQuadratic,
      spatialEnergy2D, absorptionSum, absorptionProduct]
    -- 本分支 κ≠0，先消去分母，再展开多项式。
    field_simp
    ring


/-- 将 (6.2) 的块组合放到真实时间路径上；速度槽使用实际 deriv v。
这只是局部密度函数，不是空间积分量。下方初始求导直接复用三个块的求导规则。 -/
noncomputable def singleLayerEnergyAlong (ε κ τ μ c p r : ℝ)
    (v R z hx hy lx ly : ℝ → ℝ) (t : ℝ) : ℝ :=
  singleLayerEnergy ε κ τ μ c p r (v t) (deriv v t) (R t) (z t)
    (hx t) (hy t) (lx t) (ly t)

/-- §11.1 初始能量率的真实局部时间版本，在物理区固定一点证明密度导数为 μc(ε+κ)ξ²。
hv、hvv 将 ξ、0 分别绑定到 v′(0)、v″(0)；hR、hz 绑定 R′(0)=0、z′(0)=κξ。
空间路径初值为零，导数遵守零区辅助演化；兼容仅在初始点由这些初值核验。
这里直接对极化二次型逐项求导，未对单点兼容等式求导，也未假设能量律。
结论属于局部时间路径；不能把它当成 (7.6) 的空间积分求导或 PDE 解存在性。 -/
theorem hasDerivAt_initial_localEnergy (ε κ τ μ c ξ gx gy : ℝ)
    (v R z hx hy lx ly : ℝ → ℝ) (hκ_ne : κ ≠ 0)
    (hv : HasDerivAt v ξ 0) (hvv : HasDerivAt (deriv v) 0 0)
    (hR : HasDerivAt R 0 0) (hz : HasDerivAt z (κ * ξ) 0)
    (hv_initial : v 0 = 0) (hR_initial : R 0 = κ * ξ)
    (hz_initial : z 0 = -τ * κ * ξ)
    (hhx : HasDerivAt hx gx 0) (hhy : HasDerivAt hy gy 0)
    (hlx : HasDerivAt lx gx 0) (hly : HasDerivAt ly gy 0)
    (hx_initial : hx 0 = 0) (hy_initial : hy 0 = 0)
    (lx_initial : lx 0 = 0) (ly_initial : ly 0 = 0) :
    HasDerivAt (singleLayerEnergyAlong ε κ τ μ c 0 0 v R z hx hy lx ly)
      (μ * c * (ε + κ) * ξ ^ 2) 0 := by
  -- 电块：真实一阶、二阶导数进入旧求导定理，然后只改写初始值。
  have helectric : HasDerivAt (electricEnergyAlong ε 0 0 c v)
      (ε * c * ξ ^ 2) 0 := by
    have he := hasDerivAt_electricEnergyAlong ε 0 0 c v 0 ξ 0 hv hvv
    apply he.congr_deriv
    rw [hv_initial, electricRemainder_initial]
    ring
  -- 极化块：用已证 Q 的真实求导，再除以常数 2κ，无需对兼容关系求导。
  have hz_as_R : HasDerivAt z (R 0) 0 := by
    simpa only [hR_initial] using hz
  have hpolar : HasDerivAt (polarEnergyAlong 0 0 c κ τ R z)
      (κ * c * ξ ^ 2) 0 := by
    have hQ := (hasDerivAt_polarQuadratic 0 0 c τ R z 0 0 hR hz_as_R).div_const (2 * κ)
    apply hQ.congr_deriv
    rw [hR_initial, hz_initial]
    -- κ≠0 允许约分；ring 只整理刚刚得到的真实导数值。
    field_simp [hκ_ne]
    ring
  -- 空间块：零区中 l=h=0，辅助演化的吸收项消失；耦合项也因 l₀=0 消失。
  have hspatial : HasDerivAt (spatialEnergy2D c 0 0 hx hy lx ly) 0 0 := by
    have hs := hasDerivAt_spatialEnergy2D c 0 0 hx hy lx ly 0 gx gy
      (le_refl 0) (le_refl 0) hhx (by simpa using hlx)
      hhy (by simpa using hly)
      (fun _ => ⟨by rw [lx_initial, hx_initial], by rw [ly_initial, hy_initial]⟩)
    apply hs.congr_deriv
    rw [hx_initial, hy_initial, lx_initial, ly_initial, spatialDissipation_initial]
    ring
  -- 乘 μ 后相加；函数按定义相同，最后仅合并三个导数值。
  have hsum := ((helectric.const_mul μ).add (hpolar.const_mul μ)).add hspatial
  have hsum_normalized := hsum.congr_deriv
    (show μ * (ε * c * ξ ^ 2) + μ * (κ * c * ξ ^ 2) + 0 =
      μ * c * (ε + κ) * ξ ^ 2 by ring)
  -- 逐时刻展开定义，证明两种写法是同一函数；这提供求导点附近的相等证据。
  apply hsum_normalized.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => by
    simp only [singleLayerEnergyAlong, singleLayerEnergy, electricEnergyAlong,
      polarEnergyAlong, spatialEnergy2D, absorptionSum, absorptionProduct,
      zero_add, zero_mul, Pi.add_apply])

/-- §11.1 的严格初始局部能量率：μc(ε+κ)ξ²>0。
这是上一条真实 HasDerivAt 输出值的符号判断，不是假设完整空间能量律。
完整 PDE 初始增长仍需积分求导、Green/PEC 和经过该数据的解。 -/
theorem initial_localEnergy_rate_pos (ε κ μ c ξ : ℝ)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ) (hμ_pos : 0 < μ) (hc_pos : 0 < c)
    (hξ_ne : ξ ≠ 0) :
    0 < μ * c * (ε + κ) * ξ ^ 2 := by
  have hξ_sq_pos : 0 < ξ ^ 2 := sq_pos_of_ne_zero hξ_ne
  positivity

/-- §11.1 特殊初值的实际积分入口，同时证明密度可积与积分等式。
m 是实际测度，f,p,r 是实际空间函数；h_support 只在 f≠0 处要求零吸收。
h_sq 给平方可积性；filter_upwards 将点态代数用于几乎处处的支撑条件。
这不是任意实数“normSq”，也不涉及一般时间路径的积分求导。 -/
theorem initialDissipation_integral {X : Type*} [MeasurableSpace X]
    (m : Measure X) (f p r : X → ℝ) (ε κ τ μ c : ℝ) (hκ_ne : κ ≠ 0)
    (h_support : ∀ᵐ x ∂m, f x ≠ 0 → p x = 0 ∧ r x = 0)
    (h_sq : Integrable (fun x => (f x) ^ 2) m) :
    Integrable (fun x => initialDissipation ε κ τ μ c (p x) (r x) (f x)) m ∧
    (∫ x, initialDissipation ε κ τ μ c (p x) (r x) (f x) ∂m) =
      -μ * c * (ε + κ) * ∫ x, (f x) ^ 2 ∂m := by
  have hdensity_ae :
      (fun x => initialDissipation ε κ τ μ c (p x) (r x) (f x)) =ᵐ[m]
        (fun x => (-μ * c * (ε + κ)) * (f x) ^ 2) := by
    filter_upwards [h_support] with x hx_support
    exact initialDissipation_eq ε κ τ μ c (p x) (r x) (f x) hκ_ne hx_support
  have hintegrable : Integrable
      (fun x => initialDissipation ε κ τ μ c (p x) (r x) (f x)) m :=
    (h_sq.const_mul (-μ * c * (ε + κ))).congr hdensity_ae.symm
  refine ⟨hintegrable, ?_⟩
  calc
    (∫ x, initialDissipation ε κ τ μ c (p x) (r x) (f x) ∂m)
        = ∫ x, (-μ * c * (ε + κ)) * (f x) ^ 2 ∂m := integral_congr_ae hdensity_ae
    _ = -μ * c * (ε + κ) * ∫ x, (f x) ^ 2 ∂m :=
      integral_const_mul (-μ * c * (ε + κ)) _

/-- §11.1 负耗散的积分符号：严格负性额外要求 ∫f²>0。
一般测度空间的 f≠0 不能替代 h_sq_pos；光滑非零紧支撑函数如何提供此证据尚待空间接口。
ε、κ、μ、c>0 只用于前因子；τ 不影响这次初值计算。 -/
theorem initialDissipation_integral_neg {X : Type*} [MeasurableSpace X]
    (m : Measure X) (f p r : X → ℝ) (ε κ τ μ c : ℝ)
    (hε_pos : 0 < ε) (hκ_pos : 0 < κ) (hμ_pos : 0 < μ) (hc_pos : 0 < c)
    (h_support : ∀ᵐ x ∂m, f x ≠ 0 → p x = 0 ∧ r x = 0)
    (h_sq : Integrable (fun x => (f x) ^ 2) m)
    (h_sq_pos : 0 < ∫ x, (f x) ^ 2 ∂m) :
    (∫ x, initialDissipation ε κ τ μ c (p x) (r x) (f x) ∂m) < 0 := by
  rw [(initialDissipation_integral m f p r ε κ τ μ c hκ_pos.ne' h_support h_sq).2]
  have hmaterial_pos : 0 < μ * c * (ε + κ) :=
    mul_pos (mul_pos hμ_pos hc_pos) (add_pos hε_pos hκ_pos)
  have hproduct_pos : 0 < μ * c * (ε + κ) * (∫ x, (f x) ^ 2 ∂m) :=
    mul_pos hmaterial_pos h_sq_pos
  nlinarith only [hproduct_pos]

/-- §11.1 与论文全域 L² 记号的具体测度入口。
Ω=(x₀,x₁)×(y₀,y₁) 是原文整个开矩形，volume.restrict Ω 是二维 Lebesgue 测度限制。
在平方可积时，∫Ω f² 就是论文 ‖f‖² 的积分表达；这里未构造 Lp 等价类或范数接口。
没有把 Ω 缩成物理区；p,r 在 f=0 处允许非零。上下端点顺序只影响域是否退化，不影响恒等式。 -/
theorem initialDissipation_rectangle_integral
    (x₀ y₀ x₁ y₁ ε κ τ μ c : ℝ) (f p r : ℝ × ℝ → ℝ) (hκ_ne : κ ≠ 0)
    (h_support : ∀ᵐ x ∂(volume.restrict ((Set.Ioo x₀ x₁ ×ˢ Set.Ioo y₀ y₁))),
      f x ≠ 0 → p x = 0 ∧ r x = 0)
    (h_sq : Integrable (fun x => (f x) ^ 2)
      (volume.restrict ((Set.Ioo x₀ x₁ ×ˢ Set.Ioo y₀ y₁)))) :
    Integrable (fun x => initialDissipation ε κ τ μ c (p x) (r x) (f x))
      (volume.restrict ((Set.Ioo x₀ x₁ ×ˢ Set.Ioo y₀ y₁))) ∧
    (∫ x in (Set.Ioo x₀ x₁ ×ˢ Set.Ioo y₀ y₁),
      initialDissipation ε κ τ μ c (p x) (r x) (f x)) =
      -μ * c * (ε + κ) * ∫ x in (Set.Ioo x₀ x₁ ×ˢ Set.Ioo y₀ y₁), (f x) ^ 2 := by
  exact initialDissipation_integral _ f p r ε κ τ μ c hκ_ne h_support h_sq

/-- §11.1 的 λₜ(0)=∇f 在单方向的时间接口。
hl 是 v0.2.3 的真实辅助演化 l′=V+σⱼh−σᵢl；h₀=l₀=0 便推出 l′(0)=V。
V 预期是 ∂ᵢf，但本定理不构造梯度、不证明混合微分交换，也不需要全域零吸收。 -/
theorem hasDerivAt_initial_flux (si sj V : ℝ) (h l : ℝ → ℝ)
    (hh_initial : h 0 = 0) (hl_initial : l 0 = 0)
    (hl : HasDerivAt l (V + sj * h 0 - si * l 0) 0) :
    HasDerivAt l V 0 := by
  simpa only [hh_initial, hl_initial, mul_zero, add_zero, sub_zero] using hl

/-- §11.1 第二层的分量初值密度，复用 (7.2) 的空间块：
h₁=(gₓ,gᵧ)、Λ₁=(gₓ,gᵧ)，所以 ψ₁=0。
gₓ、gᵧ 是数值参数；与真实 ∂ₓf、∂ᵧf 的对应是后续接口。 -/
noncomputable def secondLayerSpatialInitial (c p r gx gy : ℝ) : ℝ :=
  spatialDissipation2D c p r gx gy gx gy

/-- §11.1 物理区分量公式：S₁,initial=c(gₓ²+gᵧ²)。
调用 v0.2.3 零吸收结果，明确保留 c|∇f|² 预期对应项；没有除以吸收系数。 -/
theorem secondLayerSpatialInitial_zero (c gx gy : ℝ) :
    secondLayerSpatialInitial c 0 0 gx gy = c * (gx ^ 2 + gy ^ 2) := by
  exact spatialDissipation2D_of_sum_zero c 0 0 gx gy gx gy
    (by norm_num [absorptionSum])

/-- 将第二层分量计算延伸到全域：非零分量只出现在零吸收处时，仍有同一公式。
这里的支撑条件针对 gₓ、gᵧ，不能由 f 的支撑条件不加证明地替代；
它服务于下方实际分量积分，尚非真实梯度定理。 -/
theorem secondLayerSpatialInitial_eq (c p r gx gy : ℝ)
    (hsupport : gx ≠ 0 ∨ gy ≠ 0 → p = 0 ∧ r = 0) :
    secondLayerSpatialInitial c p r gx gy = c * (gx ^ 2 + gy ^ 2) := by
  by_cases hnonzero : gx ≠ 0 ∨ gy ≠ 0
  · obtain ⟨hp_zero, hr_zero⟩ := hsupport hnonzero
    rw [hp_zero, hr_zero]
    exact secondLayerSpatialInitial_zero c gx gy
  · have hzero : gx = 0 ∧ gy = 0 := by simpa only [not_or, not_not] using hnonzero
    rcases hzero with ⟨rfl, rfl⟩
    simpa only [secondLayerSpatialInitial, zero_pow (by decide : 2 ≠ 0),
      add_zero, mul_zero] using spatialDissipation_initial c p r

/-- §11.1 第二层分量的实际积分：S₁=c(∫gₓ²+∫gᵧ²)。
平方可积性保证能合法拆分和的积分；支撑条件逐点调用上一条分量公式。
这确是实际积分，但没有证明 gₓ、gᵧ 是 f 的梯度，也没有证明 Poincaré。 -/
theorem secondLayerSpatialInitial_integral {X : Type*} [MeasurableSpace X]
    (m : Measure X) (c : ℝ) (p r gx gy : X → ℝ)
    (h_support : ∀ᵐ x ∂m, gx x ≠ 0 ∨ gy x ≠ 0 → p x = 0 ∧ r x = 0)
    (hx_sq : Integrable (fun x => (gx x) ^ 2) m)
    (hy_sq : Integrable (fun x => (gy x) ^ 2) m) :
    Integrable (fun x => secondLayerSpatialInitial c (p x) (r x) (gx x) (gy x)) m ∧
    (∫ x, secondLayerSpatialInitial c (p x) (r x) (gx x) (gy x) ∂m) =
      c * ((∫ x, (gx x) ^ 2 ∂m) + ∫ x, (gy x) ^ 2 ∂m) := by
  have hdensity_ae :
      (fun x => secondLayerSpatialInitial c (p x) (r x) (gx x) (gy x)) =ᵐ[m]
        (fun x => c * ((gx x) ^ 2 + (gy x) ^ 2)) := by
    filter_upwards [h_support] with x hx_support
    exact secondLayerSpatialInitial_eq c (p x) (r x) (gx x) (gy x) hx_support
  have hintegrable := ((hx_sq.add hy_sq).const_mul c).congr hdensity_ae.symm
  refine ⟨hintegrable, ?_⟩
  calc
    (∫ x, secondLayerSpatialInitial c (p x) (r x) (gx x) (gy x) ∂m)
        = ∫ x, c * ((gx x) ^ 2 + (gy x) ^ 2) ∂m := integral_congr_ae hdensity_ae
    _ = c * ∫ x, (gx x) ^ 2 + (gy x) ^ 2 ∂m := integral_const_mul c _
    _ = c * ((∫ x, (gx x) ^ 2 ∂m) + ∫ x, (gy x) ^ 2 ∂m) := by
      rw [integral_add hx_sq hy_sq]


end LeanPML.PML.Obstructions
