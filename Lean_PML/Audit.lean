-- 从正式入口导入，审计实际交付的全部项目定理。
import LeanPML

/-!
# 公理依赖审计

#print axioms 列出定理传递依赖的公理，输出随默认构建和独立审计留档。
标准基础原则并非未完成证明；不应出现证明占位公理。
同时必须阅读定理类型，核对没有把目标能量符号、单调性或初值界当作输入。
-/

-- v0.0.3：真实函数的局部求导。
#print axioms LeanPML.Tutorial.hasDerivAt_energy
-- v0.1.1：一般时间引理与单点退化情形。
#print axioms LeanPML.Time.antitoneOn_Icc_of_hasDerivAt_nonpos
#print axioms LeanPML.Time.antitoneOn_Icc_self
-- v0.1.1：原方程 → 能量性质 → 时间单调性 → 初值界。
#print axioms LeanPML.Tutorial.energy_nonneg
#print axioms LeanPML.Tutorial.continuousOn_energy
#print axioms LeanPML.Tutorial.hasDerivAt_energy_on_Ioo
#print axioms LeanPML.Tutorial.energy_deriv_nonpos
#print axioms LeanPML.Tutorial.antitoneOn_energy_zero
#print axioms LeanPML.Tutorial.antitoneOn_energy
#print axioms LeanPML.Tutorial.energy_bounds
-- v0.1.1：修改耗散参数假设后的可编译对照例。
#print axioms LeanPML.Tutorial.exp_solves_negative_damping
#print axioms LeanPML.Tutorial.negative_damping_counterexample

-- v0.1.2：Debye 真求导、耗散、区间估计及非零显式实例。
#print axioms LeanPML.Debye.energy_nonneg
#print axioms LeanPML.Debye.continuousOn_energy
#print axioms LeanPML.Debye.hasDerivAt_energy_of_hasDerivAt
#print axioms LeanPML.Debye.hasDerivAt_energy_rate
#print axioms LeanPML.Debye.dissipation_eq_rate
#print axioms LeanPML.Debye.hasDerivAt_energy_dissipation
#print axioms LeanPML.Debye.dissipation_nonneg
#print axioms LeanPML.Debye.energy_deriv_nonpos
#print axioms LeanPML.Debye.hasDerivAt_energy_on_Ioo
#print axioms LeanPML.Debye.antitoneOn_energy_zero
#print axioms LeanPML.Debye.antitoneOn_energy
#print axioms LeanPML.Debye.energy_bounds
#print axioms LeanPML.Debye.hasDerivAt_exampleE
#print axioms LeanPML.Debye.hasDerivAt_exampleP
#print axioms LeanPML.Debye.continuous_exampleE
#print axioms LeanPML.Debye.continuous_exampleP
#print axioms LeanPML.Debye.example_ode
#print axioms LeanPML.Debye.example_initial
#print axioms LeanPML.Debye.example_energy_antitone
#print axioms LeanPML.Debye.example_energy_bounds

-- v0.1.3：时间常值接口、三个不变量、初始兼容、零吸收与非零实例。
#print axioms LeanPML.Time.eq_initial_on_Icc_zero
#print axioms LeanPML.Time.eq_initial_of_hasDerivAt_zero
#print axioms LeanPML.PML.hasDerivAt_CD_zero
#print axioms LeanPML.PML.hasDerivAt_CZ1_zero
#print axioms LeanPML.PML.hasDerivAt_CZ2_zero
#print axioms LeanPML.PML.continuousOn_CD
#print axioms LeanPML.PML.continuousOn_CZ1
#print axioms LeanPML.PML.continuousOn_CZ2
#print axioms LeanPML.PML.CD_eq_initial
#print axioms LeanPML.PML.CZ1_eq_initial
#print axioms LeanPML.PML.CZ2_eq_initial
#print axioms LeanPML.PML.CD_compatibility
#print axioms LeanPML.PML.CZ1_compatibility
#print axioms LeanPML.PML.CZ2_compatibility
#print axioms LeanPML.PML.Z1_eq_initial_of_zero_absorption
#print axioms LeanPML.PML.Z2_eq_initial_of_zero_absorption
#print axioms LeanPML.PML.Z1_zero_of_zero_absorption
#print axioms LeanPML.PML.Z2_zero_of_zero_absorption
#print axioms LeanPML.PML.hasDerivAt_exampleU
#print axioms LeanPML.PML.hasDerivAt_exampleQ
#print axioms LeanPML.PML.hasDerivAt_exampleZ1
#print axioms LeanPML.PML.hasDerivAt_exampleZ2
#print axioms LeanPML.PML.example_continuous
#print axioms LeanPML.PML.example_polarization
#print axioms LeanPML.PML.example_initial_compatibility
#print axioms LeanPML.PML.example_nonzero_initial
#print axioms LeanPML.PML.example_compatibility_on_Icc

-- v0.2.1：系数阈值双向等价、退化分支、权重界与无界族。
#print axioms LeanPML.PML.materialA_pos
#print axioms LeanPML.PML.scaleK_pos
#print axioms LeanPML.PML.threshold_pos
#print axioms LeanPML.PML.le_inv_sqrt_iff
#print axioms LeanPML.PML.le_threshold_iff_explicit
#print axioms LeanPML.PML.absorptionSum_nonneg
#print axioms LeanPML.PML.absorptionProduct_nonneg
#print axioms LeanPML.PML.absorptionSum_eq_zero_iff
#print axioms LeanPML.PML.absorptionSum_le_half
#print axioms LeanPML.PML.absorptionProduct_le_sum_sq_quarter
#print axioms LeanPML.PML.absorptionProduct_le_c_sq_sixteenth
#print axioms LeanPML.PML.absorptionSum_mul_sub_product_nonneg
#print axioms LeanPML.PML.c_mul_tau_le_material_bound
#print axioms LeanPML.PML.material_bound_lt_sixteenth
#print axioms LeanPML.PML.c_mul_tau_bounds
#print axioms LeanPML.PML.scale_mul_amplitude_sq_le_sixteenth
#print axioms LeanPML.PML.unit_material_smallness_example
#print axioms LeanPML.PML.weights_of_sum_zero
#print axioms LeanPML.PML.energyWeights_lower_bound
#print axioms LeanPML.PML.theta_partition
#print axioms LeanPML.PML.dissipationPlus_bounds
#print axioms LeanPML.PML.dissipationPlus_le_five_quarters
#print axioms LeanPML.PML.dissipationMinus_bounds
#print axioms LeanPML.PML.zero_absorption_example
#print axioms LeanPML.PML.x_layer_example
#print axioms LeanPML.PML.y_layer_example
#print axioms LeanPML.PML.corner_example
#print axioms LeanPML.PML.family_denominator_pos
#print axioms LeanPML.PML.vanishingAbsorption_bounds
#print axioms LeanPML.PML.vanishingAbsorption_eventually_small
#print axioms LeanPML.PML.energyWeights_on_family
#print axioms LeanPML.PML.energyWeights_unbounded

-- v0.2.2：代数辅助、真实求导、约束消元、四组系数界和非零路径实例。
#print axioms LeanPML.PML.electric_rate_identity
#print axioms LeanPML.PML.hasDerivAt_electricEnergyAlong
#print axioms LeanPML.PML.deriv_exampleU
#print axioms LeanPML.PML.hasDerivAt_deriv_exampleU
#print axioms LeanPML.PML.hasDerivAt_electricEnergyAlong_exampleU
#print axioms LeanPML.PML.deriv_exampleU_zero
#print axioms LeanPML.PML.polar_constraint_derivative
#print axioms LeanPML.PML.polar_shifted_constraint
#print axioms LeanPML.PML.polar_rate_algebra
#print axioms LeanPML.PML.hasDerivAt_polarQuadratic
#print axioms LeanPML.PML.hasDerivAt_polarEnergy
#print axioms LeanPML.PML.hasDerivAt_polarEnergy_on_Ioo
#print axioms LeanPML.PML.polarQuadratic_eq_reduced
#print axioms LeanPML.PML.polarEnergy_eq_reduced
#print axioms LeanPML.PML.polar_coefficients_bounds_of_local_conditions
#print axioms LeanPML.PML.polar_coefficients_bounds_of_threshold
#print axioms LeanPML.PML.example_polar_path_compatible
#print axioms LeanPML.PML.hasDerivAt_example_polarEnergy
