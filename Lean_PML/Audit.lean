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
