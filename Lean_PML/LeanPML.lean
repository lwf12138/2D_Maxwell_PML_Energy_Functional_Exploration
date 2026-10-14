import LeanPML.Examples.GeneralWeakRegression
import LeanPML.PML.MainGeneralWeak
import LeanPML.PML.SeparatedRepresentative
import LeanPML.Analysis.WeakIntervalRepresentative
import LeanPML.Rectangle.OriginalParameterThreshold
import LeanPML.Examples.WeakRepresentative
import LeanPML.PML.WeakCanonicalTime
import LeanPML.Rectangle.SharpPoincare
import LeanPML.Rectangle.SharpParameterCertificate
import LeanPML.PML.MainSharpWeakRectangle
import LeanPML.Examples.SharpWeak
import LeanPML.PML.WeakCkRegularity
import LeanPML.Examples.WeakCk
import LeanPML.Analysis.MultiplierExponential
import LeanPML.PML.AuxiliaryScalarMemory
import LeanPML.Examples.ScalarKernel
import LeanPML.Tutorial.LocalEnergy
import LeanPML.Time.Monotonicity
import LeanPML.Tutorial.ScalarEnergy
import LeanPML.Debye.ScalarEnergy
import LeanPML.Time.Constancy
import LeanPML.PML.TimeInvariants
import LeanPML.PML.Coefficients
import LeanPML.PML.Weights
import LeanPML.PML.LocalElectric
import LeanPML.PML.LocalDebye
import LeanPML.PML.LocalSpatial
import LeanPML.PML.Obstructions.SingleLayer
import LeanPML.PML.EnergyIntegrals
import LeanPML.PML.BalanceAbstract
import LeanPML.PML.PhysicalControl
import LeanPML.PML.GradientControl
import LeanPML.PML.DissipationClosure
import LeanPML.PML.MainAbstract
import LeanPML.Rectangle.Domain
import LeanPML.Rectangle.Fields
import LeanPML.Rectangle.Boundary

-- 正式导入入口：所有项目证明模块均沿此入口或 Audit 的导入链参与默认构建。





import LeanPML.Rectangle.Green
import LeanPML.Rectangle.Poincare

import LeanPML.Rectangle.TimeSpace
import LeanPML.Rectangle.L2Paths
import LeanPML.Rectangle.BoundaryTime
import LeanPML.PML.WeightedCalculus
import LeanPML.Rectangle.SmoothPaths
import LeanPML.Rectangle.StatePaths

import LeanPML.Rectangle.InterfaceAssembly

import LeanPML.Rectangle.HistoryL2
import LeanPML.PML.OriginalSystem
import LeanPML.PML.PrimitiveSystem
import LeanPML.PML.Equivalence
import LeanPML.PML.OriginalAssembly

-- v0.4 对齐：区域物理系数、真实空间可导包装及保守常数参数证书。
import LeanPML.Rectangle.ParameterCertificate
import LeanPML.PML.ClassicalSystem
import LeanPML.Rectangle.RegionalCoefficients


-- v0.5.1：具体原模型的光滑兼容类全域先验定理。
import LeanPML.PML.MainSmoothRectangle

-- v0.5.2：真实C∞剖面、物理区紧支函数与初始图数据。
import LeanPML.Examples.FullDomainProfile
import LeanPML.Examples.CompatibleData

-- v0.5.3：退化入口、非零静态解与完整场增长回归。
import LeanPML.Examples.DegenerateBranches
import LeanPML.Examples.StaticMode
import LeanPML.PML.Obstructions.UnrestrictedData

-- v1.0.1：真实弱导数图、H₀¹ 闭包和退化加权空间的实际算子。
import LeanPML.Analysis.WeightedL2Operators
import LeanPML.Rectangle.WeakSpaces
import LeanPML.Examples.WeakSpaces

-- v1.0.2 已验证子项；不表示弱主定理已经合成。
import LeanPML.Rectangle.WeakGreen
import LeanPML.Rectangle.WeakPoincare
import LeanPML.Rectangle.WeakPaths
import LeanPML.PML.AuxiliaryMemory
import LeanPML.Examples.WeakAnalysis

-- v1.0 数学补齐：图闭包、真实加权成员传播及区域弱乘积。
import LeanPML.Rectangle.SmoothWeakClosure
import LeanPML.PML.WeakCoefficients
import LeanPML.PML.WeakCoefficientExamples
import LeanPML.PML.WeightedForcing
import LeanPML.PML.AuxiliaryWeightedEvolution
import LeanPML.Examples.WeightedEvolution

import LeanPML.Rectangle.WeakDirectionalPoincare
import LeanPML.Analysis.DissipativeMemoryEstimate
import LeanPML.PML.WeightedMemoryBound


-- v1.0 补齐：真实粗糙乘积零迹、规范唯一性及弱原八式历史。
import LeanPML.PML.WeakZeroProduct
import LeanPML.Rectangle.WeakLocality
import LeanPML.PML.SeparatedWeakCoefficients
import LeanPML.PML.LiftUniqueness
import LeanPML.PML.WeakLiftCompatibility
import LeanPML.Time.BanachHistory
import LeanPML.PML.WeakOriginalSystem
import LeanPML.PML.WeakPrimitiveSystem


-- 弱原八式 → 同源路径 → 实际全域先验能量结论。
import LeanPML.PML.WeakPathAssembly
import LeanPML.PML.WeakFiniteProblem
import LeanPML.PML.MainWeakRectangle
import LeanPML.PML.WeakRegionalAbsorption
import LeanPML.PML.WeakCanonicalEnergy
import LeanPML.Examples.WeakObstructionRegression
import LeanPML.Examples.WeakStaticMode
import LeanPML.Examples.WeakBranchRegression

-- v1.0 closeout：实际原场控制、导数连接、八式反向与空间值记忆核。
import LeanPML.PML.WeakV7Regularity
import LeanPML.PML.WeakReverse
import LeanPML.PML.AuxiliaryOperatorMemory
import LeanPML.Examples.WeakCloseout

/-!
# 正式证明导入入口

v0.4的具体空间与原模型接口、v0.5的光滑兼容先验定理及实例均沿此入口参与默认构建。
Audit 保留历次审计；v1.0 新增真实弱图空间、加权传播、规范唯一性及弱原八式主定理。
新版本仍明确保留时间 jet 正则性与保守 Poincaré 常数，不宣称覆盖任意弱解。
-/



