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

/-!
# 正式证明导入入口

v0.4的具体空间与原模型接口、v0.5的光滑兼容先验定理及实例均沿此入口参与默认构建。
Audit保留历次审计；本轮光滑范围明确，后续v1.0才建设完整弱空间与传播/规范接口。
-/
