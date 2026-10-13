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

/-!
# 正式证明导入入口

v0.4.1–v0.4.4 的具体光滑矩形、真实历史与原系统接口沿此入口参与默认构建。
Audit 保留历次公理审计。下一阶段 v0.5 才发布具体主定理；本文件不改变数学范围。
-/
