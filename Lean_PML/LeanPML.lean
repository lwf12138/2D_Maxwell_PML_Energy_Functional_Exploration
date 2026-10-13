-- 正式导入入口：所有项目证明模块均沿此入口或 Audit 的导入链参与默认构建。
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

/-!
# LeanPML 正式入口

v0.2.1 加入固定空间点的系数小量条件、分支权重、有界耗散系数及无界能量权重实例。
v0.2.2 加入电块、极化块的真实局部求导、约束消元及精确系数界。
v0.2.3 加入空间块的真实时间路径、零区兼容保持和点态耗散；不等于实际空间场。
v0.2.4 核验单层特殊初值的负耗散、实际初值积分和第二层分量控制。
v0.3.1 加入实际普通/加权 L²、全域空间积分、同源时间路径与内积能量求导。
两个磁辅助不变量的时间保持、具体弱梯度/零迹、PDE 能量律与二维 PML 主定理尚未实现。
-/
