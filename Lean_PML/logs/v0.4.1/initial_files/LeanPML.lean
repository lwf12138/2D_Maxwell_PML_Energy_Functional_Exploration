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
import LeanPML.PML.BalanceAbstract
import LeanPML.PML.PhysicalControl

import LeanPML.PML.GradientControl

import LeanPML.PML.DissipationClosure

import LeanPML.PML.MainAbstract

/-!
# LeanPML 正式入口

v0.2.1 加入固定空间点的系数小量条件、分支权重、有界耗散系数及无界能量权重实例。
v0.2.2 加入电块、极化块的真实局部求导、约束消元及精确系数界。
v0.2.3 加入空间块的真实时间路径、零区兼容保持和点态耗散；不等于实际空间场。
v0.2.4 核验单层特殊初值的负耗散、实际初值积分和第二层分量控制。
v0.3.1 加入实际普通/加权 L²、全域空间积分、同源时间路径与内积能量求导。
v0.3.2 从真实 primitive 演化与明确 Green/交换接口推出条件性两层能量恒等式。
v0.3.3 在显式 Poincaré 与兼容约束下得到图范数双边界、零分离及原状态控制。
v0.3.4 用实际 J 积分与同源辅助演化证明 (9.3)–(9.5)，保留零吸收区。
v0.3.5 在明确分析接口下闭合两类耗散，证明有限闭区间单调性与实际积分平衡。
具体矩形接口、完整原 PDE 对应、两个磁不变量及解存在唯一性仍待后续。
-/
