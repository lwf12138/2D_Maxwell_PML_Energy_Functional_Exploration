-- 正式导入入口：所有项目证明模块均沿此入口或 Audit 的导入链参与默认构建。
import LeanPML.Tutorial.LocalEnergy
import LeanPML.Time.Monotonicity
import LeanPML.Tutorial.ScalarEnergy
import LeanPML.Debye.ScalarEnergy
import LeanPML.Time.Constancy
import LeanPML.PML.TimeInvariants
import LeanPML.PML.Coefficients
import LeanPML.PML.Weights

/-!
# LeanPML 正式入口

v0.2.1 加入固定空间点的系数小量条件、分支权重、有界耗散系数及无界能量权重实例。
两个磁辅助不变量、实际场空间与二维 PML 主定理尚未实现。
-/
