-- 正式导入入口：所有项目证明模块均沿此入口或 Audit 的导入链参与默认构建。
import LeanPML.Tutorial.LocalEnergy
import LeanPML.Time.Monotonicity
import LeanPML.Tutorial.ScalarEnergy
import LeanPML.Debye.ScalarEnergy
import LeanPML.Time.Constancy
import LeanPML.PML.TimeInvariants

/-!
# LeanPML 正式入口

v0.1.3 加入固定空间点的三个真实时间不变量、初始兼容保持及非零实例。
两个磁辅助不变量、实际场空间与二维 PML 主定理尚未实现。
-/
