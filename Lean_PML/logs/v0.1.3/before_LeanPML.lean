-- 正式导入入口：所有项目证明模块均沿此入口或 Audit 的导入链参与默认构建。
import LeanPML.Tutorial.LocalEnergy
import LeanPML.Time.Monotonicity
import LeanPML.Tutorial.ScalarEnergy
import LeanPML.Debye.ScalarEnergy

/-!
# LeanPML 正式入口

v0.1.2 在标量教学例之后加入 Debye 时间子系统能量耗散及非零显式实例。
真实时间不变量和二维 PML 主定理尚未实现。
-/
