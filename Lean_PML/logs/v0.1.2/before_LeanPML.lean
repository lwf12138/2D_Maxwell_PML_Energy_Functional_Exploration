-- 正式导入入口：五个项目模块均沿此入口或 Audit 的导入链参与默认构建。
import LeanPML.Tutorial.LocalEnergy
import LeanPML.Time.Monotonicity
import LeanPML.Tutorial.ScalarEnergy

/-!
# LeanPML 正式入口

v0.1.1 已实现标量能量的有限区间单调性与初值界，以及负耗散参数对照例。
Debye 子系统和二维 PML 主定理尚未实现。
-/
