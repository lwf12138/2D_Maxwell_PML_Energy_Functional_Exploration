# v1.0.2 本轮部分交付

已证：弱 Green、CP=2Lx 的弱 Poincaré、对应旧受限算子接口、实际图路径坐标求导、(5.7) 固定空间点真实时间积分及零吸收保持。非零回归通过。
未完成：一般零迹逼近、W¹∞ 弱乘积/区域系数总装、(5.8) 加权传播、提升规范唯一性、弱原系统主定理。

准确类型、假设及依赖见 DeclarationTypes.lean 的实际输出和 semantic_review.md；完整说明见 reports/weak_theorem.md。
失败过程保留：首次 API Probe 查询不存在的 Submodule.coe_topologicalClosure；Green 线性映射 RingHom.id 化简/商域相等类型；Poincaré 零迹加法的函数外延化简；时间积分表达的函数乘法/指数因子改写；总导入追加在模块文档之后引起 import 位置错误。均已修复，没有用占位证明绕过。

本目录 acceptance.json 的 partial 是数学阶段状态，engineering_checks_passed 表示当前交付子项已实际验证。未覆盖旧 v1.0.1 acceptance。
