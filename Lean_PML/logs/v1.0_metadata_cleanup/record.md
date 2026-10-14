# v1.0 发布标识与注释整理

用途：记录两个小范围整理及修改后的实际验证；不覆盖 `v1.0_finalization` 的历史验收。

- `LeanPML/PML/WeakCanonicalTime.lean`：更新 `main_energy` 及相邻区域入口注释，说明底层使用代表、一般弱系数代表已由后续模块证明并接入最终入口。
- `lakefile.toml`：仅将本项目包版本从 `0.0.3` 改为 `1.0.0`。Lean 工具链、mathlib 提交和依赖锁文件保持不变。
- README 顶部增加本记录入口，区分旧验收快照与当前源码。

去除注释后的 Lean 源码与原成功验收版本完全一致；没有修改数学定义、假设或证明。旧快照中的 122 个文件只有上述 Lean 注释文件和 Lake 配置发生变化，新哈希见 `source_snapshot.json`，逐项前后哈希见 `verification.json`。

## 实际验证

- `lake_build`：退出码 0；[完整输出](20261014T193430_072456_lake_build.log)；[命令、工作目录和退出码](20261014T193430_072456_lake_build.json)。
- `axioms_audit`：退出码 0；[完整输出](20261014T193529_928767_axioms_audit.log)；[命令、工作目录和退出码](20261014T193529_928767_axioms_audit.json)。

公理审计共 1058 次输出、1050 个不同声明；仅出现 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。构建保留了既有 linter 提示；未作无关重构。

本轮重新运行本地默认构建和完整审计，没有重新进行隔离构建或 PDF 编辑/视觉验收；原隔离记录只作为修改前基线保留。原 PDF、模型合同、路线图与历史验证记录均未修改。没有提交或推送远端。

工程根目录下复现：

```bash
python3 scripts/run_logged.py --stage v1.0_metadata_cleanup lake_build lake build
python3 scripts/run_logged.py --stage v1.0_metadata_cleanup axioms_audit lake env lean Audit.lean
```
