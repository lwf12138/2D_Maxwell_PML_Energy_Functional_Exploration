# v0.5 最终文档与假设检查

时间：2026-10-14T01:35:00.583666+08:00。root 与独立 geometry 代理实际逐段读过主入口/报告和新增清单。

- 主结构实际19字段：参数与对象、原式、边界、初值及强正则性；输出包与输入包分开。没有Green/Poincare/耗散/单调等目标输入。
- history_regular包括八个原场时间连续，实际u历史联合光滑；UniformTimeJet和WeightedJetRegular区别已经报告列明。
- 一般定理保留更强正则性；具体实例由构造证明成员与导数，不将非零数据说成一般存在性。
- 报告、源码与日志619/683/740一致，最后全工程覆盖全部。
- 保守CP2Lx、K/c*一致；profile正式名称已纠正为LeanPML.Examples.FullDomain.profile，mathlib平坦函数来源同为SmoothTransition.lean。
- README明确导数/闭合仅内部，闭区间图界/比较包含端点与T0初始兼容。
- 静态例wy3、真正主定理调用；增长例全未来量词、真实积分与不兼容界限准确。单层只针对原候选。
- PDF八页检查通过，6勾+2说明；具体类别、剩余范围和完整声明逐条记账，未给原π/传播/弱范围/存在唯一勾。
- 原20字段人工误数在早期记录后追加更正，不覆盖历史；未涉及证明修改。

## 当前记录哈希

- `README.md`：`8f1b557a0f53c7e0cd0aaf208bd774434e2f19a3b990d57cbae08aa9347343b2`
- `PROGRESS.md`：`b61615a2b5c8b64f366bc02da662b6f8c29be1d6d337e295e445f1374867627e`
- `reports/smooth_theorem.md`：`074fcab650e79c47c163f1002861efab41d24e3fb3f1f6ea03296e3cb181628e`
- `docs/source_inventory.md`：`61e47ad9a78ff6aa423d22a01194480232a2ee0c3aa576c8ccc9d53802d0ec65`
- `docs/theorem_inventory.md`：`8d98d4836561d8f50d42d23c51cd9c12729127f4e80fa3235555afeb0de1cc62`
- `docs/claim_ledger.md`：`fd4f0ca24ea44d7ead15c502a67f5c313398ef0874599154d02c5f2f0e68288b`
- `docs/pdf_formalization_marks.md`：`f095b9d58115bb4ef9af7b85102842acf2286ed5cb36f8aa6fb684b72daca8cc`
