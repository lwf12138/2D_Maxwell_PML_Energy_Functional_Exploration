# v0.5 端点时间正则性：文档对齐记录

用途：区分一般闭区间时间引理的最小输入与当前具体光滑解类采用的更强技术延拓。本轮只改报告和追加进度记录，不改证明、结构、参数或任何PDF。

## 核对结果与调用链

- `SmoothPaths.lean:24–31` 的 `SmoothTimeJet` 在全轴有联合 C∞，`deriv_value/deriv_first` 均为 `∀ t x, HasDerivAt ... t`，包括0和T。`UniformTimeJet` 全轴一致范数可微，以及 `StatePaths.lean:35–55` 的加权可微条件，进一步提供实际L²/加权导数。
- `MainSmoothRectangle.lean:26–47` 的 `SmoothCompatibleSolution` 输入这些真实路径与正则性，`problem` 调用 `RegionalAbsorption.originalRegionalFiniteIntervalProblem`；没有额外输入端点原方程或目标能量导数公式。
- `OriginalSystem.lean:73–75` 的 `OriginalOn` 只要求 `(0,T)×Ω`；技术延拓可导不意味着域外/端点PDE被要求。`energy_law_and_closure` 也仅以 `t∈Ioo 0 T` 交付。
- `SmoothCompatibleSolution.energy_antitone` → `MainAbstract.energy7_antitoneOn_Conditional`（333–341）→ `Time.antitoneOn_Icc_of_hasDerivAt_nonpos`（32起）：闭区间连续、内部导数及内部非正符号。
- `SmoothCompatibleSolution.energy_integral_balance` → `MainAbstract.energy7_integral_balance_Conditional`（248–268）→ `integral_balance_of_hasDerivAt`（120–127）→ mathlib `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`（1142起）：闭区间连续、内部导数和区间可积性，无端点导数输入。
- 所以闭区间结论含端点、一般推理不需要端点导数，与当前具体定理的技术输入已含端点双侧可导性可以同时成立。更弱的时间入口尚未在当前具体主定理中实现；这是范围说明，非新增证明结论。

## 必要修改及保留范围

- `reports/smooth_theorem.md:85`：仅改原含混句；$T=0$原说明逐字保留（现第87行）。
- `PROGRESS.md:3`：新增一段本轮说明，其余全文与历史逐字保留。
- README当前段没有直接同类错误，所以未改；历史“时间延拓”行保留。
- `Time/Monotonicity.lean` 和 `MainAbstract.lean` 的一般引理说明正确，未作机械替换。旧PROGRESS、定理清单、结论账本、PDF账本及v0.2指南的相关句子属于正确的一般接口/历史范围，全部保留。
- 本轮没有需要修复证明的发现；数学定理、签名和正则性输入均未改变。

## 修改前后

修改前：

> 相同时刻与两个端点包含在结论中，不要求端点普通双侧导数。

修改后：

> 相同时刻与两个端点包含在结论中。闭区间比较与积分平衡的时间引理不额外要求端点处的 PDE 或能量导数公式；当前具体定理采用的光滑延拓本身仍包含端点普通双侧可导性：`SmoothTimeJet` 在全时间轴上要求联合光滑性及 `HasDerivAt` 证据。更弱的时间正则性入口尚未在该具体主定理中实现。

## 哈希、检查与既有证据

- `reports/smooth_theorem.md`
  - 修改前：`074fcab650e79c47c163f1002861efab41d24e3fb3f1f6ea03296e3cb181628e`
  - 修改后：`62e4ec5a370e7fee96fd73dea84b9e008c1fcc7170e19dc2a3f73189bb62d44c`
- `PROGRESS.md`
  - 修改前：`b61615a2b5c8b64f366bc02da662b6f8c29be1d6d337e295e445f1374867627e`
  - 修改后：`220c51873bcb76e87792866e9805c076bc36fe6a1664bac762c0c6382d04760e`

核对 58 份正式Lean源码（含导入与审计入口），与v0.5.3快照全部一致。锁定配置、合同、路线图、原论文和指定PDF哈希未变。实际diff只有上述两项说明修订，见 [changes.diff](changes.diff)；细项与源码哈希见 [record.json](record.json)，修改前备份及核对基线保存在本目录。

**本轮没有运行 `lake build` 或公理审计。** 引用既有v0.5.3成功记录：

- [原整体验收](../overall_acceptance.json)；旧源码与文档哈希不改写。
- [既有完整构建](../20261014T011533_485975_lake_build.log)，退出0。
- [既有740项公理审计](../20261014T011752_801259_axioms_audit.log)，退出0。

旧验收中的报告/进度文档哈希现在是**此次修订前的历史版本**，不是新文档哈希；此次前后对应单独记在本目录，不覆盖旧acceptance。本轮只是文档对齐，不推进下一阶段、不更新依赖、不提交或推送。
