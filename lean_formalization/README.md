# Lean 形式化工程

本工程形式化梯度下降末端外推的最坏梯度范数及临界尺度。当前论文的入口为 [OriginalExtension.lean](OriginalExtension.lean)，主定理位于 [PaperFramework/OriginalCritical.lean](PaperFramework/OriginalCritical.lean)。

## 定义与主定理

命名空间：`CriticalExtrapolation.Paper`。

| 名称 | 含义 |
|---|---|
| `originalCriticalCoefficient` | 论文 c_crit：最坏梯度范数等于 Huber 界的参数集合上确界 |
| `original_sharp_critical_scale` | 对固定 h∈(0,1]，hN√log N (c_crit−1)→1 |
| `original_critical_increment_small` | N(c_crit−1)→0 |
| `original_conjecture_5_1_false` | 在 h=L=D=1 时排除正的 1/N 最终下界 |

库中 `criticalCoefficient` 表示初始精确区间的端点，保留用于既有证明链。论文 c_crit 对应 `originalCriticalCoefficient`。

[PROOF_MAP.md](PROOF_MAP.md) 按当前论文组织代码入口；[ORIGINAL_PROOF_MAP.md](ORIGINAL_PROOF_MAP.md) 给出全右侧估计和上确界结论的依赖链。

## 构建与审计

Lean：`leanprover/lean4:v4.26.0`。mathlib：`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`。传递依赖由 `lake-manifest.json` 固定。

在本目录执行：

```powershell
lake exe cache get
lake build
lake env lean OriginalAudit.lean
```

默认构建目标为 `CriticalExtrapolation`、`PaperFramework` 和 `OriginalExtension`。可用 `pwsh -File check_complete.ps1` 重新生成全项目定理清单并审计公理。

## 已有核验记录

| 范围 | 结果及位置 |
|---|---|
| 当前完整工程构建 | 2026-10-15 通过，2866 个任务，退出码 0；[提交前记录](verification/pre_submission.json) |
| 当前全部 717 条定理 | 2026-10-15 公理审计通过；[审计结果](verification/current_complete/summary.json) |
| 历史完整工程构建 | 2026-10-14 通过；`verification/original_extension/full_lake_build_status.json` |
| 原定义结果的 18 条定理 | 独立合并编译与公理审计通过；`verification/original_extension/framework_status.json` |
| 既有库的 699 条定理 | 历史审计；`verification/complete_summary.json` |

当前全库审计仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。`check_complete.ps1` 将结果写入 `verification/current_complete/`；此前的 699 条与 18 条定理审计分别保留。各次核验范围见[核验索引](verification/original_extension/README.md)。

当前 Lean 源码、审计脚本及构建配置的哈希见[源码清单](verification/current_complete/source_manifest.json)。

## 维护资料

`STATUS.md`、`FRAMEWORK.md` 和 `FORMALIZATION_NOTES.md` 保留开发与语义审计记录。逐模块检查脚本和审计入口保留在原位置。开发草稿及旧日志归档于项目根目录 `archive/research/lean_formalization/`。
