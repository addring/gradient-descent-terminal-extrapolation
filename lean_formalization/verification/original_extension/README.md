# 原定义扩展：正式核验记录

2026-10-15 的[提交前检查](../pre_submission.json)已重新完成完整 `lake build` 和全部 717 条定理的公理审计。当前完整审计结果见[审计摘要](../current_complete/summary.json)和[源码清单](../current_complete/source_manifest.json)。

本目录保留 2026-10-14 的扩展核验：18 条新增定理独立合并编译及逐条公理审计通过，实际工程完整默认 `lake build` 通过，2866 个任务，退出码 0。证明入口为 `PaperFramework/OriginalCritical.lean`。

## 阅读顺序

| 文件 | 用途 |
|---|---|
| [final_summary.json](final_summary.json) | 当前结果、核验范围及关键入口的统一索引 |
| [full_lake_build_status.json](full_lake_build_status.json) | 实际工程完整构建的命令、时间和退出码 |
| [full_lake_build.log](full_lake_build.log) | 完整构建输出及 `Build completed successfully (2866 jobs)` |
| [full_lake_build_source_manifest.json](full_lake_build_source_manifest.json) | 当前源码、构建配置和固定依赖的 SHA-256 |
| [framework_status.json](framework_status.json) | 18 条新增定理的合并编译和公理审计结果、当时的输入哈希 |
| [framework_build.log](framework_build.log) | 18 条公理输出；仅使用 `propext`、`Classical.choice`、`Quot.sound` |
| [CombinedOriginal.lean](CombinedOriginal.lean) | 实际送入独立编译器的完整证明副本，无接口占位 |
| [verification_context.json](verification_context.json) | 固定编译器、依赖、核验方式及导入修复说明 |

## 哈希与审计范围

合并审计后，逐模块构建发现 `OriginalQuadratic.lean` 需要直接导入 `PaperFramework.ProblemAndHuber`，已补齐。声明和证明体已与合并审计副本逐字核对一致；只增加导入。因此原合并审计的文件哈希保持原样，当前源码哈希另存于完整构建清单，避免改写历史证据。

旧版 `../complete_summary.json` 的 699 条定理审计属于初始区间版本。本目录的历史审计覆盖 18 条新增定理。完整工程构建覆盖三个默认目标；2026-10-15 的全库审计另存于 `../current_complete/`，覆盖当前全部 717 条定理。构建任务数与定理数分别记录。

## 复现

在 `lean_formalization/` 中，使用固定 Lean 4.26.0 和 `lake-manifest.json` 的依赖：

```powershell
lake build
lake env lean OriginalAudit.lean
```

`OriginalAudit.lean` 导入实际模块，并列出定义、主定理和全部 18 条定理的公理依赖。仅检查声明类型的 `--interfaces-only` 副本不属于正式证明记录。

## 开发期归档

实时检查日志、接口占位副本、首次失败与中断日志、旧证明草稿和整理前交接文档均保留在项目根目录的 `archive/research/lean_formalization/original_extension/`，不纳入提交包。它们不能替代本目录的正式记录。

