# Critical Extrapolation：Lean 形式化工程

主定理及其完整证明链已完成。全部核心证明接回后的完整构建通过，随后单独完整构建与全库公理审计再次通过：699 条项目定理无证明占位、无 sorryAx，公理依赖仅为 propext、Classical.choice、Quot.sound。
原论文及 Python 检查器未改写，数值实验不作为 Lean 证明。最终核验记录见 STATUS.md 和 verification/complete_summary.json。

## 目标与主定理

| 目标 | 用途 | 当前证明状态 |
|---|---|---|
| CriticalExtrapolation | 真实问题定义与 40 条基础定理 | 已证明并审计 |
| PaperFramework | 论文证明链与 659 条定理（含辅助引理） | 已证明并审计 |

入口是 PaperFramework/Main.lean 的 CriticalExtrapolation.Paper.sharp_critical_scale：对 L,D>0 和每个固定 h∈(0,1]，证明 hN√(log N)(criticalCoefficient N h L D−1)→1。
main_theorem 的类型就是基础库 MainTheoremStatement。定义保留任意有限维全局光滑凸函数类、实际 GD 轨迹、外推输出梯度和整个 [1,C] 有效区间；没有添加 QP 非负性假设。
整段下界、单点严格失败和实际二维全局函数反例也已证明。实际编译类型及定义输出见 verification/main_statement_audit.txt。

## 独立核验

check_complete.ps1 对两库的全部源定理建立清单，完整构建后逐条运行 #print axioms，并校验实际名字、数量和公理白名单。它同时拒绝证明占位、自定义 axiom、unsafe 与 native_decide。源码和固定依赖的 SHA-256 见 verification/complete_source_manifest.json。

分组记录也已刷新：基础库 40 条，能量子链 12 模块/68 条，QP 子链 39 模块/198 条，解析子链 97 模块/363 条，均仅依赖标准公理。

分组核验另有 verify.ps1、check_energy.ps1、check_qp.ps1、check_analytic.ps1；check_framework.ps1 核验 18 个关键入口并保存逐定理清单及导入图。分组范围与全库范围不同，定理数量包含辅助引理，不能解释为论文主命题数量。

## 固定依赖与复现

- Lean leanprover/lean4:v4.26.0，编译器提交 d8204c9fd894f91bbb2cdfec5912ec8196fd8562。
- mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67。
- lake-manifest.json 固定全部 9 项传递依赖。

```powershell
lake build
./check_complete.ps1
```

两次完整默认构建均成功（每次 2859 个任务）。编译有不影响证明有效性的 linter 提示。
PROOF_MAP.md 对照论文，FRAMEWORK.md 展示概念依赖主干，FORMALIZATION_NOTES.md 记录语义审计、假设修正及证明方法变化。形式化确认的是明确假设下的主定理及两侧结论；没有扩展到 h 随 N 趋零的一致估计、二阶修正或有限 N 根唯一性。

## 目录整理

`verification/` 保留最终全库审计和主定理类型核对记录。分组检查脚本仍可运行；历史分组输出移至本地 `archive/research/lean_formalization/verification/`（相对于项目根目录）。
