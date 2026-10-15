# 当前论文与 Lean 对应表

本表对应 [当前论文](../main.pdf) 的章节结构。模块均位于 `PaperFramework/`，主定理入口为 `OriginalExtension.lean`。论文与 Lean 采用各自适合的引理分解；下表按数学内容列出代码入口。

| 论文内容 | 模块入口 |
|---|---|
| §2：函数类、轨迹、最坏梯度、缩放与 Huber 下界 | `Definitions`、`InstanceBounds`、`WorstScaling`、`ProblemAndHuber` |
| §2：c_crit 定义 | `OriginalCritical` 中的 `originalCriticalCoefficient` |
| §3：插值不等式、流恒等式与证书 | `Interpolation`、`FlowIdentityProof`、`ForwardCertificate`、`Sufficiency` |
| §4：尾和变换、三对角能量与正性 | `TailTransform`、`EnergyIdentity`、`TridiagonalStructure`、`CorrectionMatrix` |
| §4：辅助规划的适定性 | `QPGeometry`、`QPSlater`、`QPExistence`、`RelativeConvexity` |
| §4：平移恒等式与能量下界 | `FeasibleFloor`、`NormalizedEnergyBound`、`ShiftedEnergy`、`EnergyLowerBound` |
| §4：下侧精确性与 h=1 | `UniformSigns`、`FiniteLowerAtOne`、`CriticalInterval` |
| §5：负方向、有限插值数据、全局二维函数 | `NegativeData`、`PerturbationRecovery`、`NegativeInstance`、`GlobalRealization` |
| §6：全参数严格可行性 | `OriginalFeasibility` |
| §6：紧区间上一致能量上界 | `OriginalEnergy` |
| §6：末端项与统一负目标 | `OriginalObjective` |
| §6：二次函数尾部 | `OriginalQuadratic` |
| §6–7：整个右侧失效、上确界夹逼与主极限 | `OriginalCritical` |
| 附录 A：KKT、严格次序、行矩、流及半正定性 | `QuadraticProgramKKT`、`KKTStrictOrder`、`OrderAndPlateaus`、`ProductFlow`、`Sufficiency` |
| 附录 B：参考能量、归一化与加权和 | `TrialReferenceEnergyError`、`TrialReferenceModelLimit`、`TrialNormalization`、`TrialWeightedSum`、`TrialAsymptotics` |
| 附录 C：局部过渡律 | `UniformAuxiliaryProof`、`TrialScaledLimitProof`、`UniformLimit` |

## 主结论

- `original_eventual_upper_failure_fixed_step`：存在最终统一的 N 阈值，使所有 c≥c_+ 严格失效。
- `original_critical_sandwich`：c_−≤c_crit≤c_+。
- `original_sharp_critical_scale`：hN√log N (c_crit−1)→1。
- `original_critical_increment_small`：N(c_crit−1)→0。
- `original_conjecture_5_1_false`：否定猜想的正逆线性下界。

精确声明见 [OriginalAudit.lean](OriginalAudit.lean)，全右侧估计依赖链见 [ORIGINAL_PROOF_MAP.md](ORIGINAL_PROOF_MAP.md)，核验材料见 [核验索引](verification/original_extension/README.md)。

## 主问题的语义核对（2026-10-15）

核对对象为论文第 2 节的定义、定理 2.1 和推论 2.2，以及 `OriginalExtension` 导出的声明。主极限所涉及的问题一致。

| 数学对象或量词 | Lean 对应及核对结果 |
|---|---|
| 全局光滑凸函数、存在极小点、初始距离不超过 D | `CriticalExtrapolation/Problem.lean` 的 `Instance`；凸性和梯度 Lipschitz 条件均在整个欧氏空间上成立 |
| N 次梯度下降，步长 h/L，输出 x₀+c(x_N−x₀) | `iterate`、`output`；性能指标是输出处的梯度范数 |
| 对所有有限维实际函数实例取上确界 | `worstGradient`；`InstanceBounds` 证明取值集合非空、有界 |
| c_crit 是全部等式成立点的上确界 | `originalValiditySet`、`originalCriticalCoefficient`；最终主定理使用此定义 |
| 固定 0<h≤1，下侧整个区间精确 | `eventual_lower_interval_fixed_step`；包含 h=1，阈值先于 c 选取 |
| 上侧所有 c≥c₊ 严格失效 | `original_eventual_upper_failure_fixed_step`；负方向覆盖有界部分，二次函数覆盖无界尾部 |
| hN√log N(c_crit−1)→1 | `original_sharp_critical_scale`；仅假设 L,D>0 和 0<h≤1 |
| N(c_crit−1)→0 及猜想的否定 | `original_critical_increment_small` 对所有固定 h 成立；`original_conjecture_5_1_false` 取 h=L=D=1，排除正的逆线性下界 |

有三处表达方式需要区分：

- 论文令 d≥1，Lean 允许 d=0。零维空间只贡献梯度范数 0；一维常函数已经贡献同一个值，因此上确界不变。
- Lean 的区间和失效定理先固定 L,D。由 `worstGradient_scaling_proved` 的恒等式 P(c;L,D)=LD·P(c;1,1)，可先在 L=D=1 选取 N₀，再用于所有 L,D>0。这给出论文中 N₀(h,ε) 的量词次序，也说明 c_crit 与 L,D 无关。
- `negative_direction_realization_proved` 显式返回二维实例；尾部证明使用一维二次函数。反例定理的类型只要求距离≤D，但具体构造满足距离=D：前者将半径 R>0 的实例按 D/R 缩放，后者将单位向量按 D 缩放。这个等式目前未作为单独的导出定理声明。

旧的 `criticalCoefficient` 表示初始有效区间的端点，仍保留在基础库中；当前论文主定理对应 `originalCriticalCoefficient`，两者没有在最终声明中混用。

随后进行的提交前检查重新运行了完整 `lake build`（2866 jobs，退出码 0）及当前全部 717 条定理的公理审计，均于 2026-10-15 通过。仅修订审计脚本，Lean 数学证明未改动；历史审计证据保持原样。本次记录见[提交前检查](verification/pre_submission.json)。上述语义核对是对声明和具体构造的人工数学检查，区别于编译与公理审计。

旧稿节号对应表保存在 `archive/article_revisions/20261015_project_cleanup/lean_formalization/PROOF_MAP.md`。
