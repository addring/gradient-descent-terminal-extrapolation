# 论文到 Lean 的定理对应表

依据：正式英文稿、中文复核稿、第 31 轮修正记录。
下列 PaperFramework 模块的完整证明均已接回，主定理及全部上游链已通过编译与最终独立全库公理审计。
“组合”指用已证明的上游定理连接；最终全部项目定理均无 sorryAx。

| 英文稿位置 | PaperFramework 模块 | 主要定理入口 |
|---|---|---|
| §1，(1.1)–(1.5) | Definitions、InstanceBounds、FunctionDilation、InstanceDilation、SmoothnessNormalization、WorstScaling、ProblemAndHuber | 实际实例值集合非空有界、实际轨迹尺度变换和最坏梯度上确界缩放均已独立审计；huber_attainment 的常梯度恢复实现已编译、独立审计并接入主入口，轨迹外延拓的方法变化已单独记录 |
| §2，(2.1) | FirstOrderConvex、SmoothDescent、FullConjugatePotential、FullRecoveredInterpolation、Interpolation | 必要性及一般有限插值充分性已编译并独立审计；一般构造保留完整函数值截距，证明全局光滑性及全部值/梯度匹配 |
| §1，半径等号嵌入 | RadiusCoordinates、RadiusInstance、ProblemAndHuber | 实际 d+1 维全局函数、精确初始化半径和所有 N,h,c 下的输出梯度范数保持均已编译、独立审计并接入原命题 |
| §2，(2.2)–(2.7) | ForwardFlowAlgebra、FlowQuadratic、FlowVectorQuadratic、FlowTrajectory、FlowSlackAlgebra、FlowIdentityProof、ForwardCertificate | 完整 forward_flow_identity_proved 已编译、独立审计并接回原入口；保留任意有限维实例、实际输出梯度、全部 slack 与末端项 |
| §3，(3.3) | TailTransform | tail_transform_recovery、tail_transform_injective 已证明 |
| §3，(3.4)–(3.5) | TailEnergyIdentities、TridiagonalQuadratic、EnergyIdentity | tridiagonal_energy_identity 已证明，含末端边界与离散分部求和 |
| §3，(3.6)–(3.8) | TridiagonalStructure、MatrixPositivity、CorrectionMatrix | 完整矩阵分裂、修正矩阵正性、energy_matrix_domination 已证明 |
| §3，(3.9) | ObjectiveEnergy、ChainMatrix、Energy、RelativeConvexity | 目标能量恒等式、链矩阵表达、零和正性、c=1 正定性及相对严格凸性已证明 |
| §3，辅助值定义 | QPValue | auxiliaryValue_attained 已证明；以给定优化器为假设，未替代优化器存在性 |
| §3，QP 存在性证明 | QPGeometry、QPUniform、QPSlater、QPExistence | 可行集紧性与凸性、严格可行扰动、optimizer_exists_unique 已证明 |
| §3，(3.10) | QuadraticVariation、FiniteQPFirstOrder、FarkasMultipliers、FiniteQPKKT、QPLinearConstraints、QuadraticProgramKKT | 一阶必要条件、非负乘子、原约束等价表示及 complete_kkt_exists 已证明；保留两组完整乘子 |
| §4，(4.1)–(4.2) | FeasiblePositivity | feasibilityGap_adjacent、slope_gap_adjacent、feasible_gap_positive、feasible_terminal_positive、feasible_coordinates_positive 已证明 |
| §4，严格次序的准备 | KKTOrderPreparation | 常值块内部斜率乘子为零、终端差分乘子为零及 finite_discrete_maximum 已证明 |
| §4，(4.3) | TransposeIdentities、KKTCoordinates | kkt_coordinate_balance、kkt_adjacent_balance 已证明，保留完整差分乘子及左侧零边界 |
| §4，(4.4) | SlopeCurvature、KKTStrictOrder | 零差分处的严格曲率、支撑最大值原理、optimizer_strict_order、difference_multipliers_vanish 已证明 |
| §5，行矩归一化 | RowMomentNormalization | row_moments_sum 已证明，只需望远镜求和 |
| §5，行矩正性 | KKTRowPositivity | kkt_row_moments_positive、row_moments_positive_normalized 已证明，不依赖流量概率非负性或端点界 |
| §5，(5.2)、(5.5) | PlateauRecurrences、FiniteIntervalSums、PlateauSums、NonterminalPlateau、TerminalPlateauSums、TerminalPlateau、OrderAndPlateaus | 两类端点界已证明并通过独立审计，保留辅助值为零的边界 |
| §6，(6.1)–(6.7) | FlowProbabilities、FlowConservation、FlowMoments、FlowMatrixAction、FlowSlopeAction、FlowSignRecurrence、FlowTransport、FlowEntrySums、FlowOffDiagonal、ProductFlow | 概率、平衡、行矩、矩阵核、非对角符号与矩阵非负性均已证明并通过审计 |
| §6，(6.8) | Sufficiency | qp_sufficiency，组合流量证书 |
| §7，(7.1)–(7.5) | FeasibleFloor、NormalizedEnergyBound、ShiftedEnergy、EnergyLowerBound | 可行坐标下限、仿射平移、全空间能量下界与 qp_energy_lower_bound 已证明，末端修正项完整保留 |
| §8 | TrialBasics、TrialSlopeScalar、TrialRightScalar、TrialFunctional、TrialProfiles、TrialDirection | trial_strict_feasibility 已整体编译通过，按文档两端分别估计再合并 |
| §9 | TrialNormalization、TrialBaseline、TrialMajorant、TrialPerturbationAlgebra、TrialPerturbationProfiles、TrialUniformLimitProof、TrialAsymptotics | baseline 正性/支配、归一化、J 精确恒等式、单调尾和及末端界已独立审计；一致极限的归一化组合已证明，真实参考能量主项已由 TrialReferenceEnergyError、TrialReferenceModelLimit 完整编译并接回，独立审计已通过；一致参数扰动已完整编译接入，新增公理审计已通过 |
| §10 | ReferenceRatio、ScaledParameters、UniformSigns、UniformLimit | 缩放坐标及条件极限的符号后果已编译；UniformAuxiliaryProof 与 TrialScaledLimitProof 已完整证明并接回两个缩放一致极限，完整主入口编译已通过 |
| §11，(11.1)–(11.5) | NegativeAlgebra、VecTwo、NegativeRadius、NegativeSmall、NegativePolynomial、NegativeLocalSlacks、NegativeLeading、NegativeBackward、NegativeSlackSigns、NegativeAllSlacks、NegativeData | 递推、slack 多项式及半径展开/严格改善已编译；相邻及特殊源节点约束已编译并审计；全部有向约束已通过编译并替换原占位；有限数据组合已通过独立公理审计 |
| §11，(11.6) | ConjugateBasics、ConjugatePotential、ConjugateGrowth、ConjugateExistence、RecoveredSmoothness、RecoveredInterpolation、PerturbationRecovery、PerturbationTrajectory、InstanceDilation、NegativeInstance、GlobalRealization | 全局优化器存在唯一性、恢复函数光滑性、特殊插值、实际轨迹、缩放和 negative_direction_realization_proved 均已通过编译及独立公理审计 |
| §11，负辅助值的严格扰动 | QPStrictNegative | negative_optimizer_has_strict_negative_direction 已证明 |
| §12 | FiniteLowerAtOne、InitialInterval、PositiveQuadraticContinuity、ChainContinuity、CriticalInterval | 最终纯区间极限已证明；h=1 有限下界已编译并审计，逐函数衔接及近 c=1 的有限区间衔接已通过编译；正定性邻域、链流量合法性、实际二次函数大系数失败均已独立审计；上游链已全部完成，完整夹逼与主定理编译已通过；最终全库独立审计已通过 |
| 主定理 (1.4) | Main | sharp_critical_scale、main_theorem，组合区间夹逼 |

基础库 `CriticalExtrapolation` 已证明的 40 条定理包括修正权重、倒数和对数渐近、
有限求和、一般平方和非负性、流量支持以及逐函数轨道连续性。
完整清单见 `AxiomAudit.lean`；框架逐定理的占位清单见
`verification/framework_obligations.json`。
能量与严格凸性子链的 68 条定理见 `EnergyAudit.lean`。
`tridiagonal_energy_identity`、`homogeneousEnergy_positive`、`objective_positive_on_zero_sum`、
`chain_at_one_positive` 和 `relative_strict_convexity` 均已补全证明并纳入无占位审计范围。
QP、完整 KKT、严格次序、平段端点及流量子链的 198 条定理见 `QPAudit.lean`。负值扰动结论给出严格可行负方向；它随后通过独立审计的第 11 节链实现为实际二维全局函数反例。

## 必须保留的语义

- 实际函数在任意有限维 `EuclideanSpace ℝ (Fin d)` 上全局凸、可微，梯度 L-Lipschitz，有极小点与初始半径约束。
- 输出 y 与末端 x_N 分开，q 是输出梯度。
- `criticalCoefficient` 是整个 [1,C] 的实际最坏值等式区间端点，未定义成 QP 根。
- 只有 N 个斜率分量、N−1 个相邻比较，无终端零斜率条件。
- 正流量边仅约束 i 到 j−1 的斜率。
- 原始权重采用已修正公式；倒数误差取绝对值；支配常数为 3。
- 主极限固定 h；未扩展为 h 随 N 趋零的一致命题。
- h=1 的下界先逐函数取步长极限，再取实例上确界。


假设修正与证明方法重组单独记录在 FORMALIZATION_NOTES.md。扩展解析审计的实际成功范围以 verification/analytic_summary.json 为准，编译状态以 STATUS.md 为准。
