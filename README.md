# 梯度下降末端外推的临界尺度

*A Sharp Asymptotic Threshold for Terminal Extrapolation of Gradient Descent*

本项目为清华大学 2026 年秋季学期户将老师《人工智能中的优化方法》课程的期中项目。课程要求选取一个有公开出处且经核实尚未解决的问题，利用 AI 探索其证明、反例或求解算法，并对研究结果进行独立核验。

我们选择研究 Luner 与 Grimmer 在 *On Averaging and Extrapolation for Gradient Descent*（[arXiv 第四版](https://arxiv.org/abs/2402.12493v4)，Conjecture 5.1）中提出的猜想：在光滑凸优化中，以末端外推点的最坏梯度范数为指标，固定步长梯度下降的临界外推参数增量是否为 $\Theta(N^{-1})$。仓库收录研究论文、Lean 形式化证明代码及 Python 精确检查程序。

## Luner–Grimmer Conjecture 5.1 — Computational and Lean-Formalized Investigation

This project investigates Conjecture 5.1 in *On Averaging and Extrapolation for Gradient Descent* by Alan Luner and Benjamin Grimmer (arXiv:2402.12493).

The project claims to refute the conjectured Theta(1/N) critical scale and proposes the sharper asymptotic 1/(hN sqrt(log N)). It provides a mathematical write-up, Lean 4 formalization, and verification scripts.

**Status:** Independent project; not peer-reviewed. Independent verification is welcome.

## 研究问题

设 $L,D>0$，$f:\mathbb{R}^d\to\mathbb{R}$ 为凸可微函数，梯度的 Lipschitz 常数不超过 $L$，且存在极小点 $x^\star$ 满足 $\|x_0-x^\star\|\le D$。考虑固定步长梯度下降

$$
x_{k+1}=x_k-\frac{h}{L}\nabla f(x_k),\qquad 0<h\le1,
$$

以及 $N$ 次迭代后的外推点

$$
y_N(c)=x_0+c(x_N-x_0),\qquad c\ge1.
$$

记 $P_{N,h}(c;L,D)$ 为所有有限维数及上述问题实例上 $\|\nabla f(y_N(c))\|$ 的上确界。我们研究等式

$$
P_{N,h}(c;L,D)=\frac{LD}{1+Nhc}
$$

成立的参数集合。定义

$$
c_{\mathrm{crit}}(N,h)
=\sup\left\lbrace
c\ge 1:\quad
P_{N,h}(c;L,D)=\frac{LD}{1+Nhc}
\right\rbrace.
$$

由缩放可知，该临界参数与 $L,D$ 无关。

## 主要结果与方法

对每个固定的 $h\in(0,1]$，有

$$
\lim_{N\to\infty}hN\sqrt{\log N}\,\bigl(c_{\mathrm{crit}}(N,h)-1\bigr)=1.
$$

具体而言，对任意 $\varepsilon\in(0,1)$，存在 $N_0=N_0(h,\varepsilon)$，使得对所有 $N\ge N_0$ 和 $L,D>0$，上述性能等式在整个区间

$$
1\le c\le1+\frac{1-\varepsilon}{hN\sqrt{\log N}}
$$

上成立；而对于每个

$$
c\ge1+\frac{1+\varepsilon}{hN\sqrt{\log N}},
$$

均存在维数至多为二、初始半径恰为 $D$ 的光滑凸实例，其输出梯度范数严格大于 $LD/(1+Nhc)$。这两部分夹逼等式集合的上确界，得到上述极限。

Luner–Grimmer 在其论文 arXiv 第四版的 Conjecture 5.1 中提出 $c_{\mathrm{crit}}-1=\Theta(N^{-1})$。本项目证明 $N(c_{\mathrm{crit}}-1)\to0$，从而否定该猜想，参见[原文](https://arxiv.org/abs/2402.12493v4)。

证明分为三个环节：

- **插值证书与二次规划。** 利用光滑凸插值条件，将性能上界归结为一个约束二次规划，并从其 KKT 条件构造非负有向流及相应的插值证书。
- **能量估计。** 通过尾和变换得到三对角能量表达式，建立辅助目标的下界。试验向量的参考能量通过与显式倒数模型比较，归结为两个调和和，确定临界尺度中的 $\sqrt{\log N}$ 因子。
- **光滑凸反例。** 从严格可行的负方向构造有限插值数据，再通过凸共轭得到二维光滑凸函数。紧区间上一致的能量与末端项估计、无界尾部的一维二次函数，共同给出所有上侧参数的严格失效。

论文采用了形式化过程中得到的整体能量比较证明，具体推导见附录 B。

## 证明与核验

[论文](main.pdf) 给出完整数学论证。[Lean 主定理](lean_formalization/PaperFramework/OriginalCritical.lean) `original_sharp_critical_scale` 对所有 $L,D>0$ 和每个固定 $h\in(0,1]$ 证明上述极限，代码中的 `originalCriticalCoefficient` 对应 $c_{\mathrm{crit}}$。

完整工程于 2026 年 10 月 15 日重新构建通过（2866 项任务）。随后对当前全部 717 条定理完成公理审计，无证明占位或 `sorryAx`，公理依赖限于 `propext`、`Classical.choice` 和 `Quot.sound`。构建日志、审计结果和源码哈希见[提交前检查记录](lean_formalization/verification/pre_submission.json)；此前的分次审计记录单独保留。

Python 程序以有理数运算检查选定实例中的证书、KKT 条件、能量恒等式和二维反例，并提供渐近推导相关公式的计算检查。一般性的数学结论由论文和 Lean 证明给出。

| 内容 | 入口 |
|---|---|
| 研究论文 | [main.pdf](main.pdf) |
| Lean 工程与证明对应表 | [工程说明](lean_formalization/README.md) · [证明对应表](lean_formalization/PROOF_MAP.md) |
| 主定理依赖链 | [依赖说明](lean_formalization/ORIGINAL_PROOF_MAP.md) |
| 编译、公理审计与源码哈希 | [核验索引](lean_formalization/verification/original_extension/README.md) · [核验汇总](lean_formalization/verification/original_extension/final_summary.json) |
| Python 精确检查 | [运行说明](verification/README.md) |

## 仓库结构与复现

```text
.
├── README.md
├── main.pdf                # 研究论文
├── lean_formalization/     # Lean 源码、固定依赖与审计记录
├── verification/           # Python 检查程序、固定输入与结果快照
└── scripts/                # 统一检查与打包入口
```

在项目根目录执行 Python 检查，仅需 Python 3 标准库；已在 Python 3.12 下验证：

```shell
python scripts/verify.py
```

该命令依次运行三组检查，日志写入 `build/verification/`，新生成的独立检查结果写入 `verification/results/`。

Lean 使用 `leanprover/lean4:v4.26.0`，mathlib 及传递依赖由 `lake-manifest.json` 固定。安装 elan 后，在项目根目录运行：

```powershell
Set-Location lean_formalization
lake exe cache get
lake build
lake env lean OriginalAudit.lean
```

全项目逐定理公理审计可在 Lean 工程目录运行 `pwsh -File check_complete.ps1`。结果写入 `verification/current_complete/`，不覆盖历史审计记录。


## AI 使用说明

AI 工具参与了问题探索、证明思路生成、推导整理、Python 与 Lean 代码编写，以及文本修订。数值检查和形式化过程中发现的问题用于修正论证，形式化也促成了能量估计证明的简化。

## 参考文献

Alan Luner and Benjamin Grimmer, *On Averaging and Extrapolation for Gradient Descent*.
[arXiv:2402.12493v4](https://arxiv.org/abs/2402.12493v4) · [DOI:10.1287/moor.2024.0449](https://doi.org/10.1287/moor.2024.0449).
