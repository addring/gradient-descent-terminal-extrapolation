# 梯度下降末端外推的临界尺度

*Terminal Extrapolation of Gradient Descent: The Sharp Critical Scale*


本项目为清华大学 2026 年秋季学期户将老师《人工智能中的优化方法》课程的期中项目。课程要求选取一个有公开出处且经核实尚未解决的问题，利用 AI 探索其证明、反例或求解算法，并对研究结果进行独立核验。

我们研究光滑凸优化中固定步长梯度下降的末端外推问题，以外推点处的梯度范数为性能指标，考察临界外推参数的渐近尺度。仓库收录研究论文、Lean 形式化证明代码及 Python 精确检查程序。

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

从 $c=1$ 起连续成立的参数区间。定义

$$
c_{\mathrm{crit}}(N,h)=\sup\left\{C\ge1:\ P_{N,h}(c;L,D)=\frac{LD}{1+Nhc}\ \text{对所有 }c\in[1,C]\right\}.
$$

由缩放可知，该临界参数与 $L,D$ 无关。

## 主要结果与方法

对每个固定的 $h\in(0,1]$，有

$$
\lim_{N\to\infty}hN\sqrt{\log N}\,\bigl(c_{\mathrm{crit}}(N,h)-1\bigr)=1.
$$

具体而言，对任意 $\varepsilon\in(0,1)$，当 $N$ 充分大时，上述性能等式在整个区间

$$
1\le c\le1+\frac{1-\varepsilon}{hN\sqrt{\log N}}
$$

上成立；而在 $c=1+(1+\varepsilon)/(hN\sqrt{\log N})$ 处，存在二维光滑凸函数使等式严格失效。这两部分给出匹配的渐近下界和上界。

Luner–Grimmer 在其论文 arXiv 第四版的 Conjecture 5.1 中提出 $c_{\mathrm{crit}}-1=\Theta(N^{-1})$。本项目得到的对数因子修正了这一猜测的阶数，参见[原文](https://arxiv.org/abs/2402.12493v4)。

证明分为三个环节：

- **插值证书与二次规划。** 利用光滑凸插值条件，将性能上界归结为一个约束二次规划，并从其 KKT 条件构造非负有向流及相应的插值证书。
- **能量估计。** 通过尾和变换得到三对角能量表达式，再与显式倒数模型作整体比较。主导项归结为两个调和和，从而得到临界尺度中的 $\sqrt{\log N}$ 因子。
- **二维反例。** 从负的试探方向构造有限插值数据，再通过凸共轭得到全局光滑凸函数，实现渐近上界所需的严格反例。

论文采用了形式化过程中得到的整体能量比较证明，具体推导见附录 B。

## 证明与核验

[论文](main.pdf) 给出完整数学论证。[Lean 主定理](lean_formalization/PaperFramework/Main.lean) 对所有满足条件的 $L,D,h$ 证明上述极限，其定义涵盖所有有限维问题实例。2026 年 10 月 12 日的完整构建与公理审计覆盖 699 条定理（含辅助引理），无 `sorry` 或 `sorryAx`，公理依赖限于 `propext`、`Classical.choice` 和 `Quot.sound`。审计摘要与对应源码哈希见下表。

Python 程序以有理数运算检查选定实例中的证书、KKT 条件、能量恒等式和二维反例，并提供渐近推导相关公式的计算检查。一般性的数学结论由论文和 Lean 证明给出。

| 内容 | 入口 |
|---|---|
| 研究论文 | [main.pdf](main.pdf) |
| Lean 工程与证明对应表 | [工程说明](lean_formalization/README.md) · [证明对应表](lean_formalization/PROOF_MAP.md) |
| 最终公理审计与源码哈希 | [审计摘要](lean_formalization/verification/complete_summary.json) · [源码清单](lean_formalization/verification/complete_source_manifest.json) |
| Python 精确检查 | [运行说明](verification/README.md) |

证明对应表沿用形式化时的原稿节号；当前论文的章节编排已有调整。

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

Lean 使用 `leanprover/lean4:v4.26.0`，mathlib 及传递依赖由 `lake-manifest.json` 固定。安装 elan 与 PowerShell 后，在项目根目录运行：

```powershell
Set-Location lean_formalization
lake exe cache get
lake build
pwsh -File check_complete.ps1
```

如需导出提交包，在项目根目录运行 `python scripts/export_repo.py`。输出为 `dist/critical-extrapolation.zip`，文件哈希清单为 `dist/manifest.json`。提交包包含最新论文 PDF、代码及必要的复现材料；历史版本、LaTeX 源文件、课程材料和本地缓存保留在本地。

## AI 使用说明

AI 工具参与了问题探索、证明思路生成、推导整理、Python 与 Lean 代码编写，以及文本修订。数值检查和形式化过程中发现的问题用于修正论证，形式化也促成了能量估计证明的简化。

## 参考文献

Alan Luner and Benjamin Grimmer, *On Averaging and Extrapolation for Gradient Descent*.
[arXiv:2402.12493v4](https://arxiv.org/abs/2402.12493v4) · [DOI:10.1287/moor.2024.0449](https://doi.org/10.1287/moor.2024.0449).
