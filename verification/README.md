# 精确检查

在项目根目录运行：

```shell
python scripts/verify.py
```

仅依赖 Python 3 标准库。该入口在构建目录运行精确检查，保留已收录的结果快照。

- `exact/`：有理数证书、KKT、平方和、能量恒等式和二维反例检查，以及最终结果快照。
- `independent/`：独立渐近证明检查与修正公式回归检查。
- `independent/inputs/verified.json`：独立检查使用的固定输入。
- `results/`：重新运行独立检查生成的本地输出，由 Git 忽略。

三组检查的日志和退出状态写入 `build/verification/`。Lean 的一般性证明及最终公理审计见 [Lean 工程](../lean_formalization/README.md)。
