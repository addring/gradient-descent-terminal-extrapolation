# c_crit 的形式化依赖链

`originalCriticalCoefficient` 定义论文中的 c_crit。令 t=1/h、a=N(c−1)，固定 h∈(0,1]。

```text
TrialProfiles + ShiftedEnergy
  → OriginalFeasibility：N≥4t 时，所有 a≥0 的严格可行性

TrialWeightedSum + TrialAsymptotics + TrialNormalization
  → OriginalEnergy：固定 [0,A] 上的一致能量上界
  → OriginalObjective：目标恒等式、末端修正界、紧区间负目标

严格可行性 + 负目标 + GlobalRealization
  → a∈[(1+ε)t/√log N,2t] 上的平面反例

QuadraticActual + 几何衰减 + WorstScaling
  → OriginalQuadratic：所有 a≥2t 的二次函数反例

两段反例
  → original_eventual_upper_failure_fixed_step
    ∀ᶠ N, ∀ c≥1+(1+ε)/(hN√log N), P(c)>LD/(1+Nhc)

全右侧失效 + 下侧精确性
  → original_critical_sandwich
  → original_sharp_critical_scale
  → original_critical_increment_small
  → original_no_positive_inverse_linear_lower_bound
  → original_conjecture_5_1_false（h=L=D=1）
```

| 模块 | 定理数 | 内容 |
|---|---:|---|
| `OriginalFeasibility` | 4 | 倒数项余量、参数系数、斜率泛函、严格可行性 |
| `OriginalEnergy` | 2 | 能量扰动上界、一致渐近上界 |
| `OriginalObjective` | 4 | 目标恒等式、末端界、标量估计、统一负目标 |
| `OriginalQuadratic` | 2 | 几何衰减、尾部严格失效 |
| `OriginalCritical` | 6 | 拼接、上确界、极限及猜想否定 |

## 复现与记录

在 Lean 工程目录执行 `lake build` 和 `lake env lean OriginalAudit.lean`。18 条定理的独立审计与完整工程构建见 [核验索引](verification/original_extension/README.md)。

`scripts/check_original_framework.py --combined` 为独立合并编译入口；`--interfaces-only` 仅检查声明类型。常规复现使用上述 Lake 命令即可。
