# Five OEIS recurrence proofs in Lean

本仓库公开五题的 Lean 证明源码、数学证明正文及可复现的构建和公理检查入口。Lean / Mathlib 固定于 `v4.34.0-rc2`，依赖版本见 `lake-manifest.json`。

| 题号与证明正文 | 最终 Lean 定理 | 已完成范围 |
|---|---|---|
| [A006343](OEISOpen/A006343/Proof.md) | `OEISOpen.A006343.recurrence_of_algebraic` | 从指定代数生成函数及两个初值推出六项递推，n≥5；原 Arkons 组合计数到生成函数的桥梁尚未形式化。 |
| [A089073](OEISOpen/A089073/Proof.md) | `OEISOpen.A089073.a089073_recurrence` | 闭式数列的指定递推，n≥5；原反射图计数桥梁有非形式化证明，尚未完整形式化。 |
| [A150500](OEISOpen/A150500/Proof.md) | `OEISOpen.A150500.a150500_recurrence` | 从原三维受限路径计数到四阶递推的完整形式化，n≥4。 |
| [A219692](OEISOpen/A219692/Proof.md) | `OEISOpen.A219692.original_tail_recurrence` | 从原有限和到递推的完整形式化，原序列 n≥3；归一化序列 n≥2。原序列 n=2 的残差为180。 |
| [A371753](OEISOpen/A371753/Proof.md) | `OEISOpen.A371753.recurrence` | 从原二项式有限和到三阶递推的完整形式化，n≥3。 |

数学证明正文保留原推导；精确的形式化范围以最终 Lean 定理的类型和定义为准。A089073 的图桥梁全文见 [GraphBridge.md](OEISOpen/A089073/GraphBridge.md) 和 [ParityBijection.md](OEISOpen/A089073/ParityBijection.md)。

## 构建与公理核验

安装 `lean-toolchain` 指定的 Lean 工具链后，在仓库根目录执行：

```sh
lake exe cache get
lake build
python scripts/check_proofs.py
```

默认 `lake build` 覆盖全部五题。检查脚本逐题运行 Lean 公理审计，只允许 `propext`、`Classical.choice` 和 `Quot.sound`，并要求五个最终定理均有实际审计输出。GitHub CI 使用同一检查入口。脚本只需要 Python 标准库。

2026-10-04 上传前，本地五题编译与五个最终定理的公理核验均通过。56个Lean源文件保留了原始字节；构建缓存没有提交。

## 文献与成果范围

A219692 的主数学结论已有 [Cooper 2012](https://link.springer.com/article/10.1007/s11139-011-9357-3) 的证明，本地成果属于独立重证与形式化；A150500 的模型也与已有文献结果相连。这五题均不主张首次性，也不宣称完成某个官方基准的五个目标。

本仓库只包含公开证明和构建材料；完整本地研究包的文献缓存、历史实验、审查日志和机器环境记录未上传。
