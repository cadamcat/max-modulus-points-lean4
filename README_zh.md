[English](README.md) | [简体中文](README_zh.md)

# 整函数的最大模点

这是一个关于非单项式整函数的两个最大模点计数问题的 Lean 4 形式化证明。

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [AUTHORS.md](AUTHORS.md).
- **Mathematics:** (a) L. Pardo-Simón 与 D. J. Sixsmith，[*A finite-order answer to a problem of Erdős on maximum modulus points*](https://arxiv.org/abs/2607.09462)，定理 1.1；本形式化证明了构造所用 tract（区域）的 Rempe-Gillen 逼近步骤（[arXiv:1106.3439](https://arxiv.org/abs/1106.3439)）。(b) Y. Li，[*A cofinal bound for maximum-modulus points of entire functions*](https://github.com/liyunpeng1991/liyunpeng1991.github.io/blob/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/papers/maximum-modulus-points-v2.pdf)，预印本。
- 本项目在 AI 协助下开发；所有证明均由 Lean 4 内核验证。

## 命题

对于整函数 `f : ℂ → ℂ` 和半径 `r`，`ν f r` 表示圆周 `|z| = r` 上使 `|f z|` 取得该圆周最大值的点的个数。定理 `MaxModulusPoints.Blueprint.main : MaxModulusPoints.Statement` 形式化了 Hayman–Lingham《函数论研究问题》第 2.16 题中的两个问题，也称 Erdős 第 1117 题：

1. 存在一个非单项式整函数 `f`，使得对任意 `N` 和 `R`，都存在 `r > R` 满足 `ν f r ≥ N`。因此，当半径趋于无穷时，最大模点个数无界。
2. 对每个非单项式整函数 `f`，都存在有限的 `B`，使得对任意 `R`，都存在 `r > R` 满足 `ν f r ≤ B`。因此，最大模点个数不会随半径趋于无穷而趋于无穷。

Lean 中的定义和量词见 [MaxModulusPoints/Challenge.lean](MaxModulusPoints/Challenge.lean)；主定理由 [MaxModulusPoints/Blueprint/Main.lean](MaxModulusPoints/Blueprint/Main.lean) 汇总。

## 构建

需要 Git 和 [elan](https://github.com/leanprover/elan)。在仓库根目录运行：

```sh
lake exe cache get
lake build MaxModulusPoints
```

主定理文件会打印汇总定理所使用的公理。

## 数学来源

- W. K. Hayman 和 E. F. Lingham，*Research Problems in Function Theory*，第 2.16 题，第 29 页（[arXiv:1809.07200](https://arxiv.org/abs/1809.07200)）；这两个问题归于 Erdős，编号为第 1117 题。
- L. Pardo-Simón 和 D. J. Sixsmith，[*A finite-order answer to a problem of Erdős on maximum modulus points*](https://arxiv.org/abs/2607.09462)：正向构造及其共形模型。
- L. Rempe-Gillen，[*Hyperbolic entire functions with full hyperbolic dimension and approximation by Eremenko-Lyubich functions*](https://arxiv.org/abs/1106.3439)：本形式化证明了构造中所用 tract（区域）的逼近步骤。
- Y. Li，[*A cofinal bound for maximum-modulus points of entire functions*](https://github.com/liyunpeng1991/liyunpeng1991.github.io/blob/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/papers/maximum-modulus-points-v2.pdf)，预印本，2026 年 10 月 11 日：沿共终半径集合得到有限上界。

## 第三方代码

导入的库源码及其许可证列于 [THIRD_PARTY.md](THIRD_PARTY.md)。
