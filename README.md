# BCMP 4.30：Lean 4.36.0 证明候选

本候选固定 **Lean 4.36.0 + mathlib v4.36.0**。定理适用于每个整数 `s ≥ 2`，结论是除顶端点外的每个未调参数都被无穷多个不同的非中性最大匹配区间积聚。以下命令重建此处的源码，而不沿用 4.19 的项目对象。

## 独立验证副本

此项目根目录包含 45 个 BCMP Lean 源、package 配置、toolchain pin 与完整 Lake lockfile。它把 mathlib tag `v4.36.0` 锁为 commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`，连同八个传递依赖的完整 commit SHA。

Clean rebuild uses the matching elan-managed Lake, which materializes the exact locked dependencies under `.lake/packages`:

```sh
lake build checkLakePins
lake exe checkLakePins
lake exe cache get Mathlib.Analysis.SpecificLimits.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
```

`checkLakePins` verifies all nine materialized package HEADs against the lockfile. The cache command must also run from this project root so its requests use the locked versions; a successful import smoke is a dependency check, not the theorem check. On this Windows host, system curl 8.13 fails TLS revocation checks for `cache.mathlib.org`. Never disable revocation or certificate validation. A maintainer can instead use a network environment with working revocation checking or fetch the locked cache artifacts with a standard TLS-verified client, verify each cache artifact, then unpack them with the bundled version-matched leantar.

## Full clean rebuild

Use Python 3.11+ and pass the actual Lean binary (not an elan shim); the verifier uses Lake from the same `bin` directory. With elan, run from the project root:

```sh
python verify.py --lean "$(elan which lean)" --preflight-only --out ../bcmp-preflight
python verify.py --lean "$(elan which lean)" --out ../bcmp-full
```

The two output directories must not exist yet. On Windows with a standalone toolchain use `py -3 -X utf8 verify.py --lean "<toolchain>\bin\lean.exe" --out "<new-directory>"`. The preflight compiles an import probe but checks no BCMP theorem. The full run checks source and consumer hashes, compares all package revisions to the project and upstream locks, rejects dirty Git worktrees and runs the Lake pin checker before compiling the project. Use a trusted Lean distribution and matching trusted dependency caches: a Git HEAD check does not authenticate ignored, prebuilt `.olean` files. No prebuilt BCMP module is used.



## 命题与资料

Lean 总定理：[`BCMP430.Final430.bcmp_conjecture_4_30`](formal/Final430.lean)。中文[证明稿](docs/proof-zh.md)及[展开消费者](checks/VerifyStatement.lean)。它对应 BCMP 作者稿 Conjecture 4.30（[作者稿](https://www.mat.univie.ac.at/~bruin/papers/bcmp.pdf)，[2017 预印本](https://arxiv.org/abs/1707.07488)）。

4.36 源码 manifest SHA-256：`770dbf88b28b8b8b7326d7aec4db6a8f57ab19689de4819b9a2cb2dc8680858c`。45 个模块中有 26 个为适配新版 Lean/mathlib 作了修改；`Final430.lean` 和展开消费者的字节均未变。公开源码材料不包含 `.lake`、本地验证日志、原论文 PDF 或工具链。
