[English](README.md) | [简体中文](README_zh.md)

# Maximum modulus points for entire functions

A Lean 4 formalization of the two maximum-modulus counting questions for non-monomial entire functions.

- Developed with AI assistance; all proofs are verified by the Lean 4 kernel.

## Statement

For an entire function `f : ℂ → ℂ` and a radius `r`, `ν f r` is the cardinality of the points on `|z| = r` where `|f z|` reaches its maximum on that circle. The theorem `MaxModulusPoints.Blueprint.main : MaxModulusPoints.Statement` formalizes both questions of Hayman–Lingham Problem 2.16, also known as Erdős Problem #1117:

1. There is a non-monomial entire function `f` such that for every `N` and `R`, some `r > R` has `ν f r ≥ N`. Thus the maximum-point counts are unbounded along radii tending to infinity.
2. For every non-monomial entire function `f`, there is a finite `B` such that for every `R`, some `r > R` has `ν f r ≤ B`. Thus the counts do not tend to infinity as the radius tends to infinity.

The Lean definitions and quantifiers are in [MaxModulusPoints/Challenge.lean](MaxModulusPoints/Challenge.lean); the theorem is assembled in [MaxModulusPoints/Blueprint/Main.lean](MaxModulusPoints/Blueprint/Main.lean).

## Build

Requirements: Git and [elan](https://github.com/leanprover/elan). From the repository root:

```sh
lake exe cache get
lake build MaxModulusPoints
```

The main theorem file prints the axioms used by the assembled theorem.

## Mathematical sources

- W. K. Hayman and E. F. Lingham, *Research Problems in Function Theory*, Problem 2.16, p. 29 ([arXiv:1809.07200](https://arxiv.org/abs/1809.07200)); the two questions are attributed to Erdős, Problem #1117.
- L. Pardo-Simón and D. J. Sixsmith, [*A finite-order answer to a problem of Erdős on maximum modulus points*](https://arxiv.org/abs/2607.09462): the positive construction and its conformal model.
- L. Rempe-Gillen, [*Hyperbolic entire functions with full hyperbolic dimension and approximation by Eremenko-Lyubich functions*](https://arxiv.org/abs/1106.3439): the formalization proves the approximation step for the tracts used in the construction.
- Y. Li, [*A cofinal bound for maximum-modulus points of entire functions*](https://github.com/liyunpeng1991/liyunpeng1991.github.io/blob/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/papers/maximum-modulus-points-v2.pdf), preprint, 11 October 2026: the finite bound along a cofinal set of radii.

## Third-party code

Imported library sources and their licenses are listed in [THIRD_PARTY.md](THIRD_PARTY.md).
