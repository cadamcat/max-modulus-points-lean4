# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author and maintainer of this formalization project.

The positive part follows L. Pardo-Simón and D. J. Sixsmith, [*A finite-order answer to a problem of Erdős on maximum modulus points*](https://arxiv.org/abs/2607.09462), Theorem 1.1, together with L. Rempe-Gillen, [*Hyperbolic entire functions with full hyperbolic dimension and approximation by Eremenko-Lyubich functions*](https://arxiv.org/abs/1106.3439); this formalization proves the approximation step for the tracts used in the construction. The negative part follows Y. Li, [*A cofinal bound for maximum-modulus points of entire functions*](https://github.com/liyunpeng1991/liyunpeng1991.github.io/blob/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/papers/maximum-modulus-points-v2.pdf), whose argument gives a finite bound along a cofinal set of radii. This repository formalizes these arguments and does not claim a new mathematical solution. The positive proof builds the chamber-and-gate tract, its normalized conformal models and their approximation by entire functions, then equalizes the slice maxima by a shooting argument to obtain unbounded maximum-point counts. The negative proof bounds the exact maximum points at radii chosen outside a countable exceptional set by a uniform bound on the corresponding fibers.

The author planned, directed and reviewed the work, using AI coding assistants; all proofs and their dependencies are checked by the Lean kernel.

The project uses Mathlib and the vendored libraries listed in [THIRD_PARTY.md](THIRD_PARTY.md).
