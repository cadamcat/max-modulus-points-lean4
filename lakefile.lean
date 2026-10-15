import Lake
open Lake DSL

package MaxModulusPoints where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI
lean_lib TauCeti
lean_lib FixedPointTheorems

@[default_target]
lean_lib MaxModulusPoints
