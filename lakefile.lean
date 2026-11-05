import Lake
open Lake DSL

package MaxModulusPoints where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

lean_lib OAI
lean_lib TauCeti
lean_lib FixedPointTheorems

@[default_target]
lean_lib MaxModulusPoints
