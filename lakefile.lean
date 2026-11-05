import Lake
open Lake DSL

package MaxModulusPoints where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

-- No root module: the vendored libraries are directories of import-closure files.
lean_lib OAI where
  globs := #[.submodules `OAI]

lean_lib TauCeti where
  globs := #[.submodules `TauCeti]

lean_lib FixedPointTheorems where
  globs := #[.submodules `FixedPointTheorems]

@[default_target]
lean_lib MaxModulusPoints
