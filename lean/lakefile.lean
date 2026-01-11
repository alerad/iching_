import Lake
open Lake DSL

package IChing where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

@[default_target]
lean_lib IChing where
  globs := #[.submodules `IChing]
