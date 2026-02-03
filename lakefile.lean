import Lake

open Lake DSL

package NLEqualsCoNL where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

@[default_target]
lean_lib NLEqualsCoNL where
  globs := #[.one `NLEqualsCoNL]
