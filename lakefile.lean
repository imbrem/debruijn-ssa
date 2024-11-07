import Lake
open Lake DSL

package «DeBruijnSSA» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "9248301da2c228348b194c74be94b0e0b0bbbb2c"

require discretion from git
  "https://github.com/imbrem/discretion.git"
    @ "bdab441c6e43d326b72b8d1ddc8c61b96054bdf3"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib «DeBruijnSSA» where
  -- add any library configuration options here
