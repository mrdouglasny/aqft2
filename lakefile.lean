import Lake
open Lake DSL

package «aqft2» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Aqft2» where
  -- add any library configuration options here

lean_lib «KolmogorovExtension4» where
  -- Kolmogorov extension theorem library
  roots := #[`KolmogorovExtension4]
