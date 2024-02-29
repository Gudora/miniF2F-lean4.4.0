import Lake
open Lake DSL

package «miniF2F-lean4» {
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-L./.lake/packages/LeanCopilot/.lake/build",
    "-lctranslate2"
  ]
}

@[default_target]
lean_lib «MiniF2F» {
  -- add library configuration options here
}

-- require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "feec58a7ee9185f92abddcf7631643b53181a7d3"
-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot" @ "v1.1.1"
-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot" @ "8c7b338cb2fbbc8e7eece9db0731bcbb9ce0c2c6"
