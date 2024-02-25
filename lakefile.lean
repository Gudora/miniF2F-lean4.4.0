import Lake
open Lake DSL

package «miniF2F-lean4» {
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
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
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot" @ "031f024e2a6440b789d0c74c6074a6263a456546"
