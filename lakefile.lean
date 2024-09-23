import Lake
open Lake DSL

package "leanwuzla" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Leanwuzla» where
  -- add library configuration options here
