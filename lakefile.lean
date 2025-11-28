import Lake
open Lake DSL

package Lewis

require mathlib from git
  "file:///Users/huubvromen/nextcloud/Leanprojects/SharedMathlib/mathlib4"

@[default_target]
lean_lib Lewis
