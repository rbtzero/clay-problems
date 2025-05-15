import Lake
open Lake DSL

package clay_problems where
  -- pass optimisation flags only if desired
  moreLeanArgs := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.19.0"

-- Lean library for the Riemann Hypothesis explicit-formula proof
lean_lib ClayRH where
  srcDir := "problems/RH/rh_lean"
  globs := #[`Ledger]

-- Minimal libraries for other stub files so Lake compiles them too
lean_lib ClayNS where
  srcDir := "problems/NS/ns_lean"
  globs := #[`Energy]

lean_lib ClayYM where
  srcDir := "problems/YM/ym_lean"
  globs := #[`AxialPositivity] 