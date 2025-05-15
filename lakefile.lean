import Lake
open Lake DSL

package clay_problems where
  -- Additional compiler options can go here

-- Pull in mathlib4 exactly matching Lean 4.19.0
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.19.0"

-- Riemann–Hypothesis proof library
lean_lib ClayRH where
  srcDir := "problems/RH/rh_lean"
  globs := #[`Ledger]

-- Navier–Stokes stub
lean_lib ClayNS where
  srcDir := "problems/NS/ns_lean"
  globs := #[`Energy]

-- Yang–Mills stub
lean_lib ClayYM where
  srcDir := "problems/YM/ym_lean"
  globs := #[`AxialPositivity] 