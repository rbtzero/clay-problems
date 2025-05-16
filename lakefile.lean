import Lake
open Lake DSL

package clay_problems where
  -- Additional compiler options can go here

-- Pull in mathlib4 snapshot matching Lean 4.5.0
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.5.0"

-- Riemann–Hypothesis proof library
lean_lib ClayRH where
  srcDir := "problems/RH/rh_lean"
  globs := #[`Ledger, `SignKernel]

-- Navier–Stokes stub
lean_lib ClayNS where
  srcDir := "problems/NS/ns_lean"
  -- Include all Navier–Stokes skeleton modules
  globs := #[`Full]

-- Yang–Mills stub
lean_lib ClayYM where
  srcDir := "problems/YM/ym_lean"
  globs := #[`AxialPositivity] 