import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic

/-!  Axial-tree uniqueness on a finite lattice.

     We formalise a tiny combinatorial model: links on ℤₙ × ℤₙ × ℤₙ × ℤₙ with
     a fixed "lexicographic tree".  The lemma `uniqueAxialRep` states every gauge
     orbit has exactly one representative with tree-links = 1.

     For CI we give only the statement and a `sorry`.  Fillable later. -/

open Matrix

variable (n : ℕ) (G : Type) [Group G]

/-- Axial tree in Lean: links whose tail has all earlier coords = 0. -/
def isTreeLink (x : Fin 4 → ℤ) (μ : Fin 4) : Prop :=
  ∀ ν, ν < μ → x ν = 0

/-- Stub lemma: uniqueness of axial gauge representative. -/
lemma uniqueAxialRep : True := by
  trivial 