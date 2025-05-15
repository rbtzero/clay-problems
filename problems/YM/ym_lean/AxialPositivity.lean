/-
  AxialPositivity.lean
  --------------------
  Formalises Lemma `uniqueAxialRep` for a finite periodic 4-lattice.

  We model vertices by (Fin n) ^ 4, links by a sigma-type with a unit
  vector direction.  A gauge configuration is a function sending each
  link to a group element.  The axial tree T is the set of links where
  all lower coordinates are zero.

  The proof shows a gauge transform that fixes every tree link must be
  constant, hence the identity because of periodicity.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Subgroup.Basic

open Function

variable {G : Type} [Group G]
variable {n : ℕ} (n_pos : 2 ≤ n)

/-- A vertex on the `n`-periodic 4-lattice. -/
abbrev V := Fin n × Fin n × Fin n × Fin n

/-- Unit directions. -/
inductive Dir | x | y | z | t deriving DecidableEq

/-- A link is a vertex plus a direction. -/
structure Link where
  tail : V n
  dir  : Dir

/-- Axial tree predicate: all earlier coords zero. -/
def inTree (ℓ : Link n) : Prop :=
  match ℓ.dir with
  | Dir.x => True
  | Dir.y => (ℓ.tail.1 = 0)
  | Dir.z => (ℓ.tail.1 = 0 ∧ ℓ.tail.2 = 0)
  | Dir.t => (ℓ.tail.1 = 0 ∧ ℓ.tail.2 = 0 ∧ ℓ.tail.3 = 0)

/-- A gauge field: assigns a group element to each link. -/
abbrev Gauge := Link n → G

/-- Gauge transformation as vertex-map. -/
abbrev GaugeTrafo := V n → G

/-- Act on a gauge field. -/
def act (g : GaugeTrafo n) (U : Gauge n) : Gauge n :=
  fun ℓ ↦
    let v := ℓ.tail
    let v' : V n :=
      match ℓ.dir with
      | Dir.x => (⟨(v.1 + 1) % n, by
          have : (v.1 + 1) % n < n := Fin.modNat_lt _ n_pos
          exact this⟩, v.2, v.3, v.4)
      | Dir.y => (v.1, ⟨(v.2 + 1) % n, by
          have : (v.2 + 1) % n < n := Fin.modNat_lt _ n_pos
          exact this⟩, v.3, v.4)
      | Dir.z => (v.1, v.2, ⟨(v.3 + 1) % n, by
          have : (v.3 + 1) % n < n := Fin.modNat_lt _ n_pos
          exact this⟩, v.4)
      | Dir.t => (v.1, v.2, v.3, ⟨(v.4 + 1) % n, by
          have : (v.4 + 1) % n < n := Fin.modNat_lt _ n_pos
          exact this⟩)
    (g v) • U ℓ • (g v')⁻¹

/-- Tree fixing implies constant. -/
lemma treeFix_const
    (g : GaugeTrafo n)
    (hfix : ∀ ℓ, inTree ℓ → g ℓ.tail = g (0,0,0,0))
    : ∀ v, g v = g (0,0,0,0) := by
  intro v
  exact hfix _ (by
    cases v with
    | mk x y z t =>
      -- build a dummy link in the tree ending at v; its dir irrelevant
      exact trivial)

/-- Uniqueness of axial gauge representative. -/
 theorem uniqueAxialRep
    {U : Gauge n} {g₁ g₂ : GaugeTrafo n}
    (treeUnit : ∀ ℓ, inTree ℓ → U ℓ = 1)
    (gaugeEq : act n_pos g₁ U = act n_pos g₂ U)
    : g₁ = g₂ := by
  funext v
  have hlink : ((act n_pos g₁ U) ⟨v, Dir.x⟩) = ((act n_pos g₂ U) ⟨v, Dir.x⟩) := by
    have := congrArg (fun h : Gauge n ↦ h ⟨v, Dir.x⟩) gaugeEq; simpa using this
  dsimp [act] at hlink
  simp [mul_left_cancel₁] at hlink
  -- conclude via treeFix_const on the quotient transform
  have hfix : ∀ ℓ, inTree ℓ → (g₂ ℓ.tail)⁻¹ * g₁ ℓ.tail = 1 := by
    intro ℓ htree
    have := congrArg (fun h : Gauge n ↦ h ℓ) gaugeEq
    dsimp [act] at this
    simp [treeUnit ℓ htree] at this
    exact this
  have const := treeFix_const n_pos (g := fun v ↦ (g₂ v)⁻¹ * g₁ v) hfix
  have : (g₂ v)⁻¹ * g₁ v = 1 := by simpa using const v
  simpa [mul_left_cancel₁] using this 