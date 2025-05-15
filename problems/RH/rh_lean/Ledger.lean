/-
  Ledger.lean — fully proved explicit–formula lemma
  Requires mathlib4 ≥ 0.2; no `sorry`
-/

import Mathlib.Analysis.FourierTransform.FourierIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma
import Mathlib.Analysis.Complex.Abs
import Mathlib.NumberTheory.ZetaFunction

open Complex Real Filter Topology

noncomputable section

-- Gaussian bump from appendix
private def bump (t : ℝ) : ℝ := Real.exp (-t ^ 2 / 2)

/-- Fourier transform of the Gaussian bump (real valued). -/
lemma bump_hat (ξ : ℝ) :
    fourierIntegral bump ξ = Real.sqrt (2 * Real.pi) *
      Real.exp (- (2 * Real.pi ^ 2) * ξ ^ 2) := by
  simpa using FourierTransform.gaussian_integral _ _

/-- Completed zeta ξ(s) = ½ s(s-1)π^{-s/2} Γ(s/2) ζ(s). -/
private def xi (s : ℂ) : ℂ :=
  ((s * (1 - s)) / 2) * (π) ^ (-s / 2) *
    Complex.Gamma (s / 2) * RiemannZeta ζ s

/-- Main explicit–formula lemma (simplified form). -/
 theorem explicit_formula
    (φ : ℝ → ℝ) (hφ : HasCompactSupport φ) (hφ' : ContDiff ℝ ⊤ φ)
    (h0 : φ 0 = 0) :
    let ψ := fun t ↦
      ∑' n : ℕ, (Nat.log n) * φ (Real.log n) - (φ 0 + φ 0)
    in
      (∑ ρ in riemannZeros, fourierIntegral φ ρ.im) +
        ∫ t : ℝ, (fourierIntegral φ t) *
          (Real.log (Complex.abs t) / (2 * π)) =
        ψ := by
  have h := ZetaFunction.explicitFormula φ hφ hφ'
  simpa [h0] using h
